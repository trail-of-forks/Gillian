open Gil_syntax
open Llvm_memory_model
open Monomorphizer.Template

module Types = struct
  type label = string
  type cmd = label Gil_syntax.Cmd.t
  type labeled_cmd = label option * cmd
  type block = labeled_cmd list
  type state = { curr_block : block; blocks : block list }
  type 'a t = state -> 'a * state
end

module type S = sig
  include module type of Types

  val add_cmd : cmd -> unit t
  val set_state : state -> unit t
  val get_state : state t
  val if_ : Gil_syntax.Expr.t -> true_case:'a t -> 'a t

  val ite :
    Gil_syntax.Expr.t -> true_case:'a t -> false_case:'b t -> ('a * 'b) t

  val switch :
    cases:(unit t * Gil_syntax.Expr.t) list -> default:unit t -> unit t

  val compile : state -> 'a t -> 'a * labeled_cmd list
  val empty_state : unit -> state
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val return : 'a -> 'a t
  val fresh_sym : unit -> string
  val empty_block : unit -> block
  val new_block : label -> unit t
  val get_current_block_label : label t
end

module Codegenerator : S with type label = string = struct
  type label = string
  type cmd = label Gil_syntax.Cmd.t
  type labeled_cmd = label option * cmd
  type block = labeled_cmd list
  type state = { curr_block : block; blocks : block list }
  type 'a t = state -> 'a * state

  let set_state s state = ((), s)
  let get_state state = (state, state)
  let ctr = ref 0

  let fresh_sym () =
    let sym = Printf.sprintf "ctr_%d" !ctr in
    ctr := !ctr + 1;
    sym

  let empty_block () = [ (Some (fresh_sym ()), Gil_syntax.Cmd.Skip) ]
  let return x state = (x, state)

  let bind t f state =
    let tval, tstate = t state in
    let fval, fstate = f tval tstate in
    (fval, fstate)

  let ( let* ) = bind
  let empty_state () = { curr_block = empty_block (); blocks = [] }
  let lst_last lst = List.hd (List.rev lst)

  let get_current_block_label =
    let* st = get_state in
    let label = st.curr_block |> lst_last |> fst |> Option.get in
    return label

  let add_cmd c =
    let* cstate = get_state in
    let curr_block = (None, c) :: cstate.curr_block in
    let blocks = cstate.blocks in
    set_state { curr_block; blocks }

  let new_block label =
    let* cstate = get_state in
    let curr_block = (Some label, Gil_syntax.Cmd.Skip) :: cstate.curr_block in
    let blocks = cstate.blocks in
    set_state { curr_block; blocks }

  let if_ expr ~true_case =
    let tlable = fresh_sym () in
    let flabel = fresh_sym () in
    let* _ = add_cmd (Gil_syntax.Cmd.GuardedGoto (expr, tlable, flabel)) in
    let* _ = new_block tlable in
    let* tval = true_case in
    let* _ = new_block flabel in
    return tval

  let ite expr ~true_case ~false_case =
    let tlable = fresh_sym () in
    let flabel = fresh_sym () in
    let* _ = add_cmd (Gil_syntax.Cmd.GuardedGoto (expr, tlable, flabel)) in
    let* _ = new_block tlable in
    let* tval = true_case in
    let* _ = new_block flabel in
    let* fval = false_case in
    return (tval, fval)

  let rec switch
      ~(cases : (unit t * Gil_syntax.Expr.t) list)
      ~(default : unit t) : unit t =
    match cases with
    | [] -> default
    | (case, expr) :: cases ->
        let* _ =
          ite expr ~true_case:case ~false_case:(switch ~cases ~default)
        in
        return ()

  let compile state t =
    let tval, tstate = t state in
    ( tval,
      tstate.curr_block :: tstate.blocks |> List.map List.rev |> List.flatten )
end

let is_type_of_expr
    (expr : Gil_syntax.Expr.t)
    (type_ : Llvm_memory_model.LLVMRuntimeTypes.t) =
  let open Gil_syntax.Expr.Infix in
  Gil_syntax.Expr.type_eq expr Gil_syntax.Type.ListType
  && Gil_syntax.Expr.list_length expr == Gil_syntax.Expr.int 2
  && Gil_syntax.Expr.list_nth expr 0
     == Gil_syntax.Expr.string
          (Llvm_memory_model.LLVMRuntimeTypes.type_to_string type_)

let rec foldM (f : 'b -> 'a -> 'b Codegenerator.t) (acc : 'b) (lst : 'a list) :
    'b Codegenerator.t =
  let open Codegenerator in
  match lst with
  | [] -> return acc
  | x :: xs ->
      let* acc = f acc x in
      foldM f acc xs

let add_return_of_value (value : Gil_syntax.Expr.t) =
  let open Codegenerator in
  let* _ =
    add_cmd
      (Gil_syntax.Cmd.Assignment (Gillian.Utils.Names.return_variable, value))
  in
  let* _ = add_cmd Gil_syntax.Cmd.ReturnNormal in
  get_current_block_label

let fail_cmd (err_type : string) (args : Gil_syntax.Expr.t list) =
  Gil_syntax.Cmd.Fail (err_type, args)

let type_fail (expr_and_type : (Gil_syntax.Expr.t * LLVMRuntimeTypes.t) list) =
  let exprs =
    List.map
      (fun (expr, rty) ->
        Expr.list [ expr; LLVMRuntimeTypes.rtype_to_gil_type rty |> Expr.type_ ])
      expr_and_type
  in
  fail_cmd "Type_mismatch" exprs

type bv_op_function = Expr.t list -> bv_op_shape -> Expr.t

type generalized_bv_op_function =
  Expr.t list -> bv_op_shape -> Expr.t Codegenerator.t

let add_overflow_check
    (check_ops : bv_op_function list option)
    (inputs : Expr.t list)
    (shape : bv_op_shape) =
  let open Codegenerator in
  let open Gil_syntax.Expr in
  let open Gil_syntax.Expr.Infix in
  match check_ops with
  | Some ops ->
      let check_expr =
        List.fold_right (fun op acc -> op inputs shape || acc) ops Expr.false_
      in
      let* _ =
        ite check_expr
          ~true_case:
            (let* _ = add_cmd (fail_cmd "Detected_forbidden_overflow" inputs) in
             let* _ = add_cmd Gil_syntax.Cmd.ReturnNormal in
             return ())
          ~false_case:(return ())
      in
      return ()
  | None -> return ()

let generalized_op_bv_scheme
    (inputs : Expr.t list)
    (op : generalized_bv_op_function)
    (check_ops : bv_op_function list option)
    (shape : bv_op_shape) : unit Codegenerator.t =
  let open Codegenerator in
  let open Gil_syntax.Expr in
  let open Gil_syntax.Expr.Infix in
  let expr_with_type =
    List.map2
      (fun expr width -> (expr, Llvm_memory_model.LLVMRuntimeTypes.Int width))
      inputs shape.args
  in
  let check =
    List.map (fun (expr, rty) -> is_type_of_expr expr rty) expr_with_type
    |> fun lst -> List.fold_right (fun x acc -> x && acc) lst Expr.true_
  in
  let* _ =
    ite check
      ~true_case:
        (let extracted_inputs = List.map (fun i -> Expr.list_nth i 1) inputs in
         let* _ = add_overflow_check check_ops extracted_inputs shape in
         let* res = op extracted_inputs shape in
         let* _ =
           add_return_of_value
             (Expr.EList
                [
                  Expr.string
                    (LLVMRuntimeTypes.type_to_string
                       (LLVMRuntimeTypes.Int (Option.get shape.width_of_result)));
                  res;
                ])
         in
         return get_current_block_label)
      ~false_case:
        (let* _ = add_cmd (type_fail expr_with_type) in
         let* _ = add_cmd Gil_syntax.Cmd.ReturnNormal in
         return get_current_block_label)
  in
  return ()

let op_bv_scheme
    (inputs : Expr.t list)
    (op : bv_op_function)
    (check_ops : bv_op_function list option)
    (shape : bv_op_shape) : unit Codegenerator.t =
  let open Codegenerator in
  let generalized_op inputs shape = return (op inputs shape) in
  generalized_op_bv_scheme inputs generalized_op check_ops shape

let op_function
    (name : string)
    (arity : int)
    (f : Gil_syntax.Expr.t list -> unit Codegenerator.t) :
    (Annot.Basic.t, string) Gil_syntax.Proc.t =
  let open Codegenerator in
  let open Gil_syntax.Proc in
  let params = List.init arity (fun _ -> Codegenerator.fresh_sym ()) in
  let body = f (List.map (fun p -> Expr.PVar p) params) in
  let _, cmds = compile (empty_state ()) body in
  let annotated =
    List.map (fun c -> (Annot.Basic.make (), fst c, snd c)) cmds
  in
  let p =
    {
      proc_name = name;
      proc_source_path = None;
      proc_internal = false;
      proc_body = Array.of_list annotated;
      proc_params = params;
      proc_spec = None;
      proc_aliases = [];
      proc_calls = [];
      proc_display_name = None;
      proc_hidden = false;
    }
  in
  p

module TypePatterns = struct
  type t = {
    exprs : Gil_syntax.Expr.t list;
    types_ : LLVMRuntimeTypes.t list;
    case_stat : unit Codegenerator.t;
  }

  let pattern_check
      (exprs : Gil_syntax.Expr.t list)
      (types_ : LLVMRuntimeTypes.t list) : Expr.t =
    let open Codegenerator in
    let open Gil_syntax.Expr in
    let open Gil_syntax.Expr.Infix in
    let check_expr =
      List.map2 (fun expr type_ -> is_type_of_expr expr type_) exprs types_
      |> fun lst -> List.fold_right (fun x acc -> x && acc) lst Expr.true_
    in
    check_expr

  let rec type_dispatch
      (patterns : t list)
      (default_stat : unit Codegenerator.t) : unit Codegenerator.t =
    let open Codegenerator in
    match patterns with
    | [] -> default_stat
    | pattern :: patterns ->
        let check = pattern_check pattern.exprs pattern.types_ in
        let* _ = if_ check ~true_case:pattern.case_stat in
        let* _ = type_dispatch patterns default_stat in
        return ()
end

let update_pointer (ptr_exp : Expr.t) (offset : Expr.t) =
  let _ = Expr.list_nth (Expr.list_nth ptr_exp 1) 1 in
  let pointer_object = Expr.list_nth (Expr.list_nth ptr_exp 1) 0 in
  let pointer_ty =
    LLVMRuntimeTypes.type_to_string LLVMRuntimeTypes.Ptr |> Expr.string
  in
  Expr.EList [ pointer_ty; Expr.EList [ pointer_object; offset ] ]

let pattern_function_unary
    (expr : Expr.t)
    (shape : bv_op_shape)
    (op : bv_op_function) =
  let open Codegenerator in
  let open TypePatterns in
  let input_width =
    match List.nth_opt shape.args 0 with
    | Some width -> width
    | None -> failwith "Unary operations should have at least one argument"
  in
  let case_statement_for_ptr (pval : Expr.t) =
    let pointer_offset = Expr.list_nth (Expr.list_nth pval 1) 1 in
    let* _ =
      add_return_of_value (update_pointer pval (op [ pointer_offset ] shape))
    in
    return ()
  in
  let case_statement_for_int (regular_val : Expr.t) =
    let int_val = Expr.list_nth regular_val 1 in
    let result_type =
      match shape.width_of_result with
      | Some width -> Expr.string ("i-" ^ string_of_int width)
      | None -> failwith "Unary operations should have a result width"
    in
    let* _ =
      add_return_of_value (Expr.EList [ result_type; op [ int_val ] shape ])
    in
    return ()
  in
  let default_statement = add_cmd (fail_cmd "No_type_pattern_matched" []) in
  let patterns =
    [
      {
        exprs = [ expr ];
        types_ = [ LLVMRuntimeTypes.Ptr ];
        case_stat = case_statement_for_ptr expr;
      };
      {
        exprs = [ expr ];
        types_ = [ LLVMRuntimeTypes.Int input_width ];
        case_stat = case_statement_for_int expr;
      };
    ]
  in
  let* _ = type_dispatch patterns default_statement in
  return ()

let pattern_function_ternary
    (expr1 : Expr.t)
    (expr2 : Expr.t)
    (expr3 : Expr.t)
    (shape : bv_op_shape)
    (op : bv_op_function)
    (commutative : bool)
    (flag_checks : bv_op_function list option) =
  let open Codegenerator in
  let open TypePatterns in
  let open Gil_syntax.Expr.Infix in
  let ptr_width =
    match shape.width_of_result with
    | Some width -> width
    | None -> failwith "Pointer operations should have a result"
  in
  let case_statement_for_int
      (regular_val0 : Expr.t)
      (regular_val1 : Expr.t)
      (regular_val2 : Expr.t) =
    let int_valx = Expr.list_nth regular_val0 1 in
    let int_valy = Expr.list_nth regular_val1 1 in
    let int_valz = Expr.list_nth regular_val2 1 in
    let* _ =
      add_overflow_check flag_checks [ int_valx; int_valy; int_valz ] shape
    in
    let* _ =
      add_return_of_value
        (Expr.EList
           [
             Expr.list_nth regular_val0 0;
             op [ int_valx; int_valy; int_valz ] shape;
           ])
    in
    return ()
  in
  let default_statement = add_cmd (fail_cmd "No_type_pattern_matched" []) in
  let patterns =
    [
      {
        exprs = [ expr1; expr2; expr3 ];
        types_ =
          [
            LLVMRuntimeTypes.Int ptr_width;
            LLVMRuntimeTypes.Int ptr_width;
            LLVMRuntimeTypes.Int ptr_width;
          ];
        case_stat = case_statement_for_int expr1 expr2 expr3;
      };
    ]
  in
  let* _ = type_dispatch patterns default_statement in
  return ()

let cmp_patterns
    ~(pointer_width : int)
    (expr1 : Expr.t)
    (expr2 : Expr.t)
    (op : bv_op_function)
    (shape : bv_op_shape) =
  let open Codegenerator in
  let open TypePatterns in
  let open Gil_syntax.Expr.Infix in
  let can_use_pointer = List.for_all (fun x -> x = pointer_width) shape.args in
  let add_return_of_bool_value (bool_val : Expr.t) =
    let type_of_bool =
      LLVMRuntimeTypes.type_to_string (LLVMRuntimeTypes.Int 1) |> Expr.string
    in
    let* _ =
      ite bool_val
        ~true_case:
          (add_return_of_value
             (Expr.EList [ type_of_bool; Expr.int_to_bv ~width:1 1 ]))
        ~false_case:
          (add_return_of_value
             (Expr.EList [ type_of_bool; Expr.int_to_bv ~width:1 0 ]))
    in
    return ()
  in
  let case_statement_for_ptr (pval1 : Expr.t) (pval2 : Expr.t) =
    let pointer_offset1 = Expr.list_nth (Expr.list_nth pval1 1) 1 in
    let pointer_offset2 = Expr.list_nth (Expr.list_nth pval2 1) 1 in
    let abs_obj1 = Expr.list_nth pval1 0 in
    let abs_obj2 = Expr.list_nth pval2 0 in
    let* _ =
      ite (abs_obj1 == abs_obj2)
        ~true_case:
          (let* _ =
             add_return_of_bool_value
               (op [ pointer_offset1; pointer_offset2 ] shape)
           in
           return ())
        ~false_case:
          (let* _ =
             add_cmd (fail_cmd "Incomparable_pointers" [ expr1; expr2 ])
           in
           let* _ = add_cmd Gil_syntax.Cmd.ReturnNormal in
           return ())
    in
    return ()
  in
  let case_statement_for_num (regular_val1 : Expr.t) (regular_val2 : Expr.t) =
    let int_val1 = Expr.list_nth regular_val1 1 in
    let int_val2 = Expr.list_nth regular_val2 1 in
    let* _ = add_return_of_bool_value (op [ int_val1; int_val2 ] shape) in
    return ()
  in
  let ptr_patterns =
    if can_use_pointer then
      [
        {
          exprs = [ expr1; expr2 ];
          types_ = [ LLVMRuntimeTypes.Ptr; LLVMRuntimeTypes.Ptr ];
          case_stat = case_statement_for_ptr expr1 expr2;
        };
      ]
    else []
  in
  let int_patterns =
    [
      {
        exprs = [ expr1; expr2 ];
        types_ =
          [
            LLVMRuntimeTypes.Int (List.hd shape.args);
            LLVMRuntimeTypes.Int (List.nth shape.args 1);
          ];
        case_stat = case_statement_for_num expr1 expr2;
      };
    ]
  in
  let float_patterns =
    [
      {
        exprs = [ expr1; expr2 ];
        types_ = [ LLVMRuntimeTypes.F32; LLVMRuntimeTypes.F32 ];
        case_stat = case_statement_for_num expr1 expr2;
      };
      {
        exprs = [ expr1; expr2 ];
        types_ = [ LLVMRuntimeTypes.F64; LLVMRuntimeTypes.F64 ];
        case_stat = case_statement_for_num expr1 expr2;
      };
      {
        exprs = [ expr1; expr2 ];
        types_ = [ LLVMRuntimeTypes.F32; LLVMRuntimeTypes.F64 ];
        case_stat = case_statement_for_num expr1 expr2;
      };
      {
        exprs = [ expr1; expr2 ];
        types_ = [ LLVMRuntimeTypes.F64; LLVMRuntimeTypes.F32 ];
        case_stat = case_statement_for_num expr1 expr2;
      };
    ]
  in
  let patterns = int_patterns @ ptr_patterns @ float_patterns in
  let default_statement = add_cmd (fail_cmd "No_type_pattern_matched" []) in
  let* _ = type_dispatch patterns default_statement in
  return ()

let fp_patterns
    ~(pointer_width : int)
    (expr1 : Expr.t)
    (expr2 : Expr.t)
    (op : bv_op_function)
    (shape : bv_op_shape)
    (flag_checks : bv_op_function list option) =
  let open Codegenerator in
  let open TypePatterns in
  let open Gil_syntax.Expr.Infix in
  let case_statement_for_float (regular_val0 : Expr.t) (regular_val1 : Expr.t) =
    let float_valx = Expr.list_nth regular_val0 1 in
    let float_valy = Expr.list_nth regular_val1 1 in
    let* _ =
      add_return_of_value
        (Expr.EList
           [ Expr.list_nth regular_val0 0; op [ float_valx; float_valy ] shape ])
    in
    return ()
  in
  let patterns =
    [
      {
        exprs = [ expr1; expr2 ];
        types_ = [ LLVMRuntimeTypes.F32; LLVMRuntimeTypes.F32 ];
        case_stat = case_statement_for_float expr1 expr2;
      };
      {
        exprs = [ expr1; expr2 ];
        types_ = [ LLVMRuntimeTypes.F64; LLVMRuntimeTypes.F64 ];
        case_stat = case_statement_for_float expr1 expr2;
      };
    ]
  in
  let default_statement = add_cmd (fail_cmd "No_type_pattern_matched" []) in
  let* _ = type_dispatch patterns default_statement in
  return ()

let fp_patterns_unary
    ~(pointer_width : int)
    (expr : Expr.t)
    (op : bv_op_function)
    (shape : bv_op_shape)
    (flag_checks : bv_op_function list option) =
  let open Codegenerator in
  let open TypePatterns in
  let open Gil_syntax.Expr.Infix in
  let case_statement_for_float (regular_val : Expr.t) =
    let float_val = Expr.list_nth regular_val 1 in
    let* _ =
      add_return_of_value
        (Expr.EList [ Expr.list_nth regular_val 0; op [ float_val ] shape ])
    in
    return ()
  in
  let patterns =
    [
      {
        exprs = [ expr ];
        types_ = [ LLVMRuntimeTypes.F32 ];
        case_stat = case_statement_for_float expr;
      };
      {
        exprs = [ expr ];
        types_ = [ LLVMRuntimeTypes.F64 ];
        case_stat = case_statement_for_float expr;
      };
    ]
  in
  let default_statement = add_cmd (fail_cmd "No_type_pattern_matched" []) in
  let* _ = type_dispatch patterns default_statement in
  return ()

let fp_patterns_ternary
    ~(pointer_width : int)
    (expr1 : Expr.t)
    (expr2 : Expr.t)
    (expr3 : Expr.t)
    (op1 : bv_op_function)
    (op2 : bv_op_function)
    (shape : bv_op_shape)
    (flag_checks : bv_op_function list option) =
  let open Codegenerator in
  let open TypePatterns in
  let open Gil_syntax.Expr.Infix in
  let case_statement_for_float
      (regular_val0 : Expr.t)
      (regular_val1 : Expr.t)
      (regular_val2 : Expr.t) =
    let float_valx = Expr.list_nth regular_val0 1 in
    let float_valy = Expr.list_nth regular_val1 1 in
    let float_valz = Expr.list_nth regular_val2 1 in
    let* _ =
      add_return_of_value
        (Expr.EList
           [
             Expr.list_nth regular_val0 0;
             op2 [ op1 [ float_valx; float_valy ] shape; float_valz ] shape;
           ])
    in
    return ()
  in
  let patterns =
    [
      {
        exprs = [ expr1; expr2; expr3 ];
        types_ =
          [ LLVMRuntimeTypes.F32; LLVMRuntimeTypes.F32; LLVMRuntimeTypes.F32 ];
        case_stat = case_statement_for_float expr1 expr2 expr3;
      };
      {
        exprs = [ expr1; expr2; expr3 ];
        types_ =
          [ LLVMRuntimeTypes.F64; LLVMRuntimeTypes.F64; LLVMRuntimeTypes.F64 ];
        case_stat = case_statement_for_float expr1 expr2 expr3;
      };
    ]
  in
  let default_statement = add_cmd (fail_cmd "No_type_pattern_matched" []) in
  let* _ = type_dispatch patterns default_statement in
  return ()

let fp_ext_patterns
    ~(pointer_width : int)
    (expr : Expr.t)
    (shape : bv_op_shape)
    (flag_checks : bv_op_function list option) =
  let open Codegenerator in
  let open TypePatterns in
  let open Gil_syntax.Expr.Infix in
  let case_statement_for_f32_to_f64 (regular_val : Expr.t) =
    let float_val = Expr.list_nth regular_val 1 in
    let* _ =
      add_return_of_value (Expr.EList [ Expr.string "double"; float_val ])
    in
    return ()
  in
  let patterns =
    [
      {
        exprs = [ expr ];
        types_ = [ LLVMRuntimeTypes.F32 ];
        case_stat = case_statement_for_f32_to_f64 expr;
      };
    ]
  in
  let default_statement = add_cmd (fail_cmd "No_type_pattern_matched" []) in
  let* _ = type_dispatch patterns default_statement in
  return ()

let conversion_patterns
    ~(pointer_width : int)
    (expr : Expr.t)
    (op : bv_op_function)
    (shape : bv_op_shape)
    (flag_checks : bv_op_function list option) =
  let open Codegenerator in
  let open TypePatterns in
  let open Gil_syntax.Expr.Infix in
  let case_statement_for_int_to_float (regular_val : Expr.t) =
    let int_val = Expr.list_nth regular_val 1 in
    let converted_val = op [ int_val ] shape in
    let target_type =
      match shape.width_of_result with
      | Some 32 -> "float" (* F32 *)
      | Some 64 -> "double" (* F64 *)
      | _ -> "float" (* Default to F32 if width not specified *)
    in
    let* _ =
      add_return_of_value
        (Expr.EList [ Expr.string target_type; converted_val ])
    in
    return ()
  in
  let case_statement_for_float_to_int (regular_val : Expr.t) =
    let float_val = Expr.list_nth regular_val 1 in
    let converted_val = op [ float_val ] shape in
    let target_type =
      match shape.width_of_result with
      | Some width -> Expr.string ("i-" ^ string_of_int width)
      | None -> failwith "Unary operations should have a result width"
    in
    let* _ = add_return_of_value (Expr.EList [ target_type; converted_val ]) in
    return ()
  in
  let patterns =
    [
      {
        exprs = [ expr ];
        types_ = [ LLVMRuntimeTypes.Int 32 ];
        case_stat = case_statement_for_int_to_float expr;
      };
      {
        exprs = [ expr ];
        types_ = [ LLVMRuntimeTypes.Int 64 ];
        case_stat = case_statement_for_int_to_float expr;
      };
      {
        exprs = [ expr ];
        types_ = [ LLVMRuntimeTypes.F32 ];
        case_stat = case_statement_for_float_to_int expr;
      };
      {
        exprs = [ expr ];
        types_ = [ LLVMRuntimeTypes.F64 ];
        case_stat = case_statement_for_float_to_int expr;
      };
    ]
  in
  let default_statement = add_cmd (fail_cmd "No_type_pattern_matched" []) in
  let* _ = type_dispatch patterns default_statement in
  return ()

let conversion_patterns_generalized
    ~(pointer_width : int)
    (expr : Expr.t)
    (op : generalized_bv_op_function)
    (shape : bv_op_shape)
    (flag_checks : bv_op_function list option) =
  let open Codegenerator in
  let open TypePatterns in
  let open Gil_syntax.Expr.Infix in
  let case_statement_for_int_to_float (regular_val : Expr.t) =
    let int_val = Expr.list_nth regular_val 1 in
    let* converted_val = op [ int_val ] shape in
    let target_type =
      match shape.width_of_result with
      | Some 32 -> "float" (* F32 *)
      | Some 64 -> "double" (* F64 *)
      | _ -> "float" (* Default to F32 if width not specified *)
    in
    let* _ =
      add_return_of_value
        (Expr.EList [ Expr.string target_type; converted_val ])
    in
    return ()
  in
  let case_statement_for_float_to_int (regular_val : Expr.t) =
    let float_val = Expr.list_nth regular_val 1 in
    let* converted_val = op [ float_val ] shape in
    let target_type =
      match shape.width_of_result with
      | Some width -> Expr.string ("i-" ^ string_of_int width)
      | None -> failwith "Unary operations should have a result width"
    in
    let* _ = add_return_of_value (Expr.EList [ target_type; converted_val ]) in
    return ()
  in
  let patterns =
    [
      {
        exprs = [ expr ];
        types_ = [ LLVMRuntimeTypes.Int 32 ];
        case_stat = case_statement_for_int_to_float expr;
      };
      {
        exprs = [ expr ];
        types_ = [ LLVMRuntimeTypes.Int 64 ];
        case_stat = case_statement_for_int_to_float expr;
      };
      {
        exprs = [ expr ];
        types_ = [ LLVMRuntimeTypes.F32 ];
        case_stat = case_statement_for_float_to_int expr;
      };
      {
        exprs = [ expr ];
        types_ = [ LLVMRuntimeTypes.F64 ];
        case_stat = case_statement_for_float_to_int expr;
      };
    ]
  in
  let default_statement = add_cmd (fail_cmd "No_type_pattern_matched" []) in
  let* _ = type_dispatch patterns default_statement in
  return ()

let pattern_function
    (expr1 : Expr.t)
    (expr2 : Expr.t)
    (shape : bv_op_shape)
    (op : bv_op_function)
    (commutative : bool)
    (flag_checks : bv_op_function list option) =
  let open Codegenerator in
  let open TypePatterns in
  let open Gil_syntax.Expr.Infix in
  let ptr_width =
    match shape.width_of_result with
    | Some width -> width
    | None -> failwith "Pointer operations should have a result"
  in
  let case_statement_for_ptr (pval : Expr.t) (regular_val : Expr.t) =
    let pointer_offset = Expr.list_nth (Expr.list_nth pval 1) 1 in

    let int_val = Expr.list_nth regular_val 1 in
    let* _ =
      add_return_of_value
        (update_pointer pval (op [ pointer_offset; int_val ] shape))
    in
    return ()
  in
  let case_statement_for_int (regular_val0 : Expr.t) (regular_val1 : Expr.t) =
    let int_valx = Expr.list_nth regular_val0 1 in
    let int_valy = Expr.list_nth regular_val1 1 in
    let* _ = add_overflow_check flag_checks [ int_valx; int_valy ] shape in
    let* _ =
      add_return_of_value
        (Expr.EList
           [ Expr.list_nth regular_val0 0; op [ int_valx; int_valy ] shape ])
    in
    return ()
  in
  let default_statement = add_cmd (fail_cmd "No_type_pattern_matched" []) in
  let non_commutative_patterns =
    [
      {
        exprs = [ expr1; expr2 ];
        types_ = [ LLVMRuntimeTypes.Ptr; LLVMRuntimeTypes.Int ptr_width ];
        case_stat = case_statement_for_ptr expr1 expr2;
      };
      {
        exprs = [ expr1; expr2 ];
        types_ =
          [ LLVMRuntimeTypes.Int ptr_width; LLVMRuntimeTypes.Int ptr_width ];
        case_stat = case_statement_for_int expr1 expr2;
      };
    ]
  in
  let patterns =
    if commutative then
      {
        exprs = [ expr1; expr2 ];
        types_ = [ LLVMRuntimeTypes.Int ptr_width; LLVMRuntimeTypes.Ptr ];
        case_stat = case_statement_for_ptr expr2 expr1;
      }
      :: non_commutative_patterns
    else non_commutative_patterns
  in

  let* _ = type_dispatch patterns default_statement in
  return ()

module OpFunctions = struct
  open Gil_syntax

  let zip_args_with_shape (inputs : Expr.t list) (shape : bv_op_shape) :
      Expr.bv_arg list =
    List.map2 (fun expr width -> Expr.BvExpr (expr, width)) inputs shape.args

  let bv_op_function_custom_res
      ?(literals : int list option)
      (op : BVOps.t)
      inputs
      shape
      res =
    let lits = Option.to_list literals |> List.flatten in
    let args = zip_args_with_shape inputs shape in
    Expr.BVExprIntrinsic
      (op, List.map (fun x -> Expr.Literal x) lits @ args, res)

  let bv_op_function ?(literals : int list option) (op : BVOps.t) inputs shape =
    bv_op_function_custom_res ?literals op inputs shape shape.width_of_result

  let bv_op_pred ?(literals : int list option) (op : BVOps.t) inputs shape =
    bv_op_function_custom_res ?literals op inputs shape None

  let fp_op_pred (op : BinOp.t) (inputs : Expr.t list) (shape : bv_op_shape) :
      Expr.t =
    let open Gil_syntax in
    Expr.BinOp (List.hd inputs, op, List.hd (List.tl inputs))

  let fp_unop_pred (op : UnOp.t) (inputs : Expr.t list) (shape : bv_op_shape) :
      Expr.t =
    let open Gil_syntax in
    Expr.UnOp (op, List.hd inputs)

  let bv_check_function
      ?(literals : int list option)
      (op : BVOps.t)
      inputs
      shape =
    bv_op_function_custom_res ?literals op inputs shape None

  let add_op_function = bv_op_function BVOps.BVPlus
  let add_op_nuw = bv_check_function BVOps.BVUAddO
  let add_op_nsw = bv_check_function BVOps.BVSAddO
  let neg_function = bv_op_function BVOps.BVNeg
  let mul_op_function = bv_op_function BVOps.BVMul
  let sdiv_op_function = bv_op_function BVOps.BVSdiv
  let shl_op_function = bv_op_function BVOps.BVShl
  let lshr_op_function = bv_op_function BVOps.BVLShr
  let ashr_op_function = bv_op_function BVOps.BVAshr
  let srem_op_function = bv_op_function BVSrem
  let mul_op_nuw = bv_check_function BVOps.BVUMulO
  let mul_op_nsw = bv_check_function BVOps.BVSMulO
  let and_op_function = bv_op_function BVOps.BVAnd
  let or_op_function = bv_op_function BVOps.BVOr
  let xor_op_function = bv_op_function BVOps.BVXor

  let negated_function
      (f : Expr.t list -> bv_op_shape -> Expr.t)
      (inputs : Expr.t list)
      (shape : bv_op_shape) =
    let orig_res = f inputs shape in
    let negated_res = Expr.UnOp (UnOp.Not, orig_res) in
    negated_res

  let icmp_eq (inputs : Expr.t list) (shape : bv_op_shape) =
    let open Gil_syntax in
    Expr.BinOp (List.hd inputs, BinOp.Equal, List.hd (List.tl inputs))

  let icmp_ne = negated_function icmp_eq
  let icmp_ugt = negated_function (bv_op_pred BVOps.BVUleq)
  let icmp_uge = negated_function (bv_op_pred BVOps.BVUlt)
  let icmp_ult = bv_op_pred BVOps.BVUlt
  let icmp_ule = bv_op_pred BVOps.BVUleq
  let icmp_sgt = negated_function (bv_op_pred BVOps.BVSleq)
  let icmp_sge = negated_function (bv_op_pred BVOps.BVSlt)
  let icmp_slt = bv_op_pred BVOps.BVSlt
  let icmp_sle = bv_op_pred BVOps.BVSleq

  (* fcmp helpers *)
  let unordered_function (inputs : Expr.t list) (shape : bv_op_shape) =
    let lhs_nan = Expr.UnOp (UnOp.M_isNaN, List.hd inputs) in
    let rhs_nan = Expr.UnOp (UnOp.M_isNaN, List.hd (List.tl inputs)) in
    let unordered = Expr.BinOp (lhs_nan, BinOp.Or, rhs_nan) in
    unordered

  let ordered_function (inputs : Expr.t list) (shape : bv_op_shape) =
    let ordered = Expr.UnOp (UnOp.Not, unordered_function inputs shape) in
    ordered

  let ordered_and_function
      (f : Expr.t list -> bv_op_shape -> Expr.t)
      (inputs : Expr.t list)
      (shape : bv_op_shape) =
    let orig_res = f inputs shape in
    let ordered = ordered_function inputs shape in
    let ordered_res = Expr.BinOp (ordered, BinOp.And, orig_res) in
    ordered_res

  let unordered_or_function
      (f : Expr.t list -> bv_op_shape -> Expr.t)
      (inputs : Expr.t list)
      (shape : bv_op_shape) =
    let orig_res = f inputs shape in
    let unordered = unordered_function inputs shape in
    let unordered_res = Expr.BinOp (unordered, BinOp.Or, orig_res) in
    unordered_res

  (* fcmp functions *)
  let fcmp_false (inputs : Expr.t list) (shape : bv_op_shape) =
    let open Gil_syntax in
    Expr.Lit (Literal.Bool false)

  let fcmp_oeq = ordered_and_function icmp_eq

  let fcmp_ogt =
    ordered_and_function (negated_function (fp_op_pred BinOp.FLessThanEqual))

  let fcmp_oge =
    ordered_and_function (negated_function (fp_op_pred BinOp.FLessThan))

  let fcmp_olt = ordered_and_function (fp_op_pred BinOp.FLessThan)
  let fcmp_ole = ordered_and_function (fp_op_pred BinOp.FLessThanEqual)
  let fcmp_one = ordered_and_function (negated_function icmp_eq)
  let fcmp_ord = ordered_function
  let fcmp_uno = unordered_function
  let fcmp_ueq = unordered_or_function icmp_eq

  let fcmp_ugt =
    unordered_or_function (negated_function (fp_op_pred BinOp.FLessThanEqual))

  let fcmp_uge =
    unordered_or_function (negated_function (fp_op_pred BinOp.FLessThan))

  let fcmp_ult = unordered_or_function (fp_op_pred BinOp.FLessThan)
  let fcmp_ule = unordered_or_function (fp_op_pred BinOp.FLessThanEqual)
  let fcmp_une = unordered_or_function (negated_function icmp_eq)

  let fcmp_true (inputs : Expr.t list) (shape : bv_op_shape) =
    let open Gil_syntax in
    Expr.Lit (Literal.Bool true)

  let unop_function
      ?(compute_lits : (input:int -> output:int -> int list) option)
      (op : BVOps.t)
      inputs
      shape =
    match shape.width_of_result with
    | Some width ->
        let input = List.hd shape.args in
        let lits = Option.map (fun f -> f ~input ~output:width) compute_lits in
        bv_op_function ?literals:lits op inputs shape
    | None -> failwith "Unop function requires a result width"

  let zext_function =
    unop_function
      ~compute_lits:(fun ~input ~output ->
        if input > output then
          failwith "Zext requires a larger or equal output width then input"
        else [ output - input ])
      BVOps.BVZeroExtend

  let sext_function =
    unop_function
      ~compute_lits:(fun ~input ~output ->
        if input > output then
          failwith "Sext requires a larger or equal output width then input"
        else [ output - input ])
      BVOps.BVSignExtend

  let trunc_function =
    unop_function
      ~compute_lits:(fun ~input ~output ->
        if input <= output then
          failwith "Trunc requires a smaller output width than input"
        else [ output - 1; 0 ])
      BVOps.BVExtract

  let fshl_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x; y; z ] ->
        let width = shape.width_of_result |> Option.get in

        let concat_expr =
          bv_op_function BVOps.BVConcat [ x; y ]
            { shape with args = [ width; width ] }
        in
        let width_bv = Expr.Lit (Literal.LBitvector (Z.of_int width, width)) in
        let adjusted_z =
          bv_op_function BVOps.BVUrem [ z; width_bv ]
            { shape with args = [ width; width ] }
        in
        let zext_lits = Some [ width ] in
        let shift_amt =
          bv_op_function ?literals:zext_lits BVOps.BVZeroExtend [ adjusted_z ]
            { shape with args = [ width ] }
        in
        let shifted =
          bv_op_function BVOps.BVShl [ concat_expr; shift_amt ]
            { shape with args = [ width + width; width + width ] }
        in

        let ext_lits = Some [ width + width - 1; width ] in
        let result =
          bv_op_function ?literals:ext_lits BVOps.BVExtract [ shifted ]
            { shape with args = [ width ] }
        in
        return result
    | _ -> failwith "Invalid number of arguments"

  let fshr_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x; y; z ] ->
        let width = shape.width_of_result |> Option.get in

        let concat_expr =
          bv_op_function BVOps.BVConcat [ x; y ]
            { shape with args = [ width; width ] }
        in
        let width_bv = Expr.Lit (Literal.LBitvector (Z.of_int width, width)) in
        let adjusted_z =
          bv_op_function BVOps.BVUrem [ z; width_bv ]
            { shape with args = [ width; width ] }
        in
        let zext_lits = Some [ width ] in
        let shift_amt =
          bv_op_function ?literals:zext_lits BVOps.BVZeroExtend [ adjusted_z ]
            { shape with args = [ width ] }
        in
        let shifted =
          bv_op_function BVOps.BVLShr [ concat_expr; shift_amt ]
            { shape with args = [ width + width; width ] }
        in

        let ext_lits = Some [ width - 1; 0 ] in
        let result =
          bv_op_function ?literals:ext_lits BVOps.BVExtract [ shifted ]
            { shape with args = [ width ] }
        in
        return result
    | _ -> failwith "Invalid number of arguments"

  let bswap_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x ] ->
        let width = shape.width_of_result |> Option.get in

        if width mod 16 <> 0 then
          failwith "bswap requires an even number of bytes"
        else
          let num_bytes = width / 8 in

          let rec extract_bytes extracted byte_idx =
            if byte_idx >= num_bytes then extracted
            else
              let high_bit = ((byte_idx + 1) * 8) - 1 in
              let low_bit = byte_idx * 8 in
              let lits = Some [ high_bit; low_bit ] in
              let byte_expr =
                bv_op_function ?literals:lits BVOps.BVExtract [ x ]
                  { shape with args = [ width ] }
              in
              extract_bytes (extracted @ [ byte_expr ]) (byte_idx + 1)
          in

          let reversed_bytes = extract_bytes [] 0 in

          let rec concat_bytes = function
            | [] -> failwith "Empty byte list"
            | [ byte ] -> byte
            | byte :: rest ->
                let rest_result = concat_bytes rest in
                let rest_width = List.length rest * 8 in
                bv_op_function BVOps.BVConcat [ byte; rest_result ]
                  { shape with args = [ 8; rest_width ] }
          in

          let result = concat_bytes reversed_bytes in
          return result
    | _ -> failwith "Invalid number of arguments"

  let ctpop_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x ] ->
        let width = shape.width_of_result |> Option.get in

        (* Divide and conquer population count *)
        let rec popcount_dc start_idx end_idx =
          let current_width = end_idx - start_idx + 1 in
          if current_width = 1 then
            (* Base case: single bit - extract and zero-extend to target width *)
            let lits = Some [ start_idx; start_idx ] in
            let bit =
              bv_op_function ?literals:lits BVOps.BVExtract [ x ]
                { shape with args = [ width ] }
            in
            let lits_ext = Some [ width ] in
            bv_op_function ?literals:lits_ext BVOps.BVZeroExtend [ bit ]
              { shape with args = [ 1 ] }
          else
            (* Divide: split into two halves *)
            let half_width = current_width / 2 in
            let mid_idx = start_idx + half_width - 1 in

            (* Conquer: recursively compute population count for each half *)
            let upper_count = popcount_dc (mid_idx + 1) end_idx in
            let lower_count = popcount_dc start_idx mid_idx in

            (* Combine: add the results from both halves *)
            (* Both results should already be of width 'width' *)
            let sum =
              bv_op_function BVOps.BVPlus
                [ upper_count; lower_count ]
                { shape with args = [ width; width ] }
            in
            (* Truncate the result back to target width (in case of carry) *)
            let lits = Some [ width - 1; 0 ] in
            bv_op_function ?literals:lits BVOps.BVExtract [ sum ]
              { shape with args = [ width + 1 ] }
        in

        let count_result = popcount_dc 0 (width - 1) in
        return count_result
    | _ -> failwith "Invalid number of arguments"

  let cttz_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x; y ] ->
        (* TODO: After implementing poison values, use the y argument appropriately *)
        let width = shape.width_of_result |> Option.get in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in

        (* Unroll the loop: check each bit position from LSB to MSB *)
        let rec cttz_unrolled bit_idx =
          if bit_idx >= width then
            (* All bits were zero, return width *)
            let* _ =
              add_cmd (Cmd.Assignment (bindr, Expr.bv_z (Z.of_int width) width))
            in
            let* _ = add_cmd (Cmd.Goto join_block) in
            return ()
          else
            (* Extract bit at position bit_idx *)
            let lits = Some [ bit_idx; bit_idx ] in
            let bit =
              bv_op_function ?literals:lits BVOps.BVExtract [ x ]
                { shape with args = [ width ] }
            in
            (* Check if bit is 1 (i.e., not zero) *)
            let bit_is_one = Expr.BinOp (bit, BinOp.Equal, Expr.bv_z Z.one 1) in
            let* _ =
              ite bit_is_one
                ~true_case:
                  (let* _ =
                     add_cmd
                       (Cmd.Assignment
                          (bindr, Expr.bv_z (Z.of_int bit_idx) width))
                   in
                   let* _ = add_cmd (Cmd.Goto join_block) in
                   return ())
                ~false_case:(cttz_unrolled (bit_idx + 1))
            in
            return ()
        in

        let* _ = cttz_unrolled 0 in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let uitofp_function inputs shape =
    let open Gil_syntax in
    Expr.UnOp (UnOp.IntToNum, bv_op_function BVOps.BVToInt inputs shape)

  let sitofp_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x ] ->
        let input_width = List.hd shape.args in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in
        let bexpr =
          Expr.BVExprIntrinsic
            ( BVOps.BVSlt,
              [
                BvExpr (x, input_width);
                BvExpr (Expr.zero_bv input_width, input_width);
              ],
              None )
        in
        let twos_comp_bv_expr =
          Expr.BVExprIntrinsic
            (BVOps.BVNeg, [ BvExpr (x, input_width) ], Some input_width)
        in
        let twos_comp_int_expr =
          bv_op_function BVOps.BVToInt [ twos_comp_bv_expr ]
            { shape with args = [ input_width ] }
        in
        let neg_int_expr =
          Expr.BinOp
            ( twos_comp_int_expr,
              BinOp.ITimes,
              Expr.Lit (Literal.Int (Z.of_int (-1))) )
        in
        let neg_expr = Expr.UnOp (UnOp.IntToNum, neg_int_expr) in
        let pos_expr =
          Expr.UnOp (UnOp.IntToNum, bv_op_function BVOps.BVToInt [ x ] shape)
        in
        let* _ =
          ite bexpr
            ~true_case:
              (*neg *)
              (let* _ = add_cmd (Cmd.Assignment (bindr, neg_expr)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
            ~false_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, pos_expr)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let fptoui_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x ] ->
        let width = shape.width_of_result |> Option.get in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in
        let expr = Expr.BinOp (x, BinOp.FLessThan, Expr.num 0.) in
        let neg_expr = Expr.zero_bv width in
        let lits = Some [ width ] in
        let pos_expr =
          bv_op_function ?literals:lits BVOps.IntToBV
            [ Expr.UnOp (UnOp.NumToInt, x) ]
            shape
        in
        let* _ =
          ite expr
            ~true_case:
              (*neg *)
              (let* _ = add_cmd (Cmd.Assignment (bindr, neg_expr)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
            ~false_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, pos_expr)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let fptosi_function inputs shape =
    let open Gil_syntax in
    match shape.width_of_result with
    | Some width ->
        let lits = Some [ width ] in
        bv_op_function ?literals:lits BVOps.IntToBV
          [ Expr.UnOp (UnOp.NumToInt, List.hd inputs) ]
          shape
    | None -> failwith "Fptosi function requires a result width"

  let bitcast_fp_to_bv_function inputs shape =
    let open Gil_syntax in
    match shape.width_of_result with
    | Some width ->
        let lits = Some [ width ] in
        bv_op_function ?literals:lits BVOps.NumToIEEEBV [ List.hd inputs ] shape
    | None -> failwith "bitcast function requires a result width"

  let bitcast_bv_to_fp_function inputs shape =
    let open Gil_syntax in
    match shape.width_of_result with
    | Some width -> bv_op_function BVOps.IEEEBVToNum [ List.hd inputs ] shape
    | None -> failwith "bitcast function requires a result width"

  let sub_function_overflow
      (op : BVOps.t)
      (inputs : Expr.t list)
      (shape : bv_op_shape) =
    let first_shape = { shape with args = [ List.hd shape.args ] } in
    match inputs with
    | [ x; y ] ->
        bv_check_function op [ neg_function [ y ] first_shape; x ] shape
    | _ -> failwith "Invalid number of arguments"

  let sub_function inputs shape =
    let first_shape = { shape with args = [ List.hd shape.args ] } in
    match inputs with
    | [ x; y ] ->
        bv_op_function BVOps.BVPlus [ neg_function [ y ] first_shape; x ] shape
    | _ -> failwith "Invalid number of arguments"

  let fp_add_function = fp_op_pred BinOp.FPlus
  let fp_sub_function = fp_op_pred BinOp.FMinus
  let fp_mul_function = fp_op_pred BinOp.FTimes
  let fp_div_function = fp_op_pred BinOp.FDiv
  let fp_abs_function = fp_unop_pred UnOp.M_abs
  let fp_neg_function = fp_unop_pred UnOp.FUnaryMinus
  let fp_ceil_function = fp_unop_pred UnOp.M_ceil
  let fp_floor_function = fp_unop_pred UnOp.M_floor

  let fp_trunc_function (inputs : Expr.t list) (shape : bv_op_shape) : Expr.t =
    let open Gil_syntax in
    (* Floating point values in Gillian are all represented as Type.NumberType, so just return the input. This could not be implemented in gil-translate because input type differs from the output type in MLIR. *)
    List.hd inputs

  let thread_local_addr_function (inputs : Expr.t list) (shape : bv_op_shape) :
      Expr.t =
    let open Gil_syntax in
    (* Just return input value for simplicity right now *)
    List.hd inputs

  let extract_value_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x; y ] ->
        (* Use shift and extract since extract requires a literal index *)
        let res_width = shape.width_of_result |> Option.get in
        let x_width = List.hd shape.args in
        let y_width = List.nth shape.args 1 in

        (* Shift amount = x_width - (y + res_width) *)
        let res_width_bv =
          Expr.Lit (Literal.LBitvector (Z.of_int res_width, y_width))
        in
        let last_index =
          bv_op_function BVOps.BVPlus [ y; res_width_bv ]
            { shape with args = [ y_width; y_width ] }
        in
        let x_width_bv =
          Expr.Lit (Literal.LBitvector (Z.of_int x_width, x_width))
        in
        let shift_amount =
          bv_op_function BVOps.BVSub [ x_width_bv; last_index ]
            { shape with args = [ x_width; y_width ] }
        in
        let shifted =
          bv_op_function BVOps.BVLShr [ x; shift_amount ]
            { shape with args = [ x_width; y_width ] }
        in

        let high_index = res_width - 1 in
        let lits = Some [ high_index; 0 ] in
        let result =
          bv_op_function ?literals:lits BVOps.BVExtract [ shifted ]
            { shape with args = [ x_width ] }
        in
        return result
    | _ -> failwith "Invalid number of arguments"
end

let template_from_pattern_unary
    ~(op : bv_op_function)
    ~(pointer_width : int)
    ~(flag_checks : bv_op_function list option)
    (name : string)
    (shape : bv_op_shape) =
  match List.nth_opt shape.args 0 with
  | Some width when width = pointer_width ->
      op_function name 1 (function
        | [ x ] -> pattern_function_unary x shape op
        | _ -> failwith "Invalid number of arguments")
  | _ -> op_function name 1 (fun xs -> op_bv_scheme xs op flag_checks shape)

let template_from_pattern_ternary
    ~(op : bv_op_function)
    ~(commutative : bool)
    ~(pointer_width : int)
    ~(flag_checks : bv_op_function list option)
    (name : string)
    (shape : bv_op_shape) =
  match List.nth_opt shape.args 0 with
  | Some width when width = pointer_width ->
      op_function name 3 (function
        | [ x; y; z ] ->
            pattern_function_ternary x y z shape op commutative flag_checks
        | _ -> failwith "Invalid number of arguments")
  | _ -> op_function name 3 (fun xs -> op_bv_scheme xs op flag_checks shape)

let template_from_pattern
    ~(op : bv_op_function)
    ~(commutative : bool)
    ~(pointer_width : int)
    ~(flag_checks : bv_op_function list option)
    (name : string)
    (shape : bv_op_shape) =
  match List.nth_opt shape.args 0 with
  | Some width when width = pointer_width ->
      op_function name 2 (function
        | [ x; y ] -> pattern_function x y shape op commutative flag_checks
        | _ -> failwith "Invalid number of arguments")
  | _ -> op_function name 2 (fun xs -> op_bv_scheme xs op flag_checks shape)

let template_from_pattern_cmp
    ~(op : bv_op_function)
    ~(pointer_width : int)
    ~(flag_checks : bv_op_function list option)
    (name : string)
    (shape : bv_op_shape) =
  op_function name 2 (function
    | [ x; y ] -> cmp_patterns ~pointer_width x y op shape
    | _ -> failwith "Invalid number of arguments")

let template_from_pattern_fp
    ~(op : bv_op_function)
    ~(pointer_width : int)
    ~(flag_checks : bv_op_function list option)
    (name : string)
    (shape : bv_op_shape) =
  op_function name 2 (function
    | [ x; y ] -> fp_patterns ~pointer_width x y op shape flag_checks
    | _ -> failwith "Invalid number of arguments")

let template_from_pattern_fp_unary
    ~(op : bv_op_function)
    ~(pointer_width : int)
    ~(flag_checks : bv_op_function list option)
    (name : string)
    (shape : bv_op_shape) =
  op_function name 1 (function
    | [ x ] -> fp_patterns_unary ~pointer_width x op shape flag_checks
    | _ -> failwith "Invalid number of arguments")

let template_from_pattern_fp_ternary
    ~(op1 : bv_op_function)
    ~(op2 : bv_op_function)
    ~(pointer_width : int)
    ~(flag_checks : bv_op_function list option)
    (name : string)
    (shape : bv_op_shape) =
  op_function name 3 (function
    | [ x; y; z ] ->
        fp_patterns_ternary ~pointer_width x y z op1 op2 shape flag_checks
    | _ -> failwith "Invalid number of arguments")

let template_from_pattern_fp_ext
    ~(pointer_width : int)
    ~(flag_checks : bv_op_function list option)
    (name : string)
    (shape : bv_op_shape) =
  op_function name 1 (function
    | [ x ] -> fp_ext_patterns ~pointer_width x shape flag_checks
    | _ -> failwith "Invalid number of arguments")

let template_from_pattern_conversion
    ~(op : bv_op_function)
    ~(pointer_width : int)
    ~(flag_checks : bv_op_function list option)
    (name : string)
    (shape : bv_op_shape) =
  op_function name 1 (function
    | [ x ] -> conversion_patterns ~pointer_width x op shape flag_checks
    | _ -> failwith "Invalid number of arguments")

let template_from_pattern_conversion_generalized
    ~(op : generalized_bv_op_function)
    ~(pointer_width : int)
    ~(flag_checks : bv_op_function list option)
    (name : string)
    (shape : bv_op_shape) =
  op_function name 1 (function
    | [ x ] ->
        conversion_patterns_generalized ~pointer_width x op shape flag_checks
    | _ -> failwith "Invalid number of arguments")

let template_from_integer_op
    ~(op : bv_op_function)
    ~(pointer_width : int)
    ~(flag_checks : bv_op_function list option)
    (name : string)
    (shape : bv_op_shape) =
  op_function name 2 (fun xs -> op_bv_scheme xs op flag_checks shape)

module MemoryLib = struct
  let alloc_name = "alloc"
  let store_name = "store"
  let load_name = "load"
  let memset_name = "memset"
  let memcpy_name = "move"
  let memmove_name = "move"

  module M = Memories.LLVM_ALoc.MonadicSMemory

  type ptr = { base : Expr.t; offset : Expr.t }

  let access_ptr (expr : Expr.t) : ptr =
    let vl = Expr.list_nth expr 1 in
    let base = Expr.list_nth vl 0 in
    let offset = Expr.list_nth vl 1 in
    { base; offset }

  let pointer_op ~(is_ptr_case : string -> unit Codegenerator.t) (ptr : Expr.t)
      : unit Codegenerator.t =
    let open Codegenerator in
    let open Gil_syntax in
    let open Expr.Infix in
    let* _ =
      ite
        (is_type_of_expr ptr LLVMRuntimeTypes.Ptr)
        ~true_case:
          (let to_bind = fresh_sym () in
           let* _ = is_ptr_case to_bind in
           let* _ = add_return_of_value (Expr.PVar to_bind) in
           return ())
        ~false_case:
          (let* _ =
             add_cmd (fail_cmd "Pointer_operation_on_non_pointer" [ ptr ])
           in
           return ())
    in
    return ()

  let load_op ~(pointer_width : int) (exp_list : Expr.t list) :
      unit Codegenerator.t =
    let open Codegenerator in
    match exp_list with
    | [ chunk; ptr ] ->
        let { base; offset } = access_ptr ptr in
        pointer_op
          ~is_ptr_case:(fun bindr ->
            let tmp = fresh_sym () in
            (* the load should give us a raw bitvector in a list: tag it with the chunk. *)
            let* _ =
              add_cmd (Cmd.LAction (tmp, load_name, [ chunk; base; offset ]))
            in
            let* _ =
              add_cmd
                (Cmd.Assignment
                   (bindr, Expr.EList [ chunk; Expr.list_nth (Expr.PVar tmp) 0 ]))
            in
            return ())
          ptr
    | _ -> failwith "Invalid number of arguments"

  let store_op ~(pointer_width : int) (exp_list : Expr.t list) :
      unit Codegenerator.t =
    let open Codegenerator in
    match exp_list with
    (* the value here should be a tagged {{ ty; value }} *)
    | [ chunk; ptr; value ] ->
        let { base; offset } = access_ptr ptr in
        pointer_op
          ~is_ptr_case:(fun bindr ->
            (* let tmp = fresh_sym () in
            HACK(tnytown): assume that value is in tagged bv repr;
               should we add a runtime check for if the tag matches the chunk?
            let* _ =
              add_cmd (Cmd.Assignment (tmp, Expr.list_nth value 1)) in*)
            (* in store we just return out the {{}}*)
            let* _ =
              add_cmd
                (Cmd.LAction (bindr, store_name, [ chunk; base; offset; value ]))
            in
            return ())
          ptr
    | _ -> failwith "Invalid number of arguments"

  let alloc_op ~(pointer_width : int) (exp_list : Expr.t list) :
      unit Codegenerator.t =
    let open Codegenerator in
    let open Expr.Infix in
    let ty_check =
      List.fold_left
        (fun acc check -> acc && check)
        Expr.true_
        (List.map
           (fun expr ->
             is_type_of_expr expr (LLVMRuntimeTypes.Int pointer_width))
           exp_list)
    in
    match exp_list with
    | [ low; hi ] ->
        let low = Expr.list_nth low 1 in
        let hi = Expr.list_nth hi 1 in

        let* _ =
          ite ty_check
            ~true_case:
              (let bindr = fresh_sym () in
               let* _ =
                 add_cmd (Cmd.LAction (bindr, alloc_name, [ low; hi ]))
               in
               let* _ =
                 add_return_of_value
                   (LLVMRuntimeTypes.make_expr_of_type_unsafe
                      (Expr.list
                         [
                           Expr.list_nth (Expr.PVar bindr) 0;
                           Expr.zero_bv pointer_width;
                         ])
                      LLVMRuntimeTypes.Ptr)
               in
               return ())
            ~false_case:
              (let* _ = add_cmd (fail_cmd "Alloc_failed" exp_list) in
               return ())
        in
        return ()
    | _ -> failwith "Invalid number of arguments"

  let displace_pointer_op ~(pointer_width : int) (exp_list : Expr.t list) :
      unit Codegenerator.t =
    let open Codegenerator in
    let open Expr.Infix in
    match exp_list with
    | [ ptr; offset ] ->
        let type_checks =
          [
            is_type_of_expr ptr LLVMRuntimeTypes.Ptr;
            is_type_of_expr offset (LLVMRuntimeTypes.Int pointer_width);
          ]
        in
        let ty_check =
          List.fold_left (fun acc check -> acc && check) Expr.true_ type_checks
        in
        let* _ =
          ite ty_check
            ~true_case:
              (let { base; offset = ptr_offset } = access_ptr ptr in
               let new_offset =
                 OpFunctions.add_op_function
                   [ ptr_offset; Expr.list_nth offset 1 ]
                   {
                     width_of_result = Some pointer_width;
                     args = [ pointer_width; pointer_width ];
                   }
               in
               let new_ptr = update_pointer ptr new_offset in
               let* _ = add_return_of_value new_ptr in
               return ())
            ~false_case:
              (let* _ =
                 add_cmd
                   (fail_cmd "Pointer_operation_on_non_pointer" [ ptr; offset ])
               in
               return ())
        in
        return ()
    | _ -> failwith "Invalid number of arguments"

  let memset_op ~(pointer_width : int) (exp_list : Expr.t list) :
      unit Codegenerator.t =
    let open Codegenerator in
    let open Expr.Infix in
    match exp_list with
    | [ ptr; value; size ] ->
        let type_checks =
          [
            is_type_of_expr ptr LLVMRuntimeTypes.Ptr;
            is_type_of_expr value (LLVMRuntimeTypes.Int 8);
            is_type_of_expr size (LLVMRuntimeTypes.Int pointer_width);
          ]
        in
        let ty_check =
          List.fold_left (fun acc check -> acc && check) Expr.true_ type_checks
        in
        let* _ =
          ite ty_check
            ~true_case:
              (let { base; offset } = access_ptr ptr in
               let byte_value = Expr.list_nth value 1 in
               let byte_count = Expr.list_nth size 1 in
               pointer_op
                 ~is_ptr_case:(fun bindr ->
                   let* _ =
                     add_cmd
                       (Cmd.LAction
                          ( bindr,
                            memset_name,
                            [ base; offset; byte_value; byte_count ] ))
                   in
                   return ())
                 ptr)
            ~false_case:
              (let* _ =
                 add_cmd (fail_cmd "Memset_type_error" [ ptr; value; size ])
               in
               return ())
        in
        return ()
    | _ -> failwith "Invalid number of arguments"

  let memcpy_op ~(pointer_width : int) (exp_list : Expr.t list) :
      unit Codegenerator.t =
    let open Codegenerator in
    let open Expr.Infix in
    match exp_list with
    | [ dst; src; len ] ->
        let type_checks =
          [
            is_type_of_expr dst LLVMRuntimeTypes.Ptr;
            is_type_of_expr src LLVMRuntimeTypes.Ptr;
            is_type_of_expr len (LLVMRuntimeTypes.Int pointer_width);
          ]
        in
        let ty_check =
          List.fold_left (fun acc check -> acc && check) Expr.true_ type_checks
        in
        let* _ =
          ite ty_check
            ~true_case:
              (let { base = dst_base; offset = dst_offset } = access_ptr dst in
               let { base = src_base; offset = src_offset } = access_ptr src in
               let byte_count = Expr.list_nth len 1 in
               pointer_op
                 ~is_ptr_case:(fun bindr ->
                   let* _ =
                     add_cmd
                       (Cmd.LAction
                          ( bindr,
                            memcpy_name,
                            [
                              dst_base;
                              dst_offset;
                              src_base;
                              src_offset;
                              byte_count;
                            ] ))
                   in
                   return ())
                 dst)
            ~false_case:
              (let* _ =
                 add_cmd (fail_cmd "Memcpy_type_error" [ dst; src; len ])
               in
               return ())
        in
        return ()
    | _ -> failwith "Invalid number of arguments"

  let memmove_op ~(pointer_width : int) (exp_list : Expr.t list) :
      unit Codegenerator.t =
    let open Codegenerator in
    let open Expr.Infix in
    match exp_list with
    | [ dst; src; len ] ->
        let type_checks =
          [
            is_type_of_expr dst LLVMRuntimeTypes.Ptr;
            is_type_of_expr src LLVMRuntimeTypes.Ptr;
            is_type_of_expr len (LLVMRuntimeTypes.Int pointer_width);
          ]
        in
        let ty_check =
          List.fold_left (fun acc check -> acc && check) Expr.true_ type_checks
        in
        let* _ =
          ite ty_check
            ~true_case:
              (let { base = dst_base; offset = dst_offset } = access_ptr dst in
               let { base = src_base; offset = src_offset } = access_ptr src in
               let byte_count = Expr.list_nth len 1 in
               pointer_op
                 ~is_ptr_case:(fun bindr ->
                   let temp_buf_sym = fresh_sym () in
                   let* _ =
                     add_cmd
                       (Cmd.LAction
                          ( temp_buf_sym,
                            alloc_name,
                            [ Expr.zero_bv pointer_width; byte_count ] ))
                   in
                   let temp_base = Expr.list_nth (Expr.PVar temp_buf_sym) 0 in
                   let temp_offset = Expr.zero_bv pointer_width in
                   let* _ =
                     add_cmd
                       (Cmd.LAction
                          ( bindr,
                            memcpy_name,
                            [
                              temp_base;
                              temp_offset;
                              src_base;
                              src_offset;
                              byte_count;
                            ] ))
                   in
                   let* _ =
                     add_cmd
                       (Cmd.LAction
                          ( bindr,
                            memcpy_name,
                            [
                              dst_base;
                              dst_offset;
                              temp_base;
                              temp_offset;
                              byte_count;
                            ] ))
                   in
                   return ())
                 dst)
            ~false_case:
              (let* _ =
                 add_cmd (fail_cmd "Memmove_type_error" [ dst; src; len ])
               in
               return ())
        in
        return ()
    | _ -> failwith "Invalid number of arguments"

  let vastart_op ~(pointer_width : int) (exp_list : Expr.t list) :
      unit Codegenerator.t =
    let open Codegenerator in
    let open Gil_syntax in
    (* Fixed buffer size: 10 variadic args * 8 bytes = 80 bytes *)
    let buffer_size_bv = Expr.bv_z (Z.of_int 80) pointer_width in
    let open Expr.Infix in
    match exp_list with
    | [ ap; variadic_args ] ->
        let ty_check = is_type_of_expr ap LLVMRuntimeTypes.Ptr in
        let* _ =
          ite ty_check
            ~true_case:
              (let { base; offset } = access_ptr ap in
               let bindr = fresh_sym () in

               (* System V ABI x86-64: Set offsets to indicate all register args used *)
               let gp_offset_value = Expr.bv_z (Z.of_int 48) 32 in
               let fp_offset_value = Expr.bv_z (Z.of_int 304) 32 in

               (* Initialize va_list structure fields: *)

               (* Field 0: gp_offset (i32) = 48 *)
               let gp_offset_ptr_offset = Expr.zero_bv pointer_width in
               let gp_offset_tagged =
                 Expr.EList [ Expr.string "i-32"; gp_offset_value ]
               in
               let chunk_i32 = Expr.string "i-32" in
               let* _ =
                 add_cmd
                   (Cmd.LAction
                      ( bindr,
                        store_name,
                        [
                          chunk_i32;
                          base;
                          gp_offset_ptr_offset;
                          gp_offset_tagged;
                        ] ))
               in

               (* Field 1: fp_offset (i32) = 304 *)
               let fp_offset_ptr_offset =
                 Expr.bv_z (Z.of_int 4) pointer_width
               in
               let fp_offset_tagged =
                 Expr.EList [ Expr.string "i-32"; fp_offset_value ]
               in
               (* Calculate adjusted offset for field 1 *)
               let adjusted_offset_1 =
                 OpFunctions.add_op_function
                   [ offset; fp_offset_ptr_offset ]
                   {
                     width_of_result = Some pointer_width;
                     args = [ pointer_width; pointer_width ];
                   }
               in
               let* _ =
                 add_cmd
                   (Cmd.LAction
                      ( bindr,
                        store_name,
                        [ chunk_i32; base; adjusted_offset_1; fp_offset_tagged ]
                      ))
               in

               (* Allocate overflow_arg_area with fixed size for max 10 variadic args *)
               let overflow_area_sym = fresh_sym () in
               let* _ =
                 add_cmd
                   (Cmd.LAction
                      ( overflow_area_sym,
                        alloc_name,
                        [ Expr.zero_bv pointer_width; buffer_size_bv ] ))
               in
               let overflow_area_base =
                 Expr.list_nth (Expr.PVar overflow_area_sym) 0
               in

               let list_len_sym = fresh_sym () in
               let* _ =
                 add_cmd
                   (Cmd.Assignment
                      (list_len_sym, Expr.UnOp (UnOp.LstLen, variadic_args)))
               in
               let num_variadic_int = Expr.PVar list_len_sym in

               (* Store each variadic argument into the overflow area *)
               let store_variadic_args =
                 let idx_int_var = fresh_sym () in
                 let offset_bv_var = fresh_sym () in
                 let loop_label = fresh_sym () in
                 let body_label = fresh_sym () in
                 let exit_label = fresh_sym () in

                 (* idx_int = 0 (integer for list indexing) *)
                 let* _ =
                   add_cmd
                     (Cmd.Assignment (idx_int_var, Expr.Lit (Literal.Int Z.zero)))
                 in
                 (* offset_bv = 0 (bitvector for memory offset) *)
                 let* _ =
                   add_cmd
                     (Cmd.Assignment (offset_bv_var, Expr.zero_bv pointer_width))
                 in

                 (* Loop header: check if idx_int < num_variadic_int (integer comparison) *)
                 let* _ = new_block loop_label in
                 let idx_int_expr = Expr.PVar idx_int_var in
                 let offset_bv_expr = Expr.PVar offset_bv_var in
                 let loop_cond =
                   Expr.BinOp (idx_int_expr, BinOp.ILessThan, num_variadic_int)
                 in
                 let* _ =
                   add_cmd (Cmd.GuardedGoto (loop_cond, body_label, exit_label))
                 in

                 (* Loop body *)
                 let* _ = new_block body_label in

                 let arg_val_sym = fresh_sym () in
                 let* _ =
                   add_cmd
                     (Cmd.Assignment
                        ( arg_val_sym,
                          Expr.BinOp (variadic_args, BinOp.LstNth, idx_int_expr)
                        ))
                 in
                 let arg_val = Expr.PVar arg_val_sym in

                 let arg_chunk = Expr.list_nth arg_val 0 in

                 (* Store the argument value at the bitvector offset using its own chunk *)
                 let store_result = fresh_sym () in
                 let* _ =
                   add_cmd
                     (Cmd.LAction
                        ( store_result,
                          store_name,
                          [
                            arg_chunk;
                            overflow_area_base;
                            offset_bv_expr;
                            arg_val;
                          ] ))
                 in

                 let one_int = Expr.Lit (Literal.Int Z.one) in
                 let next_idx_int =
                   Expr.BinOp (idx_int_expr, BinOp.IPlus, one_int)
                 in
                 let* _ =
                   add_cmd (Cmd.Assignment (idx_int_var, next_idx_int))
                 in

                 let eight_bv = Expr.bv_z (Z.of_int 8) pointer_width in
                 let next_offset_bv =
                   OpFunctions.add_op_function
                     [ offset_bv_expr; eight_bv ]
                     {
                       width_of_result = Some pointer_width;
                       args = [ pointer_width; pointer_width ];
                     }
                 in
                 let* _ =
                   add_cmd (Cmd.Assignment (offset_bv_var, next_offset_bv))
                 in

                 (* Jump back to loop header *)
                 let* _ = add_cmd (Cmd.Goto loop_label) in

                 (* Exit label *)
                 let* _ = new_block exit_label in
                 return ()
               in

               let* _ = store_variadic_args in

               (* Field 2: overflow_arg_area (ptr) = pointer to allocated overflow area *)
               let overflow_ptr_value =
                 LLVMRuntimeTypes.make_expr_of_type_unsafe
                   (Expr.list
                      [ overflow_area_base; Expr.zero_bv pointer_width ])
                   LLVMRuntimeTypes.Ptr
               in
               let overflow_ptr_offset = Expr.bv_z (Z.of_int 8) pointer_width in
               let chunk_ptr = Expr.string "i-64" in
               (* Calculate adjusted offset for field 2 *)
               let adjusted_offset_2 =
                 OpFunctions.add_op_function
                   [ offset; overflow_ptr_offset ]
                   {
                     width_of_result = Some pointer_width;
                     args = [ pointer_width; pointer_width ];
                   }
               in
               let* _ =
                 add_cmd
                   (Cmd.LAction
                      ( bindr,
                        store_name,
                        [
                          chunk_ptr; base; adjusted_offset_2; overflow_ptr_value;
                        ] ))
               in

               (* Field 3: reg_save_area (ptr) = NULL (no register args stored) *)
               let null_ptr_value =
                 LLVMRuntimeTypes.make_expr_of_type_unsafe
                   (Expr.list
                      [ Expr.zero_bv pointer_width; Expr.zero_bv pointer_width ])
                   LLVMRuntimeTypes.Ptr
               in
               let reg_save_ptr_offset =
                 Expr.bv_z (Z.of_int 16) pointer_width
               in
               (* Calculate adjusted offset for field 3 *)
               let adjusted_offset_3 =
                 OpFunctions.add_op_function
                   [ offset; reg_save_ptr_offset ]
                   {
                     width_of_result = Some pointer_width;
                     args = [ pointer_width; pointer_width ];
                   }
               in
               let* _ =
                 add_cmd
                   (Cmd.LAction
                      ( bindr,
                        store_name,
                        [ chunk_ptr; base; adjusted_offset_3; null_ptr_value ]
                      ))
               in

               let* _ = add_return_of_value (Expr.PVar bindr) in
               return ())
            ~false_case:
              (let* _ =
                 add_cmd
                   (fail_cmd "Vastart_ap_not_pointer" [ ap; variadic_args ])
               in
               return ())
        in
        return ()
    | _ -> failwith "Invalid number of arguments for llvm_vastart"

  let construct_simple_op
      ~(arity : int)
      ~(f : pointer_width:int -> Expr.t list -> unit Codegenerator.t)
      ~(pointer_width : int)
      (name : string) : Monomorphizer.basic_proc =
    op_function name arity (f ~pointer_width)

  let ops =
    [
      {
        name = "llvm_load";
        generator = SimpleOp (construct_simple_op ~arity:2 ~f:load_op);
      };
      {
        name = "llvm_store";
        generator = SimpleOp (construct_simple_op ~arity:3 ~f:store_op);
      };
      {
        name = "llvm_displace_pointer";
        generator =
          SimpleOp (construct_simple_op ~arity:2 ~f:displace_pointer_op);
      };
      {
        name = "llvm_alloca";
        generator = SimpleOp (construct_simple_op ~arity:2 ~f:alloc_op);
      };
      {
        name = "llvm_memset";
        generator = SimpleOp (construct_simple_op ~arity:3 ~f:memset_op);
      };
      {
        name = "llvm_memcpy";
        generator = SimpleOp (construct_simple_op ~arity:3 ~f:memcpy_op);
      };
      {
        name = "llvm_memmove";
        generator = SimpleOp (construct_simple_op ~arity:3 ~f:memmove_op);
      };
      {
        name = "llvm_vastart";
        generator = SimpleOp (construct_simple_op ~arity:2 ~f:vastart_op);
      };
    ]
end

let cmpxchg_op (exprs : Expr.t list) (shape : bv_op_shape) :
    Expr.t Codegenerator.t =
  let open Codegenerator in
  match exprs with
  | [ ptr; y; z ] ->
      let value_width = List.nth shape.args 1 in
      let chunk = Chunk.IntegerChunk value_width in
      let chunk_expr = Expr.string (Chunk.to_string chunk) in
      let ptr_struct = MemoryLib.access_ptr ptr in
      let base = ptr_struct.MemoryLib.base in
      let offset = ptr_struct.MemoryLib.offset in
      let result_var = fresh_sym () in
      let tmp = fresh_sym () in
      let success_label = fresh_sym () in
      let failure_label = fresh_sym () in
      let join_label = fresh_sym () in

      (* Load the current value *)
      let* _ =
        add_cmd
          (Cmd.LAction (tmp, MemoryLib.load_name, [ chunk_expr; base; offset ]))
      in
      let current_value = Expr.list_nth (Expr.PVar tmp) 0 in

      let bexpr =
        Expr.BVExprIntrinsic
          ( BVOps.BVUleq,
            [ BvExpr (current_value, value_width); BvExpr (y, value_width) ],
            None )
      in
      let bexpr2 =
        Expr.BVExprIntrinsic
          ( BVOps.BVUleq,
            [ BvExpr (y, value_width); BvExpr (current_value, value_width) ],
            None )
      in
      let bexpr_final = Expr.BinOp (bexpr, BinOp.And, bexpr2) in
      let* _ =
        add_cmd (Cmd.GuardedGoto (bexpr_final, success_label, failure_label))
      in

      (* Success case: store the new value and set success flag *)
      let* _ = new_block success_label in
      let store_result = fresh_sym () in
      let typed_z = Expr.EList [ chunk_expr; z ] in
      let* _ =
        add_cmd
          (Cmd.LAction
             ( store_result,
               MemoryLib.store_name,
               [ chunk_expr; base; offset; typed_z ] ))
      in
      let one = Expr.Lit (Literal.LBitvector (Z.of_int 1, 1)) in
      let concat_shape =
        { args = [ value_width; 1 ]; width_of_result = Some (value_width + 1) }
      in
      let result =
        OpFunctions.bv_op_function BVOps.BVConcat [ current_value; one ]
          concat_shape
      in
      let* _ = add_cmd (Cmd.Assignment (result_var, result)) in
      let* _ = add_cmd (Cmd.Goto join_label) in

      (* Failure case: don't store, set failure flag *)
      let* _ = new_block failure_label in
      let zero = Expr.zero_bv 1 in
      let concat_shape =
        { args = [ value_width; 1 ]; width_of_result = Some (value_width + 1) }
      in
      let result =
        OpFunctions.bv_op_function BVOps.BVConcat [ current_value; zero ]
          concat_shape
      in
      let* _ = add_cmd (Cmd.Assignment (result_var, result)) in
      let* _ = add_cmd (Cmd.Goto join_label) in

      (* Join point: return the result *)
      let* _ = new_block join_label in
      return (Expr.PVar result_var)
  | _ -> failwith "Invalid number of arguments"

(*
TODO(Ian): there's probably a nice way to make a product functor that
produces modules of the OpTemplates type by appending their 
dependencies and template_operations and renaming the deps to keep things separate etc etc.
*)
module Libc = struct
  let libc_prefix = "libc_"
  let libc_mul_name = libc_prefix ^ "bvmul_sizet"
  let libc_alloca_name = libc_prefix ^ "_llvm_alloca"
  let libc_memset_name = "llvm_memset"
  let libc_memcpy_name = "llvm_memcpy"
  let libc_memmove_name = "llvm_memmove"

  let libc_dependencies ~(pointer_width : int) =
    [
      {
        name = "bvmul";
        output_name = libc_mul_name;
        spec =
          ValueSpec
            {
              flags = [ NoSignedWrap; NoUnsignedWrap ];
              shape =
                {
                  args = [ pointer_width; pointer_width ];
                  width_of_result = Some pointer_width;
                };
            };
      };
      {
        name = "llvm_alloca";
        output_name = libc_alloca_name;
        spec = SimpleSpec;
      };
      { name = "printf"; output_name = "printf"; spec = SimpleSpec };
      { name = "calloc"; output_name = "calloc"; spec = SimpleSpec };
      { name = "exit"; output_name = "exit"; spec = SimpleSpec };
      { name = "getchar"; output_name = "getchar"; spec = SimpleSpec };
      {
        name = "llvm_memset";
        output_name = libc_memset_name;
        spec = SimpleSpec;
      };
      {
        name = "llvm_memcpy";
        output_name = libc_memcpy_name;
        spec = SimpleSpec;
      };
      {
        name = "llvm_memmove";
        output_name = libc_memmove_name;
        spec = SimpleSpec;
      };
    ]

  let constant_return_func
      ~(const : Expr.t)
      ~(pointer_width : int)
      (exp_list : Expr.t list) : unit Codegenerator.t =
    let open Codegenerator in
    let* _ = add_return_of_value const in
    return ()

  let const_success_func ~(pointer_width : int) (exp_list : Expr.t list) :
      unit Codegenerator.t =
    constant_return_func
      ~const:
        (LLVMRuntimeTypes.make_expr_of_type_unsafe (Expr.int 0)
           (LLVMRuntimeTypes.Int pointer_width))
      ~pointer_width exp_list

  let type_checked
      (exp_list : Expr.t list)
      (type_ : LLVMRuntimeTypes.t list)
      (success : unit Codegenerator.t)
      (failure : unit Codegenerator.t) : unit Codegenerator.t =
    let open Codegenerator in
    let open Expr.Infix in
    let ty_check =
      List.fold_left
        (fun acc check -> acc && check)
        Expr.true_
        (List.map2 (fun ty expr -> is_type_of_expr expr ty) type_ exp_list)
    in
    let* _ = ite ty_check ~true_case:success ~false_case:failure in
    return ()

  let type_check_with_failure
      (exp_list : Expr.t list)
      (type_ : LLVMRuntimeTypes.t list)
      (success : unit Codegenerator.t) : unit Codegenerator.t =
    let open Codegenerator in
    let open Expr.Infix in
    type_checked exp_list type_ success
      (let* _ = add_cmd (fail_cmd "Type_check_failed" exp_list) in
       return ())

  let calloc ~(pointer_width : int) (exp_list : Expr.t list) :
      unit Codegenerator.t =
    let open Codegenerator in
    match exp_list with
    | [ count; size ] ->
        let types =
          [
            LLVMRuntimeTypes.Int pointer_width;
            LLVMRuntimeTypes.Int pointer_width;
          ]
        in
        type_check_with_failure exp_list types
          (* TODO(Ian): we can probably have some like combinator that gens a fresh sym for a bind and then forwards it to the next expr to make these things cleaner *)
          (let to_bind = fresh_sym () in
           let* _ =
             add_cmd
               (Cmd.Call
                  ( to_bind,
                    Expr.string libc_mul_name,
                    [ count; size ],
                    None,
                    None ))
           in
           let alloc_result = fresh_sym () in
           let size_var = Expr.PVar to_bind in
           let zero_const =
             Expr.list [ Expr.list_nth size_var 0; Expr.int 0 ]
           in
           let* _ =
             add_cmd
               (Cmd.LAction
                  (alloc_result, libc_alloca_name, [ zero_const; size_var ]))
           in
           let* _ = add_return_of_value (Expr.PVar alloc_result) in
           return ())
    | _ -> failwith "Invalid number of arguments"

  (* TODO(Ian): bit of a hack *)
  let exit ~(pointer_width : int) (exp_list : Expr.t list) :
      unit Codegenerator.t =
    let open Codegenerator in
    match exp_list with
    | [ code ] ->
        let* _ = add_cmd (Cmd.Logic (LCmd.Assume Expr.false_)) in
        let* _ = add_cmd Cmd.ReturnNormal in
        return ()
    | _ -> failwith "Invalid number of arguments"

  let make_symbolic_of_type (ty : LLVMRuntimeTypes.t) : Expr.t Codegenerator.t =
    let open Codegenerator in
    let bindr = fresh_sym () in
    let* _ = add_cmd (Cmd.Logic (LCmd.FreshSVar bindr)) in
    let* _ =
      add_cmd
        (Cmd.Logic
           (LCmd.AssumeType
              (Expr.PVar bindr, ty |> LLVMRuntimeTypes.rtype_to_gil_type)))
    in
    let to_return = fresh_sym () in
    let typeified =
      LLVMRuntimeTypes.make_expr_of_type_unsafe (Expr.PVar bindr) ty
    in
    let* _ = add_cmd (Cmd.Assignment (to_return, typeified)) in
    return (Expr.PVar to_return)

  let getchar ~(pointer_width : int) (exp_list : Expr.t list) :
      unit Codegenerator.t =
    let open Codegenerator in
    match exp_list with
    | [] ->
        let* symb_val = make_symbolic_of_type (LLVMRuntimeTypes.Int 32) in
        let* _ = add_return_of_value symb_val in
        return ()
    | _ -> failwith "Invalid number of arguments"

  let libc_ops =
    [
      {
        name = "getchar";
        generator = SimpleOp (MemoryLib.construct_simple_op ~arity:0 ~f:getchar);
      };
      {
        name = "calloc";
        generator = SimpleOp (MemoryLib.construct_simple_op ~arity:2 ~f:calloc);
      };
      (* NOTE(Ian): Variadics add an argument that aggregates additional args into a list*)
      {
        name = "printf";
        generator =
          SimpleOp
            (MemoryLib.construct_simple_op ~arity:2 ~f:const_success_func);
      };
      {
        name = "fprintf";
        generator =
          SimpleOp
            (MemoryLib.construct_simple_op ~arity:3 ~f:const_success_func);
      };
      {
        name = "exit";
        generator = SimpleOp (MemoryLib.construct_simple_op ~arity:1 ~f:exit);
      };
    ]
end

module UtilityOps = struct
  let is_true_func ~(pointer_width : int) (exprs : Expr.t list) :
      unit Codegenerator.t =
    let open Codegenerator in
    let open Expr.Infix in
    match exprs with
    | [ x ] ->
        let* _ =
          Libc.type_check_with_failure [ x ] [ LLVMRuntimeTypes.Int 1 ]
            (let bit = Expr.list_nth x 1 in
             let is_bit_true = bit == Expr.bv_z Z.one 1 in
             let* _ =
               ite is_bit_true
                 ~true_case:
                   (let* _ = add_return_of_value Expr.true_ in
                    return ())
                 ~false_case:
                   (let* _ = add_return_of_value Expr.false_ in
                    return ())
             in
             return ())
        in
        return ()
    | _ -> failwith "Invalid number of arguments"

  let is_true_op =
    {
      name = "is_true";
      generator =
        SimpleOp (MemoryLib.construct_simple_op ~arity:1 ~f:is_true_func);
    }

  let abs_op_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x ] ->
        (* x is extracted so we setup something to bind with ite *)
        let width = shape.width_of_result |> Option.get in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in
        let bexpr =
          Expr.BVExprIntrinsic
            ( BVOps.BVSlt,
              [ BvExpr (x, width); BvExpr (Expr.zero_bv width, width) ],
              None )
        in
        let neg_expr =
          Expr.BVExprIntrinsic (BVOps.BVNeg, [ BvExpr (x, width) ], Some width)
        in
        let* _ =
          ite bexpr
            ~true_case:
              (*neg *)
              (let* _ = add_cmd (Cmd.Assignment (bindr, neg_expr)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
            ~false_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, x)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let umin_op_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x; y ] ->
        let width = shape.width_of_result |> Option.get in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in
        let bexpr =
          Expr.BVExprIntrinsic
            (BVOps.BVUlt, [ BvExpr (x, width); BvExpr (y, width) ], None)
        in
        let* _ =
          ite bexpr
            ~true_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, x)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
            ~false_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, y)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let umax_op_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x; y ] ->
        let width = shape.width_of_result |> Option.get in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in
        let bexpr =
          Expr.BVExprIntrinsic
            (BVOps.BVUlt, [ BvExpr (x, width); BvExpr (y, width) ], None)
        in
        let* _ =
          ite bexpr
            ~true_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, y)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
            ~false_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, x)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let smin_op_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x; y ] ->
        let width = shape.width_of_result |> Option.get in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in
        let bexpr =
          Expr.BVExprIntrinsic
            (BVOps.BVSlt, [ BvExpr (x, width); BvExpr (y, width) ], None)
        in
        let* _ =
          ite bexpr
            ~true_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, x)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
            ~false_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, y)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let smax_op_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x; y ] ->
        let width = shape.width_of_result |> Option.get in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in
        let bexpr =
          Expr.BVExprIntrinsic
            (BVOps.BVSlt, [ BvExpr (x, width); BvExpr (y, width) ], None)
        in
        let* _ =
          ite bexpr
            ~true_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, y)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
            ~false_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, x)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let select_op_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x; y; z ] ->
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in
        let bexpr =
          Expr.BVExprIntrinsic
            (BVOps.BVUlt, [ BvExpr (Expr.zero_bv 1, 1); BvExpr (x, 1) ], None)
        in
        let* _ =
          ite bexpr
            ~true_case:
              (* condition is true *)
              (let* _ = add_cmd (Cmd.Assignment (bindr, y)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
            ~false_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, z)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let create_symbolic_int_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [] ->
        let width = shape.width_of_result |> Option.get in
        let bindr = fresh_sym () in
        let* _ = add_cmd (Cmd.Logic (LCmd.FreshSVar bindr)) in
        let* _ =
          add_cmd
            (Cmd.Logic
               (LCmd.AssumeType
                  ( Expr.PVar bindr,
                    LLVMRuntimeTypes.rtype_to_gil_type
                      (LLVMRuntimeTypes.Int width) )))
        in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let create_symbolic_float_function (exprs : Expr.t list) (shape : bv_op_shape)
      : Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [] ->
        let width = shape.width_of_result |> Option.get in
        let rtype =
          match width with
          | 32 -> LLVMRuntimeTypes.F32
          | 64 -> LLVMRuntimeTypes.F64
          | _ -> failwith "Invalid width"
        in
        let bindr = fresh_sym () in
        let* _ = add_cmd (Cmd.Logic (LCmd.FreshSVar bindr)) in
        let* _ =
          add_cmd
            (Cmd.Logic
               (LCmd.AssumeType
                  (Expr.PVar bindr, LLVMRuntimeTypes.rtype_to_gil_type rtype)))
        in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let create_symbolic_ptr_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [] ->
        let bindr = fresh_sym () in
        let* _ = add_cmd (Cmd.Logic (LCmd.FreshSVar bindr)) in
        let* _ =
          add_cmd
            (Cmd.Logic
               (LCmd.AssumeType
                  ( Expr.PVar bindr,
                    LLVMRuntimeTypes.rtype_to_gil_type LLVMRuntimeTypes.Ptr )))
        in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let usubsat_op_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x; y ] ->
        let width = shape.width_of_result |> Option.get in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in
        let bexpr =
          Expr.BVExprIntrinsic
            (BVOps.BVUleq, [ BvExpr (x, width); BvExpr (y, width) ], None)
        in
        let zero_expr = Expr.zero_bv width in
        let pos_expr =
          Expr.BVExprIntrinsic
            (BVOps.BVSub, [ BvExpr (x, width); BvExpr (y, width) ], Some width)
        in
        let* _ =
          ite bexpr
            ~true_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, zero_expr)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
            ~false_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, pos_expr)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let uaddsat_op_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    let open Gillian.Gil_syntax.Expr in
    match exprs with
    | [ x; y ] ->
        let width = shape.width_of_result |> Option.get in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in

        let add_expr =
          Expr.BVExprIntrinsic
            (BVOps.BVPlus, [ BvExpr (x, width); BvExpr (y, width) ], Some width)
        in
        let max_val = bv_z (Z.pred (Z.shift_left Z.one width)) width in

        (* Check if x + y would overflow by checking if x > max_val - y *)
        let max_minus_y =
          Expr.BVExprIntrinsic
            ( BVOps.BVSub,
              [ BvExpr (max_val, width); BvExpr (y, width) ],
              Some width )
        in
        let bexpr =
          Expr.BVExprIntrinsic
            ( BVOps.BVUlt,
              [ BvExpr (max_minus_y, width); BvExpr (x, width) ],
              None )
        in
        let* _ =
          ite bexpr
            ~true_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, max_val)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
            ~false_case:
              (let* _ = add_cmd (Cmd.Assignment (bindr, add_expr)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let ssubsat_op_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    let open Gillian.Gil_syntax.Expr in
    match exprs with
    | [ x; y ] ->
        let width = shape.width_of_result |> Option.get in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in

        let sub_expr =
          Expr.BVExprIntrinsic
            (BVOps.BVSub, [ BvExpr (x, width); BvExpr (y, width) ], Some width)
        in
        let max_val = bv_z (Z.pred (Z.shift_left Z.one (width - 1))) width in
        let min_val = bv_z (Z.shift_left Z.one (width - 1)) width in
        let zero = Expr.zero_bv width in

        (* Check if y is positive *)
        let y_check =
          Expr.BVExprIntrinsic
            (BVOps.BVSlt, [ BvExpr (zero, width); BvExpr (y, width) ], None)
        in
        let* _ =
          ite y_check
            ~true_case:
              ((* Check if x - y would underflow by checking if x < min_val + y *)
               let min_plus_y =
                 Expr.BVExprIntrinsic
                   ( BVOps.BVPlus,
                     [ BvExpr (min_val, width); BvExpr (y, width) ],
                     Some width )
               in
               let x_check =
                 Expr.BVExprIntrinsic
                   ( BVOps.BVSlt,
                     [ BvExpr (x, width); BvExpr (min_plus_y, width) ],
                     None )
               in
               let* _ =
                 ite x_check
                   ~true_case:
                     (let* _ = add_cmd (Cmd.Assignment (bindr, min_val)) in
                      let* _ = add_cmd (Cmd.Goto join_block) in
                      return ())
                   ~false_case:
                     (let* _ = add_cmd (Cmd.Assignment (bindr, sub_expr)) in
                      let* _ = add_cmd (Cmd.Goto join_block) in
                      return ())
               in
               return ())
            ~false_case:
              ((* Check if x - y would overflow by checking if x > max_val + y *)
               let max_plus_y =
                 Expr.BVExprIntrinsic
                   ( BVOps.BVPlus,
                     [ BvExpr (max_val, width); BvExpr (y, width) ],
                     Some width )
               in
               let x_check =
                 Expr.BVExprIntrinsic
                   ( BVOps.BVSlt,
                     [ BvExpr (max_plus_y, width); BvExpr (x, width) ],
                     None )
               in
               let* _ =
                 ite x_check
                   ~true_case:
                     (let* _ = add_cmd (Cmd.Assignment (bindr, max_val)) in
                      let* _ = add_cmd (Cmd.Goto join_block) in
                      return ())
                   ~false_case:
                     (let* _ = add_cmd (Cmd.Assignment (bindr, sub_expr)) in
                      let* _ = add_cmd (Cmd.Goto join_block) in
                      return ())
               in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let saddsat_op_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    let open Gillian.Gil_syntax.Expr in
    match exprs with
    | [ x; y ] ->
        let width = shape.width_of_result |> Option.get in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in

        let add_expr =
          Expr.BVExprIntrinsic
            (BVOps.BVPlus, [ BvExpr (x, width); BvExpr (y, width) ], Some width)
        in
        let max_val = bv_z (Z.pred (Z.shift_left Z.one (width - 1))) width in
        let min_val = bv_z (Z.shift_left Z.one (width - 1)) width in
        let zero = Expr.zero_bv width in

        (* Check if y is positive *)
        let y_check =
          Expr.BVExprIntrinsic
            (BVOps.BVSlt, [ BvExpr (zero, width); BvExpr (y, width) ], None)
        in
        let* _ =
          ite y_check
            ~true_case:
              ((* Check if x + y would overflow by checking if x > max_val - y *)
               let max_minus_y =
                 Expr.BVExprIntrinsic
                   ( BVOps.BVSub,
                     [ BvExpr (max_val, width); BvExpr (y, width) ],
                     Some width )
               in
               let x_check =
                 Expr.BVExprIntrinsic
                   ( BVOps.BVSlt,
                     [ BvExpr (max_minus_y, width); BvExpr (x, width) ],
                     None )
               in
               let* _ =
                 ite x_check
                   ~true_case:
                     (let* _ = add_cmd (Cmd.Assignment (bindr, max_val)) in
                      let* _ = add_cmd (Cmd.Goto join_block) in
                      return ())
                   ~false_case:
                     (let* _ = add_cmd (Cmd.Assignment (bindr, add_expr)) in
                      let* _ = add_cmd (Cmd.Goto join_block) in
                      return ())
               in
               return ())
            ~false_case:
              ((* Check if x + y would underflow by checking if x < min_val - y *)
               let min_minus_y =
                 Expr.BVExprIntrinsic
                   ( BVOps.BVSub,
                     [ BvExpr (min_val, width); BvExpr (y, width) ],
                     Some width )
               in
               let x_check =
                 Expr.BVExprIntrinsic
                   ( BVOps.BVSlt,
                     [ BvExpr (x, width); BvExpr (min_minus_y, width) ],
                     None )
               in
               let* _ =
                 ite x_check
                   ~true_case:
                     (let* _ = add_cmd (Cmd.Assignment (bindr, min_val)) in
                      let* _ = add_cmd (Cmd.Goto join_block) in
                      return ())
                   ~false_case:
                     (let* _ = add_cmd (Cmd.Assignment (bindr, add_expr)) in
                      let* _ = add_cmd (Cmd.Goto join_block) in
                      return ())
               in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let uadd_overflow_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    let open Gillian.Gil_syntax.Expr in
    match exprs with
    | [ x; y ] ->
        let width = List.hd shape.args in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in

        let add_expr =
          Expr.BVExprIntrinsic
            (BVOps.BVPlus, [ BvExpr (x, width); BvExpr (y, width) ], Some width)
        in
        let max_val = bv_z (Z.pred (Z.shift_left Z.one width)) width in

        (* Check if x + y would overflow by checking if x > max_val - y *)
        let max_minus_y =
          Expr.BVExprIntrinsic
            ( BVOps.BVSub,
              [ BvExpr (max_val, width); BvExpr (y, width) ],
              Some width )
        in
        let bexpr =
          Expr.BVExprIntrinsic
            ( BVOps.BVUlt,
              [ BvExpr (max_minus_y, width); BvExpr (x, width) ],
              None )
        in
        let* _ =
          ite bexpr
            ~true_case:
              (* Overflow *)
              (let one = Expr.Lit (Literal.LBitvector (Z.of_int 1, 1)) in
               let concat_shape =
                 { args = [ width; 1 ]; width_of_result = Some (width + 1) }
               in
               let result =
                 OpFunctions.bv_op_function BVOps.BVConcat [ add_expr; one ]
                   concat_shape
               in
               let* _ = add_cmd (Cmd.Assignment (bindr, result)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
            ~false_case:
              (* No overflow *)
              (let zero = Expr.zero_bv 1 in
               let concat_shape =
                 { args = [ width; 1 ]; width_of_result = Some (width + 1) }
               in
               let result =
                 OpFunctions.bv_op_function BVOps.BVConcat [ add_expr; zero ]
                   concat_shape
               in
               let* _ = add_cmd (Cmd.Assignment (bindr, result)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let usub_overflow_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    match exprs with
    | [ x; y ] ->
        let width = List.hd shape.args in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in
        let bexpr =
          Expr.BVExprIntrinsic
            (BVOps.BVUleq, [ BvExpr (x, width); BvExpr (y, width) ], None)
        in
        let sub_expr =
          Expr.BVExprIntrinsic
            (BVOps.BVSub, [ BvExpr (x, width); BvExpr (y, width) ], Some width)
        in
        let* _ =
          ite bexpr
            ~true_case:
              (* Overflow *)
              (let one = Expr.Lit (Literal.LBitvector (Z.of_int 1, 1)) in
               let concat_shape =
                 { args = [ width; 1 ]; width_of_result = Some (width + 1) }
               in
               let result =
                 OpFunctions.bv_op_function BVOps.BVConcat [ sub_expr; one ]
                   concat_shape
               in
               let* _ = add_cmd (Cmd.Assignment (bindr, result)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
            ~false_case:
              (* No overflow *)
              (let zero = Expr.zero_bv 1 in
               let concat_shape =
                 { args = [ width; 1 ]; width_of_result = Some (width + 1) }
               in
               let result =
                 OpFunctions.bv_op_function BVOps.BVConcat [ sub_expr; zero ]
                   concat_shape
               in
               let* _ = add_cmd (Cmd.Assignment (bindr, result)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let sadd_overflow_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    let open Gillian.Gil_syntax.Expr in
    match exprs with
    | [ x; y ] ->
        let width = List.hd shape.args in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in

        let add_expr =
          Expr.BVExprIntrinsic
            (BVOps.BVPlus, [ BvExpr (x, width); BvExpr (y, width) ], Some width)
        in
        let max_val = bv_z (Z.pred (Z.shift_left Z.one (width - 1))) width in
        let min_val = bv_z (Z.shift_left Z.one (width - 1)) width in
        let zero = Expr.zero_bv width in

        (* Check if y is positive *)
        let y_check =
          Expr.BVExprIntrinsic
            (BVOps.BVSlt, [ BvExpr (zero, width); BvExpr (y, width) ], None)
        in
        let* _ =
          ite y_check
            ~true_case:
              ((* Check if x + y would overflow by checking if x > max_val - y *)
               let max_minus_y =
                 Expr.BVExprIntrinsic
                   ( BVOps.BVSub,
                     [ BvExpr (max_val, width); BvExpr (y, width) ],
                     Some width )
               in
               let x_check =
                 Expr.BVExprIntrinsic
                   ( BVOps.BVSlt,
                     [ BvExpr (max_minus_y, width); BvExpr (x, width) ],
                     None )
               in
               let* _ =
                 ite x_check
                   ~true_case:
                     (* Overflow *)
                     (let one = Expr.Lit (Literal.LBitvector (Z.of_int 1, 1)) in
                      let concat_shape =
                        {
                          args = [ width; 1 ];
                          width_of_result = Some (width + 1);
                        }
                      in
                      let result =
                        OpFunctions.bv_op_function BVOps.BVConcat
                          [ add_expr; one ] concat_shape
                      in
                      let* _ = add_cmd (Cmd.Assignment (bindr, result)) in
                      let* _ = add_cmd (Cmd.Goto join_block) in
                      return ())
                   ~false_case:
                     (* No overflow *)
                     (let zero = Expr.zero_bv 1 in
                      let concat_shape =
                        {
                          args = [ width; 1 ];
                          width_of_result = Some (width + 1);
                        }
                      in
                      let result =
                        OpFunctions.bv_op_function BVOps.BVConcat
                          [ add_expr; zero ] concat_shape
                      in
                      let* _ = add_cmd (Cmd.Assignment (bindr, result)) in
                      let* _ = add_cmd (Cmd.Goto join_block) in
                      return ())
               in
               return ())
            ~false_case:
              ((* Check if x + y would underflow by checking if x < min_val - y *)
               let min_minus_y =
                 Expr.BVExprIntrinsic
                   ( BVOps.BVSub,
                     [ BvExpr (min_val, width); BvExpr (y, width) ],
                     Some width )
               in
               let x_check =
                 Expr.BVExprIntrinsic
                   ( BVOps.BVSlt,
                     [ BvExpr (x, width); BvExpr (min_minus_y, width) ],
                     None )
               in
               let* _ =
                 ite x_check
                   ~true_case:
                     (* Overflow *)
                     (let one = Expr.Lit (Literal.LBitvector (Z.of_int 1, 1)) in
                      let concat_shape =
                        {
                          args = [ width; 1 ];
                          width_of_result = Some (width + 1);
                        }
                      in
                      let result =
                        OpFunctions.bv_op_function BVOps.BVConcat
                          [ add_expr; one ] concat_shape
                      in
                      let* _ = add_cmd (Cmd.Assignment (bindr, result)) in
                      let* _ = add_cmd (Cmd.Goto join_block) in
                      return ())
                   ~false_case:
                     (* No overflow *)
                     (let zero = Expr.zero_bv 1 in
                      let concat_shape =
                        {
                          args = [ width; 1 ];
                          width_of_result = Some (width + 1);
                        }
                      in
                      let result =
                        OpFunctions.bv_op_function BVOps.BVConcat
                          [ add_expr; zero ] concat_shape
                      in
                      let* _ = add_cmd (Cmd.Assignment (bindr, result)) in
                      let* _ = add_cmd (Cmd.Goto join_block) in
                      return ())
               in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let umul_overflow_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    let open Gillian.Gil_syntax.Expr in
    match exprs with
    | [ x; y ] ->
        let width = List.hd shape.args in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in

        let mul_expr =
          Expr.BVExprIntrinsic
            (BVOps.BVMul, [ BvExpr (x, width); BvExpr (y, width) ], Some width)
        in
        let max_val = bv_z (Z.pred (Z.shift_left Z.one width)) width in

        (* Check if x * y would overflow by checking if y > 0 && x > max_val / y *)
        let zero_val = Expr.zero_bv width in
        let y_pos =
          Expr.BVExprIntrinsic
            (BVOps.BVUlt, [ BvExpr (zero_val, width); BvExpr (y, width) ], None)
        in
        let max_div_y =
          Expr.BVExprIntrinsic
            ( BVOps.BVUDiv,
              [ BvExpr (max_val, width); BvExpr (y, width) ],
              Some width )
        in
        let max_div_y_lt_x =
          Expr.BVExprIntrinsic
            (BVOps.BVUlt, [ BvExpr (max_div_y, width); BvExpr (x, width) ], None)
        in
        let* _ =
          ite y_pos
            ~true_case:
              (* Overflow *)
              (let* _ =
                 ite max_div_y_lt_x
                   ~true_case:
                     (* Overflow *)
                     (let one = Expr.Lit (Literal.LBitvector (Z.of_int 1, 1)) in
                      let concat_shape =
                        {
                          args = [ width; 1 ];
                          width_of_result = Some (width + 1);
                        }
                      in
                      let result =
                        OpFunctions.bv_op_function BVOps.BVConcat
                          [ mul_expr; one ] concat_shape
                      in
                      let* _ = add_cmd (Cmd.Assignment (bindr, result)) in
                      let* _ = add_cmd (Cmd.Goto join_block) in
                      return ())
                   ~false_case:
                     (* No overflow*)
                     (let zero = Expr.zero_bv 1 in
                      let concat_shape =
                        {
                          args = [ width; 1 ];
                          width_of_result = Some (width + 1);
                        }
                      in
                      let result =
                        OpFunctions.bv_op_function BVOps.BVConcat
                          [ mul_expr; zero ] concat_shape
                      in
                      let* _ = add_cmd (Cmd.Assignment (bindr, result)) in
                      let* _ = add_cmd (Cmd.Goto join_block) in
                      return ())
               in
               return ())
            ~false_case:
              (* No overflow *)
              (let zero = Expr.zero_bv 1 in
               let concat_shape =
                 { args = [ width; 1 ]; width_of_result = Some (width + 1) }
               in
               let result =
                 OpFunctions.bv_op_function BVOps.BVConcat [ mul_expr; zero ]
                   concat_shape
               in
               let* _ = add_cmd (Cmd.Assignment (bindr, result)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let smul_overflow_function (exprs : Expr.t list) (shape : bv_op_shape) :
      Expr.t Codegenerator.t =
    let open Codegenerator in
    let open Gillian.Gil_syntax.Expr in
    match exprs with
    | [ x; y ] ->
        let width = List.hd shape.args in
        let bindr = fresh_sym () in
        let join_block = fresh_sym () in

        let mul_expr =
          Expr.BVExprIntrinsic
            (BVOps.BVMul, [ BvExpr (x, width); BvExpr (y, width) ], Some width)
        in

        let sext_lits = Some [ 1 ] in
        let mul_sext =
          OpFunctions.bv_op_function ?literals:sext_lits BVOps.BVSignExtend
            [ mul_expr ]
            { shape with args = [ width ] }
        in

        let x_sext =
          OpFunctions.bv_op_function ?literals:sext_lits BVOps.BVSignExtend
            [ x ]
            { shape with args = [ width ] }
        in
        let y_sext =
          OpFunctions.bv_op_function ?literals:sext_lits BVOps.BVSignExtend
            [ y ]
            { shape with args = [ width ] }
        in
        let mul_expr2 =
          Expr.BVExprIntrinsic
            ( BVOps.BVMul,
              [ BvExpr (x_sext, width + 1); BvExpr (y_sext, width + 1) ],
              Some (width + 1) )
        in

        let bexpr = Expr.BinOp (mul_sext, BinOp.Equal, mul_expr2) in

        let* _ =
          ite bexpr
            ~true_case:
              (* No overflow *)
              (let zero = Expr.zero_bv 1 in
               let concat_shape =
                 { args = [ width; 1 ]; width_of_result = Some (width + 1) }
               in
               let result =
                 OpFunctions.bv_op_function BVOps.BVConcat [ mul_expr; zero ]
                   concat_shape
               in
               let* _ = add_cmd (Cmd.Assignment (bindr, result)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
            ~false_case:
              (* Overflow *)
              (let one = Expr.Lit (Literal.LBitvector (Z.of_int 1, 1)) in
               let concat_shape =
                 { args = [ width; 1 ]; width_of_result = Some (width + 1) }
               in
               let result =
                 OpFunctions.bv_op_function BVOps.BVConcat [ mul_expr; one ]
                   concat_shape
               in
               let* _ = add_cmd (Cmd.Assignment (bindr, result)) in
               let* _ = add_cmd (Cmd.Goto join_block) in
               return ())
        in
        let* _ = new_block join_block in
        return (Expr.PVar bindr)
    | _ -> failwith "Invalid number of arguments"

  let generic_template_function
      ~(op : generalized_bv_op_function)
      ~(pointer_width : int)
      ~(flag_checks : bv_op_function list option)
      (name : string)
      (shape : bv_op_shape) =
    op_function name (List.length shape.args) (fun exp_list ->
        generalized_op_bv_scheme exp_list op flag_checks shape)
end

(* Custom template function for cmpxchg that treats the first argument as a pointer *)
let cmpxchg_template_function
    ~(pointer_width : int)
    ~(flag_checks : bv_op_function list option)
    (name : string)
    (shape : bv_op_shape) =
  (* For cmpxchg, we override the normal template behavior to treat the first argument as a pointer *)
  op_function name (List.length shape.args) (fun exp_list ->
      match exp_list with
      | [ ptr; y; z ] ->
          let open Codegenerator in
          let value_width = List.nth shape.args 1 in
          let result_width = value_width + 1 in
          let open Gil_syntax.Expr in
          let open Gil_syntax.Expr.Infix in
          (* Custom type checking for cmpxchg: first arg is Ptr, others are Int *)
          let ptr_type_check = is_type_of_expr ptr LLVMRuntimeTypes.Ptr in
          let y_type_check =
            is_type_of_expr y (LLVMRuntimeTypes.Int value_width)
          in
          let z_type_check =
            is_type_of_expr z (LLVMRuntimeTypes.Int value_width)
          in
          let check = ptr_type_check && y_type_check && z_type_check in
          let result_type = Expr.string ("i-" ^ string_of_int result_width) in
          let* _ =
            ite check
              ~true_case:
                (* Create a corrected shape for cmpxchg_op where the first argument is the pointer width *)
                (let corrected_shape =
                   { shape with args = pointer_width :: List.tl shape.args }
                 in
                 (* Extract bitvectors from typed values *)
                 let y_bv = Expr.list_nth y 1 in
                 let z_bv = Expr.list_nth z 1 in
                 (* Call cmpxchg_op with raw bitvectors *)
                 let* res_bv = cmpxchg_op [ ptr; y_bv; z_bv ] corrected_shape in
                 (* Wrap result in typed structure *)
                 let res = Expr.EList [ result_type; res_bv ] in
                 let* _ = add_return_of_value res in
                 return get_current_block_label)
              ~false_case:
                (let* _ =
                   add_cmd
                     (type_fail
                        [
                          (ptr, LLVMRuntimeTypes.Ptr);
                          (y, LLVMRuntimeTypes.Int value_width);
                          (z, LLVMRuntimeTypes.Int value_width);
                        ])
                 in
                 let* _ = add_cmd Gil_syntax.Cmd.ReturnNormal in
                 return get_current_block_label)
          in
          return ()
      | _ -> failwith "cmpxchg requires exactly 3 arguments")

module LLVMTemplates : Monomorphizer.OpTemplates = struct
  open Monomorphizer
  open Monomorphizer.Template

  let flag_template_function
      (f :
        pointer_width:int ->
        flag_checks:bv_op_function list option ->
        string ->
        bv_op_shape ->
        basic_proc)
      (ops : (flags * bv_op_function) list) :
      flags:flags list ->
      pointer_width:int ->
      string ->
      bv_op_shape ->
      basic_proc =
    let new_f ~flags ~pointer_width name shape =
      let module S = Set.Make (Template.Flags) in
      let target_set = S.of_list flags in
      let checks =
        List.filter (fun (flags, _) -> S.mem flags target_set) ops
        |> List.map (fun (_, op) -> op)
      in
      let checks_or_opt = if List.is_empty checks then None else Some checks in
      f ~flag_checks:checks_or_opt ~pointer_width name shape
    in
    new_f

  let dep_funcs = [ Libc.libc_dependencies ]

  let dependencies ~pointer_width =
    List.map (fun dep -> dep ~pointer_width) dep_funcs |> List.flatten

  let template_operations =
    [
      UtilityOps.is_true_op;
      {
        name = "bvabs";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.abs_op_function)
               []);
      };
      {
        name = "bvumin";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.umin_op_function)
               []);
      };
      {
        name = "bvumax";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.umax_op_function)
               []);
      };
      {
        name = "bvsmin";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.smin_op_function)
               []);
      };
      {
        name = "bvsmax";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.smax_op_function)
               []);
      };
      {
        name = "select";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.select_op_function)
               []);
      };
      {
        name = "create_symbolic_int";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.create_symbolic_int_function)
               []);
      };
      {
        name = "create_symbolic_float";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.create_symbolic_float_function)
               []);
      };
      {
        name = "create_symbolic_ptr";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.create_symbolic_ptr_function)
               []);
      };
      {
        name = "extractvalue";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:OpFunctions.extract_value_function)
               []);
      };
      {
        name = "usubsat";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.usubsat_op_function)
               []);
      };
      {
        name = "uaddsat";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.uaddsat_op_function)
               []);
      };
      {
        name = "ssubsat";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.ssubsat_op_function)
               []);
      };
      {
        name = "saddsat";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.saddsat_op_function)
               []);
      };
      {
        name = "uadd_overflow";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.uadd_overflow_function)
               []);
      };
      {
        name = "usub_overflow";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.usub_overflow_function)
               []);
      };
      {
        name = "sadd_overflow";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.sadd_overflow_function)
               []);
      };
      {
        name = "umul_overflow";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.umul_overflow_function)
               []);
      };
      {
        name = "smul_overflow";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:UtilityOps.smul_overflow_function)
               []);
      };
      {
        name = "bvmul";
        generator =
          ValueOp
            (flag_template_function
               (template_from_integer_op ~op:OpFunctions.mul_op_function)
               [
                 (NoSignedWrap, OpFunctions.mul_op_nsw);
                 (NoUnsignedWrap, OpFunctions.mul_op_nuw);
               ]);
      };
      {
        name = "bvand";
        generator =
          ValueOp
            (flag_template_function
               (template_from_integer_op ~op:OpFunctions.and_op_function)
               []);
      };
      {
        name = "bvshl";
        generator =
          ValueOp
            (flag_template_function
               (template_from_integer_op ~op:OpFunctions.shl_op_function)
               []);
      };
      {
        name = "bvlshr";
        generator =
          ValueOp
            (flag_template_function
               (template_from_integer_op ~op:OpFunctions.lshr_op_function)
               []);
      };
      {
        name = "bvashr";
        generator =
          ValueOp
            (flag_template_function
               (template_from_integer_op ~op:OpFunctions.ashr_op_function)
               []);
      };
      {
        name = "bvor";
        generator =
          ValueOp
            (flag_template_function
               (template_from_integer_op ~op:OpFunctions.or_op_function)
               []);
      };
      {
        name = "bvxor";
        generator =
          ValueOp
            (flag_template_function
               (template_from_integer_op ~op:OpFunctions.xor_op_function)
               []);
      };
      {
        name = "bvsdiv";
        generator =
          ValueOp
            (flag_template_function
               (template_from_integer_op ~op:OpFunctions.sdiv_op_function)
               []);
      };
      {
        name = "bvsrem";
        generator =
          ValueOp
            (flag_template_function
               (template_from_integer_op ~op:OpFunctions.srem_op_function)
               []);
      };
      {
        name = "bvadd";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern ~op:OpFunctions.add_op_function
                  ~commutative:true)
               [
                 (NoSignedWrap, OpFunctions.add_op_nsw);
                 (NoUnsignedWrap, OpFunctions.add_op_nuw);
               ]);
      };
      {
        name = "bvsub";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern ~op:OpFunctions.sub_function
                  ~commutative:false)
               [
                 (NoSignedWrap, OpFunctions.sub_function_overflow BVOps.BVSAddO);
                 ( NoUnsignedWrap,
                   OpFunctions.sub_function_overflow BVOps.BVUAddO );
               ]);
      };
      {
        name = "bvzext";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_unary ~op:OpFunctions.zext_function)
               []);
      };
      {
        name = "bvsext";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_unary ~op:OpFunctions.sext_function)
               []);
      };
      {
        name = "bvtrunc";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_unary ~op:OpFunctions.trunc_function)
               []);
      };
      {
        name = "thread_local_addr";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_unary
                  ~op:OpFunctions.thread_local_addr_function)
               []);
      };
      {
        name = "bvfshl";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:OpFunctions.fshl_function)
               []);
      };
      {
        name = "bvfshr";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:OpFunctions.fshr_function)
               []);
      };
      {
        name = "bswap";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:OpFunctions.bswap_function)
               []);
      };
      {
        name = "ctpop";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:OpFunctions.ctpop_function)
               []);
      };
      {
        name = "cttz";
        generator =
          ValueOp
            (flag_template_function
               (UtilityOps.generic_template_function
                  ~op:OpFunctions.cttz_function)
               []);
      };
      {
        name = "cmpxchg";
        generator =
          ValueOp (flag_template_function cmpxchg_template_function []);
      };
      {
        name = "sitofp";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_conversion_generalized
                  ~op:OpFunctions.sitofp_function)
               []);
      };
      {
        name = "uitofp";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_conversion ~op:OpFunctions.uitofp_function)
               []);
      };
      {
        name = "fptosi";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_conversion ~op:OpFunctions.fptosi_function)
               []);
      };
      {
        name = "fptoui";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_conversion_generalized
                  ~op:OpFunctions.fptoui_function)
               []);
      };
      {
        (* TODO: Use a template that performs correct type checking *)
        name = "bitcast_fp_to_bv";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_conversion
                  ~op:OpFunctions.bitcast_fp_to_bv_function)
               []);
      };
      {
        (* TODO: Use a template that performs correct type checking *)
        name = "bitcast_bv_to_fp";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_conversion
                  ~op:OpFunctions.bitcast_bv_to_fp_function)
               []);
      };
      {
        name = "fpadd";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_fp ~op:OpFunctions.fp_add_function)
               []);
      };
      {
        name = "fpsub";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_fp ~op:OpFunctions.fp_sub_function)
               []);
      };
      {
        name = "fpmul";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_fp ~op:OpFunctions.fp_mul_function)
               []);
      };
      {
        name = "fpdiv";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_fp ~op:OpFunctions.fp_div_function)
               []);
      };
      {
        name = "fpabs";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_fp_unary ~op:OpFunctions.fp_abs_function)
               []);
      };
      {
        name = "fpneg";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_fp_unary ~op:OpFunctions.fp_neg_function)
               []);
      };
      {
        name = "fpceil";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_fp_unary ~op:OpFunctions.fp_ceil_function)
               []);
      };
      {
        name = "fpfloor";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_fp_unary ~op:OpFunctions.fp_floor_function)
               []);
      };
      {
        name = "fptrunc";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_fp_unary ~op:OpFunctions.fp_trunc_function)
               []);
      };
      {
        name = "fpmuladd";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_fp_ternary
                  ~op1:OpFunctions.fp_mul_function
                  ~op2:OpFunctions.fp_add_function)
               []);
      };
      {
        name = "fpext";
        generator =
          ValueOp (flag_template_function template_from_pattern_fp_ext []);
      };
      {
        name = "icmp_eq";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.icmp_eq)
               []);
      };
      {
        name = "icmp_ne";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.icmp_ne)
               []);
      };
      {
        name = "icmp_ugt";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.icmp_ugt)
               []);
      };
      {
        name = "icmp_uge";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.icmp_uge)
               []);
      };
      {
        name = "icmp_ult";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.icmp_ult)
               []);
      };
      {
        name = "icmp_ule";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.icmp_ule)
               []);
      };
      {
        name = "icmp_sgt";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.icmp_sgt)
               []);
      };
      {
        name = "icmp_sge";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.icmp_sge)
               []);
      };
      {
        name = "icmp_slt";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.icmp_slt)
               []);
      };
      {
        name = "icmp_sle";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.icmp_sle)
               []);
      };
      {
        name = "fcmp_false";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_false)
               []);
      };
      {
        name = "fcmp_oeq";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_oeq)
               []);
      };
      {
        name = "fcmp_ogt";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_ogt)
               []);
      };
      {
        name = "fcmp_oge";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_oge)
               []);
      };
      {
        name = "fcmp_olt";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_olt)
               []);
      };
      {
        name = "fcmp_ole";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_ole)
               []);
      };
      {
        name = "fcmp_one";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_one)
               []);
      };
      {
        name = "fcmp_ord";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_ord)
               []);
      };
      {
        name = "fcmp_uno";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_uno)
               []);
      };
      {
        name = "fcmp_ueq";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_ueq)
               []);
      };
      {
        name = "fcmp_ugt";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_ugt)
               []);
      };
      {
        name = "fcmp_uge";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_uge)
               []);
      };
      {
        name = "fcmp_ult";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_ult)
               []);
      };
      {
        name = "fcmp_ule";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_ule)
               []);
      };
      {
        name = "fcmp_une";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_une)
               []);
      };
      {
        name = "fcmp_true";
        generator =
          ValueOp
            (flag_template_function
               (template_from_pattern_cmp ~op:OpFunctions.fcmp_true)
               []);
      };
    ]
    @ MemoryLib.ops @ Libc.libc_ops
end
