open Gil_syntax
open Utils
open Simple_smt
open Syntaxes.Option

(* open Ctx *)
module L = Logging

let z3_config =
  [
    ("model", "true");
    ("proof", "false");
    ("unsat_core", "false");
    ("auto_config", "true");
    ("timeout", "30000");
  ]

let solver = new_solver z3
let cmd s = ack_command solver s
let () = z3_config |> List.iter (fun (k, v) -> cmd (set_option (":" ^ k) v))

exception SMT_unknown

let pp_sexp = Sexplib.Sexp.pp_hum
let init_decls : sexp list ref = ref []
let builtin_funcs : sexp list ref = ref []
let defined_bv_variants : int list ref = ref []

let sanitize_identifier =
  let pattern = Str.regexp "#" in
  Str.global_replace pattern "$$"

let is_true = function
  | Sexplib.Sexp.Atom "true" -> true
  | _ -> false

type typenv = (string, Type.t) Hashtbl.t

let pp_typenv = Fmt.(Dump.hashtbl string (Fmt.of_to_string Type.str))

let encoding_cache : (Expr.Set.t, sexp list) Hashtbl.t =
  Hashtbl.create Config.big_tbl_size

let sat_cache : (Expr.Set.t, sexp option) Hashtbl.t =
  Hashtbl.create Config.big_tbl_size

let ( <| ) constr e = app constr [ e ]
let ( $$ ) constr l = app constr l
let declare_const const typ = atom "declare-const" $$ [ atom const; typ ]

let quant q (vars : (sexp * sexp) list) (s : sexp) : sexp =
  let vars = vars |> List.map (fun (v, t) -> list [ v; t ]) in
  app (atom q) [ list vars; s ]

let forall' = quant "forall"

let forall (vars : (string * sexp) list) (s : sexp) : sexp =
  let vars =
    vars |> List.map (fun (v, t) -> (atom (sanitize_identifier v), t))
  in
  forall' vars s

let exists' = quant "exists"

let exists (vars : (string * sexp) list) (s : sexp) : sexp =
  let vars =
    vars |> List.map (fun (v, t) -> (atom (sanitize_identifier v), t))
  in
  exists' vars s

let t_seq t = list [ atom "Seq"; t ]
let seq_len s = atom "seq.len" <| s
let seq_extract s offset length = atom "seq.extract" $$ [ s; offset; length ]
let seq_nth s offset = atom "seq.nth" $$ [ s; offset ]
let seq_concat ss = atom "seq.++" $$ ss
let seq_unit s = atom "seq.unit" <| s

let set_union' ext xs =
  let f =
    match ext with
    | CVC5 -> atom "set.union"
    | _ -> atom "union"
  in
  f $$ xs

let set_intersection' ext xs =
  let f =
    match ext with
    | CVC5 -> atom "set.inter"
    | _ -> atom "intersection"
  in
  f $$ xs

module Variant = struct
  module type S = sig
    val name : string
    val params : (string * sexp) list
    val recognizer : string
    val recognize : sexp -> sexp
  end

  module type Nullary = sig
    include S

    val construct : sexp
  end

  module type Unary = sig
    include S

    val construct : sexp -> sexp
    val access : sexp -> sexp
  end

  let nul ?recognizer name =
    let recognizer = Option.value recognizer ~default:("is" ^ name) in
    let module M = struct
      let name = name
      let params = []
      let construct = atom name $$ []
      let recognizer = recognizer
      let recognize x = atom recognizer <| x
    end in
    (module M : Nullary)

  let un ?recognizer name param param_typ =
    let module N = (val nul ?recognizer name : Nullary) in
    let module M = struct
      include N

      let params = [ (param, param_typ) ]
      let construct x = atom name <| x
      let accessor = atom param
      let access x = accessor <| x
    end in
    (module M : Unary)
end

let declare_recognizer ~name ~constructor ~typ =
  define_fun name
    [ ("x", typ) ]
    t_bool
    (list [ atom "_"; atom "is"; atom constructor ] <| atom "x")

let create_datatype name type_params (variants : (module Variant.S) list) =
  let constructors, recognizer_defs =
    variants
    |> List.map (fun v ->
           let module V = (val v : Variant.S) in
           let constructor = (V.name, V.params) in
           let recognizer_def =
             declare_recognizer ~name:V.recognizer ~constructor:V.name
               ~typ:(atom name)
           in
           (constructor, recognizer_def))
    |> List.split
  in
  let decl = declare_datatype name type_params constructors in
  (decl, recognizer_defs)

let mk_datatype name type_params (variants : (module Variant.S) list) =
  let decl, recognizer_defs = create_datatype name type_params variants in
  let () = init_decls := recognizer_defs @ (decl :: !init_decls) in
  atom name

let mk_fun_decl name param_types result_type =
  let decl = declare_fun name param_types result_type in
  let () = builtin_funcs := decl :: !builtin_funcs in
  atom name

module Type_operations = struct
  open Variant
  module Undefined = (val nul "UndefinedType" : Nullary)
  module Null = (val nul "NullType" : Nullary)
  module Empty = (val nul "EmptyType" : Nullary)
  module None = (val nul "NoneType" : Nullary)
  module Boolean = (val nul "BooleanType" : Nullary)
  module Int = (val nul "IntType" : Nullary)
  module Number = (val nul "NumberType" : Nullary)
  module String = (val nul "StringType" : Nullary)
  module Object = (val nul "ObjectType" : Nullary)
  module List = (val nul "ListType" : Nullary)
  module Type = (val nul "TypeType" : Nullary)
  module Set = (val nul "SetType" : Nullary)
  module Bv = (val un "BvType" "bvWidth" t_int : Unary)

  let t_gil_type =
    mk_datatype "GIL_Type" []
      [
        (module Undefined : Variant.S);
        (module Null : Variant.S);
        (module Empty : Variant.S);
        (module None : Variant.S);
        (module Boolean : Variant.S);
        (module Int : Variant.S);
        (module Number : Variant.S);
        (module String : Variant.S);
        (module Object : Variant.S);
        (module List : Variant.S);
        (module Type : Variant.S);
        (module Set : Variant.S);
        (module Bv : Variant.S);
      ]
end

let t_gil_type = Type_operations.t_gil_type

module BvLiteral = struct
  let lit_name = "GIL_BVLiteral"
  let t_lit_name = atom lit_name
  let name (width : int) = Printf.sprintf "Bv_%d" width
  let accessor (width : int) = Printf.sprintf "bv_under_value_%d" width

  let make_mod (width : int) =
    Variant.un (name width) (accessor width) (t_bits width)

  let decl_data_type _ =
    let mods =
      List.map
        (fun x ->
          let module S = (val make_mod x) in
          (module S : Variant.S))
        (!defined_bv_variants |> List.sort_uniq Int.compare)
    in
    let mods_with_nop_constructor =
      let module M = (val Variant.nul "BVNoop") in
      (module M : Variant.S) :: mods
    in

    create_datatype lit_name [] mods_with_nop_constructor
end

module Lit_operations = struct
  open Variant

  let gil_literal_name = "GIL_Literal"
  let t_gil_literal = atom gil_literal_name

  module Undefined = (val nul "Undefined" : Nullary)
  module Null = (val nul "Null" : Nullary)
  module Empty = (val nul "Empty" : Nullary)
  module Bool = (val un "Bool" "bValue" t_bool : Unary)
  module Int = (val un "Int" "iValue" t_int : Unary)
  module Num = (val un "Num" "nValue" t_real : Unary)
  module String = (val un "String" "sValue" t_int : Unary)
  module Loc = (val un "Loc" "locValue" t_int : Unary)
  module Type = (val un "Type" "tValue" t_gil_type : Unary)
  module List = (val un "List" "listValue" (t_seq t_gil_literal) : Unary)
  module Bv = (val un "Bv" "bv_value" BvLiteral.t_lit_name : Unary)
  module None = (val nul "None" : Nullary)

  let _ =
    mk_datatype gil_literal_name []
      [
        (module Undefined : Variant.S);
        (module Null : Variant.S);
        (module Empty : Variant.S);
        (module Bool : Variant.S);
        (module Int : Variant.S);
        (module Num : Variant.S);
        (module String : Variant.S);
        (module Loc : Variant.S);
        (module Type : Variant.S);
        (module List : Variant.S);
        (module None : Variant.S);
        (module Bv : Variant.S);
      ]
end

let t_gil_literal = Lit_operations.t_gil_literal
let t_gil_literal_list = t_seq t_gil_literal
let t_gil_literal_set = t_set t_gil_literal

let seq_of ~typ = function
  | [] -> as_type (atom "seq.empty") typ
  | xs -> xs |> List.map seq_unit |> seq_concat

let set_of xs =
  let rec aux acc = function
    | [] -> acc
    | x :: xs -> aux (set_insert Z3 x acc) xs
  in
  aux (set_empty Z3 t_gil_literal) xs

module Ext_lit_operations = struct
  open Variant

  module Gil_sing_elem =
    (val un "Elem" ~recognizer:"isSingular" "singElem" t_gil_literal : Unary)

  module Gil_set = (val un "Set" "setElem" t_gil_literal_set : Unary)

  let t_gil_ext_literal =
    mk_datatype "Extended_GIL_Literal" []
      [ (module Gil_sing_elem : Variant.S); (module Gil_set : Variant.S) ]
end

module Axiomatised_operations = struct
  let slen = mk_fun_decl "s-len" [ t_int ] t_real
  let llen = mk_fun_decl "l-len" [ t_gil_literal_list ] t_int
  let num2str = mk_fun_decl "num2str" [ t_real ] t_int
  let str2num = mk_fun_decl "str2num" [ t_int ] t_real
  let num2int = mk_fun_decl "num2int" [ t_real ] t_real
  let snth = mk_fun_decl "s-nth" [ t_int; t_real ] t_int
  let lrev = mk_fun_decl "l-rev" [ t_gil_literal_list ] t_gil_literal_list
end

let t_gil_ext_literal = Ext_lit_operations.t_gil_ext_literal
let str_codes = Hashtbl.create 1000
let str_codes_inv = Hashtbl.create 1000
let str_counter = ref 0

(** We only check for string equality; each unique string is assigned a code,
    and the solver can check for equality by checking equality of the codes. *)
let encode_string s =
  match Hashtbl.find_opt str_codes s with
  | Some code -> int_k code
  | None ->
      let code = int_k !str_counter in
      let () = Hashtbl.add str_codes s !str_counter in
      let () = Hashtbl.add str_codes_inv !str_counter s in
      let () = incr str_counter in
      code

let encode_type (t : Type.t) =
  try
    match t with
    | UndefinedType -> Type_operations.Undefined.construct
    | NullType -> Type_operations.Null.construct
    | EmptyType -> Type_operations.Empty.construct
    | NoneType -> Type_operations.None.construct
    | BooleanType -> Type_operations.Boolean.construct
    | IntType -> Type_operations.Int.construct
    | NumberType -> Type_operations.Number.construct
    | StringType -> Type_operations.String.construct
    | ObjectType -> Type_operations.Object.construct
    | ListType -> Type_operations.List.construct
    | TypeType -> Type_operations.Type.construct
    | SetType -> Type_operations.Set.construct
    | BvType w -> Type_operations.Bv.construct (nat_k w)
  with _ -> Fmt.failwith "DEATH: encode_type with arg: %a" Type.pp t

module Encoding = struct
  type kind =
    | Native of Type.t
        (** This value encodes to an SMTLIB native type, like Int or Seq *)
    | Simple_wrapped  (** Cannot be a set *)
    | Extended_wrapped  (** Can be a set *)

  let native_sort_of_type =
    let open Type in
    function
    | IntType | StringType | ObjectType -> t_int
    | ListType -> t_gil_literal_list
    | BooleanType -> t_bool
    | NumberType -> t_real
    | UndefinedType | NoneType | EmptyType | NullType -> t_gil_literal
    | SetType -> t_gil_literal_set
    | TypeType -> t_gil_type
    | BvType width -> t_bits width

  type t = {
    consts : (string * sexp) Hashset.t; [@default Hashset.empty ()]
    kind : kind;
    extra_asrts : sexp list;
    expr : sexp; [@main]
  }
  [@@deriving make]

  let merge_consts a b =
    let result = Hashset.copy a in
    let () = b |> Hashset.iter (Hashset.add result) in
    result

  let all_consts encs =
    List.fold_left
      (fun acc enc -> merge_consts acc enc.consts)
      (Hashset.empty ()) encs

  let undefined_encoding =
    make ~kind:Simple_wrapped Lit_operations.Undefined.construct

  let null_encoding = make ~kind:Simple_wrapped Lit_operations.Null.construct
  let empty_encoding = make ~kind:Simple_wrapped Lit_operations.Empty.construct
  let none_encoding = make ~kind:Simple_wrapped Lit_operations.None.construct

  let native typ =
    (match typ with
    | Type.BvType width -> defined_bv_variants := width :: !defined_bv_variants
    | _ -> ());
    make ~kind:(Native typ)

  let make_const ?extra_asrts ~typ kind const =
    let const = sanitize_identifier const in
    let consts = Hashtbl.singleton (const, typ) () in
    make ?extra_asrts ~consts ~kind (atom const)

  let native_const ?extra_asrts typ =
    make_const ?extra_asrts ~typ:(native_sort_of_type typ) (Native typ)

  let ( >- ) expr typ = native typ expr

  let ( let>- ) (enc : t) (f : t -> t) =
    let enc' = f enc in
    let consts = merge_consts enc.consts enc'.consts in
    let extra_asrts = enc.extra_asrts @ enc'.extra_asrts in
    { enc' with consts; extra_asrts }

  let ( let>-- ) (encs : t list) (f : t list -> t) =
    let enc' = f encs in
    let consts = merge_consts (all_consts encs) enc'.consts in
    let extra_asrts =
      List.concat_map (fun e -> e.extra_asrts) encs @ enc'.extra_asrts
    in
    { enc' with consts; extra_asrts }

  let get_native ~accessor { expr; kind; _ } =
    (* No additional check is performed on native type,
       it should be already type checked *)
    match kind with
    | Native _ -> expr
    | Simple_wrapped -> accessor expr
    | Extended_wrapped ->
        accessor (Ext_lit_operations.Gil_sing_elem.access expr)

  let simply_wrapped = make ~kind:Simple_wrapped

  (** Takes a value either natively encoded or simply wrapped
    and returns a value simply wrapped.
    Careful: do not use wrap with a a set, as they cannot be simply wrapped *)
  let simple_wrap { expr; kind; _ } =
    let open Lit_operations in
    match kind with
    | Simple_wrapped -> expr
    | Native typ ->
        let construct =
          match typ with
          | IntType -> Int.construct
          | NumberType -> Num.construct
          | StringType -> String.construct
          | ObjectType -> Loc.construct
          | TypeType -> Type.construct
          | BooleanType -> Bool.construct
          | ListType -> List.construct
          | BvType w ->
              let module M = (val BvLiteral.make_mod w) in
              M.construct
          | UndefinedType | NullType | EmptyType | NoneType | SetType ->
              Fmt.failwith "Cannot simple-wrap value of type %s"
                (Gil_syntax.Type.str typ)
        in
        construct expr
    | Extended_wrapped -> Ext_lit_operations.Gil_sing_elem.access expr

  let extend_wrap e =
    match e.kind with
    | Extended_wrapped -> e.expr
    | Native SetType -> Ext_lit_operations.Gil_set.construct (simple_wrap e)
    | _ -> Ext_lit_operations.Gil_sing_elem.construct (simple_wrap e)

  let get_num = get_native ~accessor:Lit_operations.Num.access
  let get_int = get_native ~accessor:Lit_operations.Int.access
  let get_bool = get_native ~accessor:Lit_operations.Bool.access
  let get_list = get_native ~accessor:Lit_operations.List.access

  let get_bv (width : int) (e : t) : sexp =
    get_native
      ~accessor:(fun x ->
        let m = BvLiteral.make_mod width in
        let module M = (val m : Variant.Unary) in
        Lit_operations.Bv.access x |> M.access)
      e

  let get_set { kind; expr; _ } =
    match kind with
    | Native SetType -> expr
    | Extended_wrapped -> Ext_lit_operations.Gil_set.access expr
    | _ -> failwith "wrong encoding of set"

  let get_string = get_native ~accessor:Lit_operations.String.access
end

let typeof_simple e =
  let open Type in
  let guards =
    Lit_operations.
      [
        (Null.recognize, NullType);
        (Empty.recognize, EmptyType);
        (Undefined.recognize, UndefinedType);
        (None.recognize, NoneType);
        (Bool.recognize, BooleanType);
        (Int.recognize, IntType);
        (Num.recognize, NumberType);
        (String.recognize, StringType);
        (Loc.recognize, ObjectType);
        (Type.recognize, TypeType);
        (List.recognize, ListType);
      ]
  in
  List.fold_left
    (fun acc (guard, typ) -> ite (guard e) (encode_type typ) acc)
    (encode_type UndefinedType)
    guards

let typeof_extended e =
  let open Ext_lit_operations in
  let guard = Gil_set.recognize e in
  let typeof_simple = e |> Gil_sing_elem.access |> typeof_simple in
  ite guard (encode_type SetType) typeof_simple

let typeof_expression ({ kind; expr; _ } : Encoding.t) =
  match kind with
  | Native typ -> encode_type typ
  | Simple_wrapped -> typeof_simple expr
  | Extended_wrapped -> typeof_extended expr

module RepeatCache = struct
  let cache : (sexp * sexp, Encoding.t) Hashtbl.t = Hashtbl.create 0
  let var_counter = ref 0
  let make_var counter = "__repeat_var_" ^ string_of_int counter

  let next_var () =
    let ret = !var_counter in
    let () = incr var_counter in
    make_var ret

  let clear_var_counter () = var_counter := 0
  let index = atom "__index__"

  let clear () =
    let () = Hashtbl.clear cache in
    clear_var_counter ()

  let get_constraints var x n =
    let at_index_is_x = eq (seq_nth var index) x in
    let length = seq_len var in
    let all_eq_x = forall' [ (index, t_int) ] at_index_is_x in
    let length_is_n = eq length n in
    [ all_eq_x; length_is_n ]

  let get x n : Encoding.t =
    let- () = Hashtbl.find_opt cache (x, n) in
    let var = next_var () in
    let e = atom var in
    let extra_asrts = get_constraints e x n in
    let () = Hashtbl.add cache (x, n) (Encoding.native ListType e) in
    Encoding.native_const ~extra_asrts ListType var
end

let rec encode_lit (lit : Literal.t) : Encoding.t =
  let open Encoding in
  try
    match lit with
    | Undefined -> undefined_encoding
    | Null -> null_encoding
    | Empty -> empty_encoding
    | Nono -> none_encoding
    | Bool b -> bool_k b >- BooleanType
    | Int i -> int_zk i >- IntType
    | Num n -> real_k (Q.of_float n) >- NumberType
    | String s -> encode_string s >- StringType
    | Loc l -> encode_string l >- ObjectType
    | LBitvector (v, w) -> bv_k w v >- BvType w
    | Type t -> encode_type t >- TypeType
    | LList lits ->
        let args = List.map (fun lit -> simple_wrap (encode_lit lit)) lits in
        list args >- ListType
    | Constant _ -> raise (Exceptions.Unsupported "Z3 encoding: constants")
  with Failure msg ->
    Fmt.failwith "DEATH: encode_lit %a. %s" Literal.pp lit msg

let encode_equality (p1 : Encoding.t) (p2 : Encoding.t) : Encoding.t =
  let open Encoding in
  let>- _ = p1 in
  let>- _ = p2 in
  let res =
    match (p1.kind, p2.kind) with
    | Native t1, Native t2 when Type.equal t1 t2 ->
        if Type.equal t1 BooleanType then
          if is_true p1.expr then p2.expr
          else if is_true p2.expr then p1.expr
          else eq p1.expr p2.expr
        else eq p1.expr p2.expr
    | Simple_wrapped, Simple_wrapped | Extended_wrapped, Extended_wrapped ->
        eq p1.expr p2.expr
    | Native _, Native _ -> failwith "incompatible equality, type error!"
    | Simple_wrapped, Native _ | Native _, Simple_wrapped ->
        eq (simple_wrap p1) (simple_wrap p2)
    | Extended_wrapped, _ | _, Extended_wrapped ->
        eq (extend_wrap p1) (extend_wrap p2)
  in
  res >- BooleanType

let encode_binop (op : BinOp.t) (p1 : Encoding.t) (p2 : Encoding.t) : Encoding.t
    =
  let open Encoding in
  let>- _ = p1 in
  let>- _ = p2 in
  (* In the case of strongly typed operations, we do not perform any check.
     Type checking has happened before reaching z3, and therefore, isn't required here again.
     An unknown type is represented by the [None] variant of the option type.
     It is expected that values of unknown type are already wrapped into their constructors.
  *)
  match op with
  | IPlus -> num_add (get_int p1) (get_int p2) >- IntType
  | IMinus -> num_sub (get_int p1) (get_int p2) >- IntType
  | ITimes -> num_mul (get_int p1) (get_int p2) >- IntType
  | IDiv -> num_div (get_int p1) (get_int p2) >- IntType
  | IMod -> num_mod (get_int p1) (get_int p2) >- IntType
  | ILessThan -> num_lt (get_int p1) (get_int p2) >- BooleanType
  | ILessThanEqual -> num_leq (get_int p1) (get_int p2) >- BooleanType
  | FPlus -> num_add (get_num p1) (get_num p2) >- NumberType
  | FMinus -> num_sub (get_num p1) (get_num p2) >- NumberType
  | FTimes -> num_mul (get_num p1) (get_num p2) >- NumberType
  | FDiv -> num_div (get_num p1) (get_num p2) >- NumberType
  | FLessThan -> num_lt (get_num p1) (get_num p2) >- BooleanType
  | FLessThanEqual -> num_leq (get_num p1) (get_num p2) >- BooleanType
  | Equal -> encode_equality p1 p2
  | Or -> bool_or (get_bool p1) (get_bool p2) >- BooleanType
  | Impl -> bool_implies (get_bool p1) (get_bool p2) >- BooleanType
  | And -> bool_and (get_bool p1) (get_bool p2) >- BooleanType
  | SetMem ->
      (* p2 has to be already wrapped *)
      set_member Z3 (simple_wrap p1) (get_set p2) >- BooleanType
  | SetDiff -> set_difference Z3 (get_set p1) (get_set p2) >- SetType
  | SetSub -> set_subset Z3 (get_set p1) (get_set p2) >- BooleanType
  | LstNth -> seq_nth (get_list p1) (get_int p2) |> simply_wrapped
  | LstRepeat ->
      let x = simple_wrap p1 in
      let n = get_int p2 in
      RepeatCache.get x n
  | StrNth ->
      let str' = get_string p1 in
      let index' = get_num p2 in
      let res = Axiomatised_operations.snth $$ [ str'; index' ] in
      res >- StringType
  | FMod
  | StrLess
  | BitwiseAnd
  | BitwiseOr
  | BitwiseXor
  | LeftShift
  | SignedRightShift
  | UnsignedRightShift
  | BitwiseAndL
  | BitwiseOrL
  | BitwiseXorL
  | LeftShiftL
  | SignedRightShiftL
  | UnsignedRightShiftL
  | BitwiseAndF
  | BitwiseOrF
  | BitwiseXorF
  | LeftShiftF
  | SignedRightShiftF
  | UnsignedRightShiftF
  | M_atan2
  | M_pow
  | StrCat ->
      Fmt.failwith "SMT encoding: Costruct not supported yet - binop: %s"
        (BinOp.str op)

let encode_unop ~llen_lvars ~e (op : UnOp.t) le =
  let open Encoding in
  let open Axiomatised_operations in
  let>- _ = le in
  match op with
  | IUnaryMinus -> num_neg (get_int le) >- IntType
  | FUnaryMinus -> num_neg (get_num le) >- NumberType
  | LstLen ->
      (* If we only use an LVar as an argument to llen, then encode it as an uninterpreted function. *)
      let enc =
        match e with
        | Expr.LVar l when SS.mem l llen_lvars -> llen <| get_list le
        | _ -> seq_len (get_list le)
      in
      enc >- IntType
  | StrLen -> slen <| get_string le >- NumberType
  | ToStringOp -> Axiomatised_operations.num2str <| get_num le >- StringType
  | ToNumberOp -> Axiomatised_operations.str2num <| get_string le >- NumberType
  | ToIntOp -> Axiomatised_operations.num2int <| get_num le >- NumberType
  | Not -> bool_not (get_bool le) >- BooleanType
  | Cdr ->
      let list = get_list le in
      seq_extract list (int_k 1) (seq_len list) >- ListType
  | Car -> seq_nth (get_list le) (int_k 0) |> simply_wrapped
  | TypeOf -> typeof_expression le >- TypeType
  | ToUint32Op -> get_num le |> real_to_int |> int_to_real >- NumberType
  | LstRev -> Axiomatised_operations.lrev <| get_list le >- ListType
  | NumToInt -> get_num le |> real_to_int >- IntType
  | IntToNum -> get_int le |> int_to_real >- NumberType
  | IsInt -> num_divisible (get_num le) 1 >- BooleanType
  | BitwiseNot
  | M_isNaN
  | M_abs
  | M_acos
  | M_asin
  | M_atan
  | M_ceil
  | M_cos
  | M_exp
  | M_floor
  | M_log
  | M_round
  | M_sgn
  | M_sin
  | M_sqrt
  | M_tan
  | ToUint16Op
  | ToInt32Op
  | SetToList ->
      let msg =
        Fmt.str "SMT encoding: Construct not supported yet - unop - %s!"
          (UnOp.str op)
      in
      let () = L.print_to_all msg in
      raise (Failure msg)

let encode_quantified_expr
    ~(encode_expr :
       gamma:typenv ->
       llen_lvars:SS.t ->
       list_elem_vars:SS.t ->
       'a ->
       Encoding.t)
    ~mk_quant
    ~gamma
    ~llen_lvars
    ~list_elem_vars
    quantified_vars
    (assertion : 'a) : Encoding.t =
  let open Encoding in
  let- () =
    match quantified_vars with
    | [] ->
        (* A quantified assertion with no quantified variables is just the assertion *)
        Some (encode_expr ~gamma ~llen_lvars ~list_elem_vars assertion)
    | _ -> None
  in
  (* Start by updating gamma with the information provided by quantifier types.
     There's very few foralls, so it's ok to copy the gamma entirely *)
  let gamma = Hashtbl.copy gamma in
  let () =
    quantified_vars
    |> List.iter (fun (x, typ) ->
           match typ with
           | None -> Hashtbl.remove gamma x
           | Some typ -> Hashtbl.replace gamma x typ)
  in
  (* Not the same gamma now!*)
  let encoded_assertion, consts, extra_asrts =
    match encode_expr ~gamma ~llen_lvars ~list_elem_vars assertion with
    | { kind = Native BooleanType; expr; consts; extra_asrts } ->
        (expr, consts, extra_asrts)
    | _ -> failwith "the thing inside forall is not boolean!"
  in
  let quantified_vars =
    quantified_vars
    |> List.map (fun (x, t) ->
           let sort =
             match t with
             | None -> t_gil_ext_literal
             | Some typ -> Encoding.native_sort_of_type typ
           in
           (x, sort))
  in
  (* Don't declare consts for quantified vars *)
  let () =
    consts
    |> Hashtbl.filter_map_inplace (fun c () ->
           if List.mem c quantified_vars then None else Some ())
  in
  let expr = mk_quant quantified_vars encoded_assertion in
  native ~consts ~extra_asrts BooleanType expr

let encode_bvop
    (op : BVOps.t)
    (literals : int list)
    (bvs : sexp list)
    (width : int) : Encoding.t =
  let unop_encode (f : sexp -> sexp) = f (List.hd bvs) in
  let binop_encode (f : sexp -> sexp -> sexp) =
    f (List.hd bvs) (List.nth bvs 1)
  in
  let sexpr =
    match op with
    | BVOps.BVNeg -> unop_encode bv_neg
    | BVOps.BVNot -> unop_encode bv_not
    | BVOps.BVPlus -> binop_encode bv_add
    | BVOps.BVAnd -> binop_encode bv_and
    | BVOps.BVOr -> binop_encode bv_or
    | BVOps.BVMul -> binop_encode bv_mul
    | BVOps.BVUDiv -> binop_encode bv_udiv
    | BVOps.BVUrem -> binop_encode bv_urem
    | BVOps.BVShl -> binop_encode bv_shl
    | BVOps.BVLShr -> binop_encode bv_lshr
    | BVConcat -> binop_encode bv_concat
    | BVExtract ->
        bv_extract (List.hd literals) (List.nth literals 1) (List.hd bvs)
    | _ -> raise (Failure ("No encoding for bv op " ^ BVOps.str op))
  in
  Encoding.native (Gil_syntax.Type.BvType width) sexpr

let encode_bv_assertion (op : BVPred.t) (_literals : int list) (bvs : sexp list)
    =
  let binop_encode (f : sexp -> sexp -> sexp) =
    f (List.hd bvs) (List.nth bvs 1)
  in
  let sexpr =
    match op with
    | BVPred.BVUlt -> binop_encode bv_ult
    | _ -> raise (Failure ("No encoding for bv op " ^ BVPred.str op))
  in
  Encoding.native Gil_syntax.Type.BooleanType sexpr

let rec encode_logical_expression
    ~(gamma : typenv)
    ~(llen_lvars : SS.t)
    ~(list_elem_vars : SS.t)
    (le : Expr.t) : Encoding.t =
  let open Encoding in
  let f = encode_logical_expression ~gamma ~llen_lvars ~list_elem_vars in

  match le with
  | Lit lit -> encode_lit lit
  | LVar var ->
      let kind, typ =
        match Hashtbl.find_opt gamma var with
        | Some typ -> (Native typ, native_sort_of_type typ)
        | None ->
            if SS.mem var list_elem_vars then (Simple_wrapped, t_gil_literal)
            else (Extended_wrapped, t_gil_ext_literal)
      in
      make_const ~typ kind var
  | ALoc var -> native_const ObjectType var
  | PVar _ -> failwith "HORROR: Program variable in pure formula"
  | UnOp (op, le) -> encode_unop ~llen_lvars ~e:le op (f le)
  | BinOp (le1, op, le2) -> encode_binop op (f le1) (f le2)
  | BVExprIntrinsic (op, es, width) ->
      let extracted_bvs, extracted_lits = Expr.partition_bvargs es in
      let widths = List.map (fun (_, w) -> w) extracted_bvs in
      let>-- les = List.map (fun (e, _) -> f e) extracted_bvs in
      List.combine les widths |> List.map (fun (encoded, w) -> get_bv w encoded)
      |> fun encodings -> encode_bvop op extracted_lits encodings width
  | NOp (SetUnion, les) ->
      let>-- les = List.map f les in
      les |> List.map get_set |> set_union' Z3 >- SetType
  | NOp (SetInter, les) ->
      let>-- les = List.map f les in
      les |> List.map get_set |> set_intersection' Z3 >- SetType
  | NOp (LstCat, les) ->
      let>-- les = List.map f les in
      les |> List.map get_list |> seq_concat >- ListType
  | EList les ->
      let>-- args = List.map f les in
      args |> List.map simple_wrap |> seq_of ~typ:t_gil_literal_list >- ListType
  | ESet les ->
      let>-- args = List.map f les in
      args |> List.map simple_wrap |> set_of >- SetType
  | LstSub (lst, start, len) ->
      let>- lst = f lst in
      let>- start = f start in
      let>- len = f len in
      let lst = get_list lst in
      let start = get_int start in
      let len = get_int len in
      seq_extract lst start len >- ListType
  | Exists (bt, e) ->
      encode_quantified_expr ~encode_expr:encode_logical_expression
        ~mk_quant:exists ~gamma ~llen_lvars ~list_elem_vars bt e
  | ForAll (bt, e) ->
      encode_quantified_expr ~encode_expr:encode_logical_expression
        ~mk_quant:forall ~gamma ~llen_lvars ~list_elem_vars bt e

and encode_assertion
    ~(gamma : typenv)
    ~(llen_lvars : SS.t)
    ~(list_elem_vars : SS.t)
    (a : Formula.t) : Encoding.t =
  let f = encode_assertion ~gamma ~llen_lvars ~list_elem_vars in
  let fe = encode_logical_expression ~gamma ~llen_lvars ~list_elem_vars in
  let open Encoding in
  match a with
  | Not a ->
      let>- a = f a in
      get_bool a |> bool_not >- BooleanType
  | Eq (le1, le2) -> encode_equality (fe le1) (fe le2)
  | FLess (le1, le2) ->
      let>- le1 = fe le1 in
      let>- le2 = fe le2 in
      num_lt (get_num le1) (get_num le2) >- BooleanType
  | FLessEq (le1, le2) ->
      let>- le1 = fe le1 in
      let>- le2 = fe le2 in
      num_leq (get_num le1) (get_num le2) >- BooleanType
  | ILess (le1, le2) ->
      let>- le1 = fe le1 in
      let>- le2 = fe le2 in
      num_lt (get_int le1) (get_int le2) >- BooleanType
  | ILessEq (le1, le2) ->
      let>- le1 = fe le1 in
      let>- le2 = fe le2 in
      num_leq (get_int le1) (get_int le2) >- BooleanType
  | Impl (a1, a2) ->
      let>- a1 = f a1 in
      let>- a2 = f a2 in
      bool_implies (get_bool a1) (get_bool a2) >- BooleanType
  | StrLess (_, _) -> failwith "SMT encoding does not support STRLESS"
  | True -> bool_k true >- BooleanType
  | False -> bool_k false >- BooleanType
  | Or (a1, a2) ->
      let>- a1 = f a1 in
      let>- a2 = f a2 in
      bool_or (get_bool a1) (get_bool a2) >- BooleanType
  | And (a1, a2) ->
      let>- a1 = f a1 in
      let>- a2 = f a2 in
      bool_and (get_bool a1) (get_bool a2) >- BooleanType
  | SetMem (le1, le2) ->
      let>- le1 = fe le1 in
      let>- le2 = fe le2 in
      set_member Z3 (simple_wrap le1) (get_set le2) >- BooleanType
  | SetSub (le1, le2) ->
      let>- le1 = fe le1 in
      let>- le2 = fe le2 in
      set_subset Z3 (get_set le1) (get_set le2) >- BooleanType
  | ForAll (bt, a) ->
      encode_quantified_expr ~encode_expr:encode_assertion ~mk_quant:forall
        ~gamma ~llen_lvars ~list_elem_vars bt a
  | IsInt e ->
      let>- e = fe e in
      num_divisible (get_num e) 1 >- BooleanType
  | BVFormIntrinsic (op, es) ->
      let extracted_es, extracted_lits = Expr.partition_bvargs es in
      let widths = List.map (fun (_, w) -> w) extracted_es in
      let>-- les = List.map (fun (e, _) -> fe e) extracted_es in
      List.combine les widths |> List.map (fun (encoded, w) -> get_bv w encoded)
      |> fun encodings -> encode_bv_assertion op extracted_lits encodings

let encode_assertion_top_level
    ~(gamma : typenv)
    ~(llen_lvars : SS.t)
    ~(list_elem_vars : SS.t)
    (a : Expr.t) : Encoding.t =
  try
    encode_logical_expression ~gamma ~llen_lvars ~list_elem_vars
      (Expr.push_in_negations a)
  with e ->
    let s = Printexc.to_string e in
    let msg =
      Fmt.str "Failed to encode %a in gamma %a with error %s\n" Expr.pp a
        pp_typenv gamma s
    in
    let () = L.print_to_all msg in
    raise e

let lvars_only_in_llen (fs : Expr.Set.t) : SS.t =
  let inspector =
    object
      inherit [_] Visitors.iter as super
      val mutable llen_vars = SS.empty
      val mutable other_vars = SS.empty
      method get_diff = SS.diff llen_vars other_vars

      method! visit_expr () e =
        match e with
        | UnOp (UnOp.LstLen, Expr.LVar l) -> llen_vars <- SS.add l llen_vars
        | LVar l -> other_vars <- SS.add l other_vars
        | _ -> super#visit_expr () e
    end
  in
  fs |> Expr.Set.iter (inspector#visit_expr ());
  inspector#get_diff

let lvars_as_list_elements (assertions : Expr.Set.t) : SS.t =
  let collector =
    object (self)
      inherit [_] Visitors.reduce
      inherit Visitors.Utils.ss_monoid

      method! visit_ForAll (exclude, is_in_list) binders f =
        (* Quantified variables need to be excluded *)
        let univ_quant = List.to_seq binders |> Seq.map fst in
        let exclude = Containers.SS.add_seq univ_quant exclude in
        self#visit_expr (exclude, is_in_list) f

      method! visit_Exists (exclude, is_in_list) binders e =
        let exist_quants = List.to_seq binders |> Seq.map fst in
        let exclude = Containers.SS.add_seq exist_quants exclude in
        self#visit_expr (exclude, is_in_list) e

      method! visit_EList (exclude, _) es =
        List.fold_left
          (fun acc e ->
            match e with
            | Expr.LVar x ->
                if not (Containers.SS.mem x exclude) then
                  Containers.SS.add x acc
                else acc
            | _ ->
                let inner = self#visit_expr (exclude, true) e in
                Containers.SS.union acc inner)
          Containers.SS.empty es

      method! visit_LVar (exclude, is_in_list) x =
        if is_in_list && not (Containers.SS.mem x exclude) then
          Containers.SS.singleton x
        else Containers.SS.empty

      method! visit_'label _ (_ : int) = self#zero
      method! visit_'annot _ () = self#zero
    end
  in
  Expr.Set.fold
    (fun f acc ->
      let new_lvars = collector#visit_expr (SS.empty, false) f in
      SS.union new_lvars acc)
    assertions SS.empty

let encode_assertions (fs : Expr.Set.t) (gamma : typenv) : sexp list =
  let open Encoding in
  let- () = Hashtbl.find_opt encoding_cache fs in
  let llen_lvars = lvars_only_in_llen fs in
  let list_elem_vars = lvars_as_list_elements fs in
  let encoded =
    Expr.Set.elements fs
    |> List.map (encode_assertion_top_level ~gamma ~llen_lvars ~list_elem_vars)
  in
  let consts =
    Hashtbl.fold
      (fun (const, typ) () acc -> declare_const const typ :: acc)
      (all_consts encoded) []
  in
  let asrts =
    let extra_asrts = List.concat_map (fun e -> e.extra_asrts) encoded in
    let encoded_asrts = List.map (fun e -> e.expr) encoded in
    List.map assume (extra_asrts @ encoded_asrts)
  in
  let encoded = consts @ asrts in
  let () = Hashtbl.replace encoding_cache fs encoded in
  encoded

module Dump = struct
  let counter = ref 0

  let folder =
    let folder_name = "gillian_smt_queries" in
    let created = ref false in
    let create () =
      created := true;
      try Unix.mkdir folder_name 0o755 with
      | Unix.Unix_error (Unix.EEXIST, _, _) -> ()
      | e -> raise e
    in
    fun () ->
      let () = if not !created then create () in
      folder_name

  let file () =
    let ret = Printf.sprintf "query_%d.smt2" !counter in
    let () = incr counter in
    ret

  let to_file f =
    let () = L.verbose (fun m -> m "Dumping query %d to file" !counter) in
    let path = Filename.concat (folder ()) (file ()) in
    let c = open_out path in
    let () = f c in
    let () = close_out c in
    ()

  let dump fs gamma cmds =
    to_file (fun c ->
        Fmt.pf
          (Format.formatter_of_out_channel c)
          "GIL query:\nFS: %a\nGAMMA: %a\nEncoded as SMT Query:\n%a@?"
          (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp)
          fs pp_typenv gamma
          (Fmt.list ~sep:(Fmt.any "\n") Sexplib.Sexp.pp_hum)
          cmds)
end

let reset_solver () =
  let () = cmd (pop 1) in
  let () = RepeatCache.clear () in
  let () = cmd (push 1) in
  ()

let perform_decls _ =
  let bv_decl, bv_recogs = BvLiteral.decl_data_type () in
  let decls = List.rev !init_decls in
  (bv_decl :: bv_recogs) @ decls |> List.iter (fun decl -> cmd decl)

let exec_sat' (fs : Expr.Set.t) (gamma : typenv) : sexp option =
  let () =
    L.verbose (fun m ->
        m "@[<v 2>About to check SAT of:@\n%a@]@\nwith gamma:@\n@[%a@]\n"
          (Fmt.iter ~sep:(Fmt.any "@\n") Expr.Set.iter Expr.pp)
          fs pp_typenv gamma)
  in
  let () = reset_solver () in
  let encoded_assertions = encode_assertions fs gamma in
  let () = perform_decls () in
  let () = if true then Dump.dump fs gamma encoded_assertions in
  let () = List.iter cmd !builtin_funcs in
  let () = List.iter cmd encoded_assertions in
  L.verbose (fun fmt -> fmt "Reached SMT.");
  let result = check solver in
  L.verbose (fun m ->
      let r =
        match result with
        | Sat -> "satisfiable"
        | Unsat -> "unsatisfiable"
        | Unknown -> "unknown"
      in
      m "The solver returned: %s" r);
  let ret =
    match result with
    | Unknown ->
        if !Config.under_approximation then raise SMT_unknown
        else
          let msg =
            Fmt.str
              "FATAL ERROR: SMT returned UNKNOWN for SAT question:\n\
               %a\n\
               with gamma:\n\
               @[%a@]\n\n\n\
               Solver:\n\
               %a\n\
               @?"
              (Fmt.iter ~sep:(Fmt.any ", ") Expr.Set.iter Expr.pp)
              fs pp_typenv gamma
              (Fmt.list ~sep:(Fmt.any "\n\n") Sexplib.Sexp.pp_hum)
              encoded_assertions
          in
          let () = L.print_to_all msg in
          exit 1
    | Sat -> Some (get_model solver)
    | Unsat -> None
  in
  ret

let exec_sat (fs : Expr.Set.t) (gamma : typenv) : sexp option =
  try exec_sat' fs gamma
  with UnexpectedSolverResponse _ as e ->
    let msg =
      Fmt.str "SMT failure!@\n%s@\nExpressions: @\n%a"
        (Printexc.to_string e ^ "\n")
        Fmt.(list ~sep:(Fmt.any "@\n") Expr.pp)
        (Expr.Set.elements fs)
    in
    let () = L.print_to_all msg in
    exit 1

let check_sat (fs : Expr.Set.t) (gamma : typenv) : sexp option =
  match Hashtbl.find_opt sat_cache fs with
  | Some result ->
      let () =
        L.verbose (fun m ->
            m "SAT check cached with result: %b" (Option.is_some result))
      in
      result
  | None ->
      let () = L.verbose (fun m -> m "SAT check not found in cache") in
      let ret = exec_sat fs gamma in
      let () =
        L.verbose (fun m ->
            let f = Expr.conjunct (Expr.Set.elements fs) in
            m "Adding to cache : @[%a@]" Expr.pp f)
      in
      let () = Hashtbl.replace sat_cache fs ret in
      ret

let is_sat (fs : Expr.Set.t) (gamma : typenv) : bool =
  check_sat fs gamma |> Option.is_some

let lift_model
    (model : sexp)
    (gamma : typenv)
    (subst_update : string -> Expr.t -> unit)
    (target_vars : Expr.Set.t) : unit =
  let () = reset_solver () in
  let model_eval = (model_eval' solver model).eval [] in

  let get_val x =
    try
      let x = x |> sanitize_identifier |> atom in
      model_eval x |> Option.some
    with UnexpectedSolverResponse _ -> None
  in

  let recover_number (n : sexp) : float option =
    try Some (to_q n |> Q.to_float) with UnexpectedSolverResponse _ -> None
  in

  let recover_int (n : sexp) : Z.t option =
    try Some (to_z n) with UnexpectedSolverResponse _ -> None
  in

  let lift_val (x : string) : Literal.t option =
    let* gil_type = Hashtbl.find_opt gamma x in
    let* v = get_val x in
    match gil_type with
    | NumberType ->
        let+ n = recover_number v in
        Literal.Num n
    | IntType ->
        let+ n = recover_int v in
        Literal.Int n
    | StringType ->
        let* si = recover_int v in
        let+ str_code = Hashtbl.find_opt str_codes_inv (Z.to_int si) in
        Literal.String str_code
    | _ -> None
  in

  let () = L.verbose (fun m -> m "Inside lift_model") in
  target_vars
  |> Expr.Set.iter (fun x ->
         let x =
           match x with
           | LVar x -> x
           | _ ->
               failwith "INTERNAL ERROR: SMT lifting of a non-logical variable"
         in
         let v = lift_val x in
         let () =
           L.verbose (fun m ->
               let binding =
                 v
                 |> Option.fold
                      ~some:(Fmt.to_to_string Literal.pp)
                      ~none:"NO BINDING!"
               in
               m "SMT binding for %s: %s\n" x binding)
         in
         v |> Option.iter (fun v -> subst_update x (Expr.Lit v)))

let () = cmd (push 1)
