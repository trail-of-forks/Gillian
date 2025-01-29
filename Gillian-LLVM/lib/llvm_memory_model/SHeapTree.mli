open Gil_syntax
open Gillian.Utils.Containers
open Monadic
open SVal

type err =
  | UseAfterFree
  | BufferOverrun
  | InsufficientPermission of { required : Perm.t; actual : Perm.t }
  | InvalidAlignment of { alignment : int; offset : Expr.t }
  | MissingResource
  | Unhandled of string
  | WrongMemVal
  | MemoryNotFreed
  | LoadingPoison
[@@deriving yojson]

val pp_err : err Fmt.t
val err_equal : err -> err -> bool

type 'a or_error = ('a, err) Result.t
type 'a d_or_error = ('a, err) Delayed_result.t

module Range : sig
  type t = Expr.t * Expr.t

  val of_low_chunk_and_size : Expr.t -> Chunk.t -> Expr.t -> t
end

type t [@@deriving yojson]

val pp : t Fmt.t
val pp_full : t Fmt.t
val empty : t
val is_empty : t -> bool
val is_concrete : t -> bool
val lvars : t -> SS.t
val alocs : t -> SS.t
val load_bounds : t -> Range.t or_error
val cons_bounds : t -> (Range.t * t) or_error
val prod_bounds : t -> Range.t -> t or_error

val cons_single :
  t -> Expr.t -> Chunk.t -> (SVal.t * Perm.t option * t) d_or_error

val prod_single : t -> Expr.t -> Chunk.t -> SVal.t -> Perm.t -> t d_or_error

val get_array :
  t -> Expr.t -> Expr.t -> Chunk.t -> (SVArray.t * Perm.t option * t) d_or_error

val cons_array :
  t -> Expr.t -> Expr.t -> Chunk.t -> (SVArray.t * Perm.t option * t) d_or_error

val prod_array :
  t -> Expr.t -> Expr.t -> Chunk.t -> SVArray.t -> Perm.t -> t d_or_error

val instantiate : Expr.t -> Expr.t -> t
val cons_hole : t -> Expr.t -> Expr.t -> (t * Perm.t option) d_or_error
val prod_hole : t -> Expr.t -> Expr.t -> Perm.t -> t d_or_error
val cons_zeros : t -> Expr.t -> Expr.t -> (t * Perm.t option) d_or_error
val prod_zeros : t -> Expr.t -> Expr.t -> Perm.t -> t d_or_error
val alloc : Expr.t -> Expr.t -> t
val store : t -> Chunk.t -> Expr.t -> SVal.t -> t d_or_error
val poison : t -> Expr.t -> Expr.t -> t d_or_error
val zero_init : t -> Expr.t -> Expr.t -> t d_or_error
val load : t -> Chunk.t -> Expr.t -> (SVal.t * t) d_or_error
val is_exclusively_owned : t -> Expr.t -> Expr.t -> bool Delayed.t
val drop_perm : t -> Expr.t -> Expr.t -> Perm.t -> t d_or_error
val get_perm_at : t -> Expr.t -> Perm.t option d_or_error
val weak_valid_pointer : t -> Expr.t -> bool d_or_error

(** [move dst_tree dst_ofs src_tree src_ofs size] moves [size] bytes from
    [src_tree] at [src_ofs] into [dst_tree] at [dst_ofs] and returns the new
    [dst_tree] after modification *)
val move : t -> Expr.t -> t -> Expr.t -> Expr.t -> t d_or_error

val assertions : t -> (LActions.ga * Expr.t list * Expr.t list) list
val assertions_others : t -> Asrt.atom list

val substitution :
  le_subst:(Expr.t -> Expr.t) ->
  sval_subst:(SVal.t -> SVal.t) ->
  svarr_subst:(SVArray.t -> SVArray.t) ->
  t ->
  t

val merge : old_tree:t -> new_tree:t -> t d_or_error

module Lift : sig
  open Gillian.Debugger.Utils

  val get_variable :
    make_node:
      (name:string ->
      value:string ->
      ?children:Variable.t list ->
      unit ->
      Variable.t) ->
    loc:string ->
    t ->
    Variable.t
end
