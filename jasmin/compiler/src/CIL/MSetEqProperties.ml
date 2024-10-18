open Datatypes
open Equalities
open MSetInterface
open MSetProperties
open Nat0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module WEqPropertiesOn =
 functor (E:DecidableType) ->
 functor (M:sig
  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool
 end) ->
 struct
  module MP = WPropertiesOn(E)(M)

  (** val choose_mem_3 : M.t -> M.elt **)

  let choose_mem_3 s =
    let o = M.choose s in
    (match o with
     | Some e -> e
     | None -> assert false (* absurd case *))

  (** val set_rec :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> (M.t -> M.elt -> __ -> 'a1 -> 'a1)
      -> 'a1 -> M.t -> 'a1 **)

  let set_rec x x0 x1 s =
    MP.set_induction (fun s0 _ -> x M.empty s0 __ x1) (fun s0 s' x2 x3 _ _ ->
      x (M.add x3 s0) s' __ (x0 s0 x3 __ x2)) s

  (** val for_all_mem_4 : (M.elt -> bool) -> M.t -> M.elt **)

  let for_all_mem_4 f s =
    choose_mem_3 (M.filter (fun x -> negb (f x)) s)

  (** val exists_mem_4 : (M.elt -> bool) -> M.t -> M.elt **)

  let exists_mem_4 f s =
    for_all_mem_4 (fun x -> negb (f x)) s

  (** val sum : (M.elt -> nat) -> M.t -> nat **)

  let sum f s =
    M.fold (fun x -> add (f x)) s O
 end

module WEqProperties =
 functor (M:WSets) ->
 WEqPropertiesOn(M.E)(M)

module EqProperties = WEqProperties
