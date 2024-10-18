open Datatypes
open Eqtype
open Seq
open Utils0

module type EqType =
 sig
  val coq_T : Equality.coq_type
 end

module NaiveUnionFind =
 functor (E:EqType) ->
 struct
  (** val coq_S : Equality.coq_type **)

  let coq_S =
    E.coq_T

  type unionfind_r = (Equality.sort * Equality.sort) list

  (** val is_labeled : Equality.sort -> (Equality.sort * 'a1) -> bool **)

  let is_labeled l pl =
    eq_op coq_S l (fst pl)

  (** val is_pair :
      Equality.coq_type -> (Equality.sort * Equality.sort) ->
      (Equality.sort * Equality.sort) -> bool **)

  let is_pair t pl1 pl2 =
    (&&) (eq_op coq_S (fst pl1) (fst pl2)) (eq_op t (snd pl1) (snd pl2))

  (** val makeset : unionfind_r -> Equality.sort -> unionfind_r **)

  let makeset uf0 l =
    if has (is_labeled l) uf0 then uf0 else (l, l) :: uf0

  (** val empty_r : unionfind_r **)

  let empty_r =
    []

  (** val find_r : unionfind_r -> Equality.sort -> Equality.sort **)

  let find_r uf0 l =
    snd (nth (l, l) uf0 (find (is_labeled l) uf0))

  (** val union_r :
      unionfind_r -> Equality.sort -> Equality.sort ->
      (Equality.sort * Equality.sort) list **)

  let union_r uf0 lx ly =
    let ufx = makeset uf0 lx in
    let ufxy = makeset ufx ly in
    let fx = find_r ufxy lx in
    let fy = find_r ufxy ly in
    map (fun pl -> ((fst pl),
      (if eq_op coq_S fx (snd pl) then fy else snd pl))) ufxy

  type unionfind_i =
    (Equality.sort * Equality.sort) list
    (* singleton inductive, whose constructor was mkUF *)

  (** val uf : unionfind_i -> (Equality.sort * Equality.sort) list **)

  let uf u =
    u

  type unionfind = unionfind_i

  (** val empty : unionfind **)

  let empty =
    empty_r

  (** val union : unionfind -> Equality.sort -> Equality.sort -> unionfind **)

  let union uf0 x y =
    union_r (uf uf0) x y

  (** val find : unionfind -> Equality.sort -> Equality.sort **)

  let find uf0 x =
    find_r (uf uf0) x
 end

module LblEqType =
 struct
  (** val coq_T : Equality.coq_type **)

  let coq_T =
    Equality.clone pos_eqType (Obj.magic pos_eqMixin) (fun x -> x)
 end

module LUF = NaiveUnionFind(LblEqType)
