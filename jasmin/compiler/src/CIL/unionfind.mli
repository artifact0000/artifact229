open Datatypes
open Eqtype
open Seq
open Utils0

module type EqType =
 sig
  val coq_T : Equality.coq_type
 end

module NaiveUnionFind :
 functor (E:EqType) ->
 sig
  val coq_S : Equality.coq_type

  type unionfind_r = (Equality.sort * Equality.sort) list

  val is_labeled : Equality.sort -> (Equality.sort * 'a1) -> bool

  val is_pair :
    Equality.coq_type -> (Equality.sort * Equality.sort) ->
    (Equality.sort * Equality.sort) -> bool

  val makeset : unionfind_r -> Equality.sort -> unionfind_r

  val empty_r : unionfind_r

  val find_r : unionfind_r -> Equality.sort -> Equality.sort

  val union_r :
    unionfind_r -> Equality.sort -> Equality.sort ->
    (Equality.sort * Equality.sort) list

  type unionfind_i =
    (Equality.sort * Equality.sort) list
    (* singleton inductive, whose constructor was mkUF *)

  val uf : unionfind_i -> (Equality.sort * Equality.sort) list

  type unionfind = unionfind_i

  val empty : unionfind

  val union : unionfind -> Equality.sort -> Equality.sort -> unionfind

  val find : unionfind -> Equality.sort -> Equality.sort
 end

module LblEqType :
 sig
  val coq_T : Equality.coq_type
 end

module LUF :
 sig
  val coq_S : Equality.coq_type

  type unionfind_r = (Equality.sort * Equality.sort) list

  val is_labeled : Equality.sort -> (Equality.sort * 'a1) -> bool

  val is_pair :
    Equality.coq_type -> (Equality.sort * Equality.sort) ->
    (Equality.sort * Equality.sort) -> bool

  val makeset : unionfind_r -> Equality.sort -> unionfind_r

  val empty_r : unionfind_r

  val find_r : unionfind_r -> Equality.sort -> Equality.sort

  val union_r :
    unionfind_r -> Equality.sort -> Equality.sort ->
    (Equality.sort * Equality.sort) list

  type unionfind_i =
    (Equality.sort * Equality.sort) list
    (* singleton inductive, whose constructor was mkUF *)

  val uf : unionfind_i -> (Equality.sort * Equality.sort) list

  type unionfind = unionfind_i

  val empty : unionfind

  val union : unionfind -> Equality.sort -> Equality.sort -> unionfind

  val find : unionfind -> Equality.sort -> Equality.sort
 end
