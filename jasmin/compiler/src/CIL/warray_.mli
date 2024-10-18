open BinInt
open BinNums
open BinPos
open Bool
open Datatypes
open Eqtype
open Gen_map
open Memory_model
open Seq
open Ssralg
open Ssrbool
open Ssrfun
open Ssrnat
open Utils0
open Word0
open Word_ssrZ
open Wsize

type arr_access =
| AAdirect
| AAscale

val arr_access_beq : arr_access -> arr_access -> bool

val arr_access_eq_dec : arr_access -> arr_access -> bool

val arr_access_eq_axiom : arr_access Equality.axiom

val arr_access_eqMixin : arr_access Equality.mixin_of

val arr_access_eqType : Equality.coq_type

val arr_size : wsize -> positive -> coq_Z

val mk_scale : arr_access -> wsize -> coq_Z

module WArray :
 sig
  type array =
    GRing.ComRing.sort Mz.t
    (* singleton inductive, whose constructor was Build_array *)

  val arr_data : positive -> array -> GRing.ComRing.sort Mz.t

  val empty : positive -> array

  val coq_PointerZ : pointer_op

  val in_bound : positive -> array -> coq_Z -> bool

  val in_boundP : positive -> array -> coq_Z -> reflect

  val is_init : positive -> array -> Equality.sort -> bool

  val get8 :
    positive -> array -> Equality.sort -> (error, GRing.Zmodule.sort) result

  val set8 :
    positive -> array -> Equality.sort -> GRing.ComRing.sort -> (error,
    array) result

  val valid8P :
    positive -> array -> Equality.sort -> GRing.ComRing.sort -> reflect

  val array_CM : positive -> array coreMem

  val in_range : positive -> Equality.sort -> wsize -> bool

  val in_rangeP : positive -> coq_Z -> wsize -> reflect

  val get :
    positive -> arr_access -> wsize -> array -> coq_Z -> GRing.ComRing.sort
    exec

  val set :
    positive -> wsize -> array -> arr_access -> coq_Z -> GRing.ComRing.sort
    -> array exec

  val fcopy :
    wsize -> positive -> array -> array -> coq_Z -> coq_Z -> (error, array)
    result

  val copy : wsize -> positive -> array -> (error, array) result

  val fill : positive -> GRing.ComRing.sort list -> array exec

  val get_sub_data :
    arr_access -> wsize -> positive -> GRing.ComRing.sort Mz.t -> coq_Z ->
    GRing.ComRing.sort Mz.t

  val get_sub :
    positive -> arr_access -> wsize -> positive -> array -> coq_Z -> array
    exec

  val set_sub_data :
    arr_access -> wsize -> positive -> GRing.ComRing.sort Mz.t -> coq_Z ->
    GRing.ComRing.sort Mz.t -> GRing.ComRing.sort Mz.t

  val set_sub :
    positive -> arr_access -> wsize -> positive -> array -> coq_Z -> array ->
    array exec

  val cast : positive -> positive -> array -> (error, array) result

  val of_list : wsize -> GRing.ComRing.sort list -> array
 end
