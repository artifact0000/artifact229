open BinInt
open BinNums
open Datatypes
open Div
open Eqtype
open Expr
open Flag_combination
open Sem_type
open Ssralg
open Type
open Utils0
open Word0
open Word_ssrZ
open Wsize

val sem_sop1_typed : sop1 -> sem_t -> sem_t

val zlsl : coq_Z -> coq_Z -> coq_Z

val zasr : coq_Z -> coq_Z -> coq_Z

val sem_shift :
  (wsize -> GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort) -> wsize ->
  GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort

val sem_shr :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort

val sem_sar :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort

val sem_shl :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort

val sem_ror :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort

val sem_rol :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort

val sem_vadd :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  GRing.ComRing.sort

val sem_vsub :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  GRing.ComRing.sort

val sem_vmul :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  GRing.ComRing.sort

val sem_vshr :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  GRing.ComRing.sort

val sem_vsar :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  GRing.ComRing.sort

val sem_vshl :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  GRing.ComRing.sort

val signed : 'a1 -> 'a1 -> signedness -> 'a1

val mk_sem_divmod :
  wsize -> (GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort)
  -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort exec

val mk_sem_sop2 : ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a2 -> 'a3 exec

val sem_sop2_typed : sop2 -> sem_t -> sem_t -> sem_t exec

val sem_combine_flags :
  coq_FlagCombinationParams -> combine_flags -> bool -> bool -> bool -> bool
  -> bool

val sem_opN_typed : coq_FlagCombinationParams -> opN -> sem_t exec sem_prod
