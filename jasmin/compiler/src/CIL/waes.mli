open BinNums
open Datatypes
open Seq
open Ssralg
open Ssrnat
open Word0
open Word
open Wsize

val coq_Sbox : GRing.ComRing.sort -> GRing.ComRing.sort

val coq_InvSbox : GRing.ComRing.sort -> GRing.ComRing.sort

val coq_SubWord : GRing.ComRing.sort -> GRing.ComRing.sort

val coq_InvSubWord : GRing.ComRing.sort -> GRing.ComRing.sort

val coq_RotWord : GRing.ComRing.sort -> GRing.ComRing.sort

val to_matrix :
  GRing.ComRing.sort ->
  ((((((((((((((word * word) * word) * word) * word) * word) * word) * word) * word) * word) * word) * word) * word) * word) * word) * word

val to_state :
  (((((((((((((((GRing.ComRing.sort * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort) * GRing.ComRing.sort)
  -> GRing.ComRing.sort

val coq_SubBytes : GRing.ComRing.sort -> GRing.ComRing.sort

val coq_InvSubBytes : GRing.ComRing.sort -> GRing.ComRing.sort

val coq_ShiftRows : GRing.ComRing.sort -> GRing.ComRing.sort

val coq_InvShiftRows : GRing.ComRing.sort -> GRing.ComRing.sort

val coq_MixColumns : GRing.ComRing.sort -> GRing.ComRing.sort

val coq_InvMixColumns : GRing.ComRing.sort -> GRing.ComRing.sort

val wAESDEC : GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort

val wAESDECLAST :
  GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort

val wAESENC : GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort

val wAESENCLAST :
  GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort

val wAESKEYGENASSIST :
  GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
