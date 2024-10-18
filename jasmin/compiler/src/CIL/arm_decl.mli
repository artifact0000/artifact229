open BinInt
open BinNums
open Datatypes
open Arch_decl
open Arch_utils
open Eqtype
open Expr
open Fintype
open Flag_combination
open Seq
open Shift_kind
open Ssralg
open Ssrint
open Type
open Utils0
open Word0
open Word_ssrZ
open Wsize

type __ = Obj.t

val arm_reg_size : wsize

val arm_xreg_size : wsize

type register =
| R00
| R01
| R02
| R03
| R04
| R05
| R06
| R07
| R08
| R09
| R10
| R11
| R12
| LR
| SP

val register_beq : register -> register -> bool

val register_eq_dec : register -> register -> bool

val register_eq_axiom : register Equality.axiom

val eqTC_register : register eqTypeC

val arm_register_eqType : Equality.coq_type

val registers : register list

val finTC_register : register finTypeC

val register_finType : Finite.coq_type

val register_to_string : register -> char list

val reg_toS : register coq_ToString

type rflag =
| NF
| ZF
| CF
| VF

val rflag_beq : rflag -> rflag -> bool

val rflag_eq_dec : rflag -> rflag -> bool

val rflag_eq_axiom : rflag Equality.axiom

val eqTC_rflag : rflag eqTypeC

val rflag_eqType : Equality.coq_type

val rflags : rflag list

val finTC_rflag : rflag finTypeC

val rflag_finType : Finite.coq_type

val flag_to_string : rflag -> char list

val rflag_toS : rflag coq_ToString

type condt =
| EQ_ct
| NE_ct
| CS_ct
| CC_ct
| MI_ct
| PL_ct
| VS_ct
| VC_ct
| HI_ct
| LS_ct
| GE_ct
| LT_ct
| GT_ct
| LE_ct

val condt_beq : condt -> condt -> bool

val condt_eq_dec : condt -> condt -> bool

val condt_eq_axiom : condt Equality.axiom

val eqTC_condt : condt eqTypeC

val condt_eqType : Equality.coq_type

val condts : condt list

val finTC_condt : condt finTypeC

val condt_finType : Finite.coq_type

val string_of_condt : condt -> char list

val shift_kind_beq : shift_kind -> shift_kind -> bool

val shift_kind_eq_dec : shift_kind -> shift_kind -> bool

val shift_kind_eq_axiom : shift_kind Equality.axiom

val eqTC_shift_kind : shift_kind eqTypeC

val shift_kind_eqType : Equality.coq_type

val shift_kinds : shift_kind list

val string_of_shift_kind : shift_kind -> char list

val check_shift_amount : shift_kind -> coq_Z -> bool

val shift_op :
  shift_kind -> wsize -> GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort

val shift_of_sop2 : wsize -> sop2 -> shift_kind option

val arm_fc_of_cfc : combine_flags_core -> flag_combination

val arm_fcp : coq_FlagCombinationParams

val arm_decl : (register, __, __, rflag, condt) arch_decl

val arm_linux_call_conv : (register, __, __, rflag, condt) calling_convention

type expand_immediate_kind =
| EI_none
| EI_byte
| EI_pattern
| EI_shift

val z_to_bytes : coq_Z -> ((coq_Z * coq_Z) * coq_Z) * coq_Z

val is_ei_pattern : coq_Z -> bool

val is_ei_shift : coq_Z -> bool

val ei_kind : coq_Z -> expand_immediate_kind

val is_expandable : coq_Z -> bool

val is_expandable_or_shift : coq_Z -> bool

val is_w12_encoding : coq_Z -> bool

val is_w16_encoding : coq_Z -> bool
