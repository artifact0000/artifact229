open Arch_decl
open Eqtype
open Fintype
open Flag_combination
open Seq
open Utils0
open Wsize

val x86_reg_size : wsize

val x86_xreg_size : wsize

type register =
| RAX
| RCX
| RDX
| RBX
| RSP
| RBP
| RSI
| RDI
| R8
| R9
| R10
| R11
| R12
| R13
| R14
| R15

type register_ext =
| MM0
| MM1
| MM2
| MM3
| MM4
| MM5
| MM6
| MM7

type xmm_register =
| XMM0
| XMM1
| XMM2
| XMM3
| XMM4
| XMM5
| XMM6
| XMM7
| XMM8
| XMM9
| XMM10
| XMM11
| XMM12
| XMM13
| XMM14
| XMM15

type rflag =
| CF
| PF
| ZF
| SF
| OF

type condt =
| O_ct
| NO_ct
| B_ct
| NB_ct
| E_ct
| NE_ct
| BE_ct
| NBE_ct
| S_ct
| NS_ct
| P_ct
| NP_ct
| L_ct
| NL_ct
| LE_ct
| NLE_ct

val register_beq : register -> register -> bool

val register_eq_dec : register -> register -> bool

val reg_eq_axiom : register Equality.axiom

val reg_eqMixin : register Equality.mixin_of

val reg_eqType : Equality.coq_type

val register_ext_beq : register_ext -> register_ext -> bool

val register_ext_eq_dec : register_ext -> register_ext -> bool

val regx_eq_axiom : register_ext Equality.axiom

val regx_eqMixin : register_ext Equality.mixin_of

val regx_eqType : Equality.coq_type

val xmm_register_beq : xmm_register -> xmm_register -> bool

val xmm_register_eq_dec : xmm_register -> xmm_register -> bool

val xreg_eq_axiom : xmm_register Equality.axiom

val xreg_eqMixin : xmm_register Equality.mixin_of

val xreg_eqType : Equality.coq_type

val rflag_beq : rflag -> rflag -> bool

val rflag_eq_dec : rflag -> rflag -> bool

val rflag_eq_axiom : rflag Equality.axiom

val rflag_eqMixin : rflag Equality.mixin_of

val rflag_eqType : Equality.coq_type

val condt_beq : condt -> condt -> bool

val condt_eq_dec : condt -> condt -> bool

val condt_eq_axiom : condt Equality.axiom

val condt_eqMixin : condt Equality.mixin_of

val condt_eqType : Equality.coq_type

val registers : register list

val reg_choiceMixin : Equality.sort Choice.Choice.mixin_of

val reg_choiceType : Choice.Choice.coq_type

val reg_countMixin : Equality.sort Choice.Countable.mixin_of

val reg_countType : Choice.Countable.coq_type

val reg_finMixin : Finite.mixin_of

val reg_finType : Finite.coq_type

val regxs : register_ext list

val regx_choiceMixin : Equality.sort Choice.Choice.mixin_of

val regx_choiceType : Choice.Choice.coq_type

val regx_countMixin : Equality.sort Choice.Countable.mixin_of

val regx_countType : Choice.Countable.coq_type

val regx_finMixin : Finite.mixin_of

val regx_finType : Finite.coq_type

val xmm_registers : xmm_register list

val xreg_choiceMixin : Equality.sort Choice.Choice.mixin_of

val xreg_choiceType : Choice.Choice.coq_type

val xreg_countMixin : Equality.sort Choice.Countable.mixin_of

val xreg_countType : Choice.Countable.coq_type

val xreg_finMixin : Finite.mixin_of

val xreg_finType : Finite.coq_type

val rflags : rflag list

val rflag_choiceMixin : Equality.sort Choice.Choice.mixin_of

val rflag_choiceType : Choice.Choice.coq_type

val rflag_countMixin : Equality.sort Choice.Countable.mixin_of

val rflag_countType : Choice.Countable.coq_type

val rflag_finMixin : Finite.mixin_of

val rflag_finType : Finite.coq_type

val eqTC_register : register eqTypeC

val finC_register : register finTypeC

val register_to_string : register -> char list

val x86_reg_toS : register coq_ToString

val eqTC_regx : register_ext eqTypeC

val finC_regx : register_ext finTypeC

val regx_to_string : register_ext -> char list

val x86_regx_toS : register_ext coq_ToString

val eqTC_xmm_register : xmm_register eqTypeC

val finC_xmm_register : xmm_register finTypeC

val xreg_to_string : xmm_register -> char list

val x86_xreg_toS : xmm_register coq_ToString

val eqTC_rflag : rflag eqTypeC

val finC_rflag : rflag finTypeC

val rflag_to_string : rflag -> char list

val x86_rflag_toS : rflag coq_ToString

val eqC_condt : condt eqTypeC

val x86_fc_of_cfc : combine_flags_core -> flag_combination

val x86_fcp : coq_FlagCombinationParams

val x86_decl : (register, register_ext, xmm_register, rflag, condt) arch_decl

val x86_linux_call_conv :
  (register, register_ext, xmm_register, rflag, condt) calling_convention

val x86_windows_call_conv :
  (register, register_ext, xmm_register, rflag, condt) calling_convention
