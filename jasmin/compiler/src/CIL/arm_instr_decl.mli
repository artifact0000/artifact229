open BinInt
open BinNums
open Bool
open Datatypes
open PeanoNat
open String0
open Arch_decl
open Arch_utils
open Arm_decl
open Eqtype
open Fintype
open Sem_type
open Seq
open Shift_kind
open Sopn
open Ssralg
open Ssrbool
open Ssrnat
open Type
open Utils0
open Word0
open Word_ssrZ
open Wsize
open Xseq

type __ = Obj.t

module E :
 sig
  val no_semantics : error
 end

type arm_options = { set_flags : bool; is_conditional : bool;
                     has_shift : shift_kind option }

val set_flags : arm_options -> bool

val is_conditional : arm_options -> bool

val has_shift : arm_options -> shift_kind option

val arm_options_beq : arm_options -> arm_options -> bool

val arm_options_eq_axiom : arm_options Equality.axiom

val eqTC_arm_options : arm_options eqTypeC

val arm_options_eqType : Equality.coq_type

val arm_options_dec_eq : arm_options -> arm_options -> bool

val default_opts : arm_options

val set_is_conditional : arm_options -> arm_options

val unset_is_conditional : arm_options -> arm_options

type halfword =
| HWB
| HWT

type arm_mnemonic =
| ADD
| ADC
| MUL
| MLA
| MLS
| SDIV
| SUB
| RSB
| UDIV
| UMULL
| UMAAL
| UMLAL
| SMULL
| SMLAL
| SMMUL
| SMMULR
| SMUL_hw of halfword * halfword
| SMLA_hw of halfword * halfword
| SMULW_hw of halfword
| AND
| BFC
| BFI
| BIC
| EOR
| MVN
| ORR
| ASR
| LSL
| LSR
| ROR
| REV
| REV16
| REVSH
| ADR
| MOV
| MOVT
| UBFX
| UXTB
| UXTH
| SBFX
| CLZ
| CMP
| TST
| CMN
| LDR
| LDRB
| LDRH
| LDRSB
| LDRSH
| STR
| STRB
| STRH

val internal_halfword_beq : halfword -> halfword -> bool

val arm_mnemonic_beq : arm_mnemonic -> arm_mnemonic -> bool

val arm_mnemonic_eq_dec : arm_mnemonic -> arm_mnemonic -> bool

val arm_mnemonic_eq_axiom : arm_mnemonic Equality.axiom

val eqTC_arm_mnemonic : arm_mnemonic eqTypeC

val arm_mnemonic_eqType : Equality.coq_type

val arm_mnemonics : arm_mnemonic list

val finTC_arm_mnemonic : arm_mnemonic finTypeC

val arm_mnemonic_finType : Finite.coq_type

val set_flags_mnemonics : arm_mnemonic list

val has_shift_mnemonics : arm_mnemonic list

val condition_mnemonics : arm_mnemonic list

val always_has_shift_mnemonics : (arm_mnemonic * shift_kind) list

val wsize_uload_mn : (wsize * arm_mnemonic) list

val uload_mn_of_wsize : wsize -> arm_mnemonic option

val wsize_of_uload_mn : arm_mnemonic -> wsize option

val wsize_sload_mn : (wsize * arm_mnemonic) list

val sload_mn_of_wsize : wsize -> arm_mnemonic option

val wsize_of_sload_mn : arm_mnemonic -> wsize option

val wsize_of_load_mn : arm_mnemonic -> wsize option

val wsize_store_mn : (wsize * arm_mnemonic) list

val store_mn_of_wsize : wsize -> arm_mnemonic option

val wsize_of_store_mn : arm_mnemonic -> wsize option

val string_of_hw : halfword -> char list

val string_of_arm_mnemonic : arm_mnemonic -> char list

type arm_op =
| ARM_op of arm_mnemonic * arm_options

val arm_op_beq : arm_op -> arm_op -> bool

val arm_op_eq_axiom : arm_op Equality.axiom

val eqTC_arm_op : arm_op eqTypeC

val arm_op_eqType : Equality.coq_type

val arm_op_dec_eq : arm_op -> arm_op -> bool

val ad_nz : (register, __, __, rflag, condt) Arch_decl.arg_desc list

val ad_nzc : (register, __, __, rflag, condt) Arch_decl.arg_desc list

val ad_nzcv : (register, __, __, rflag, condt) Arch_decl.arg_desc list

val coq_NF_of_word : wsize -> GRing.ComRing.sort -> bool

val coq_ZF_of_word : wsize -> GRing.ComRing.sort -> bool

val nzcv_of_aluop : wsize -> GRing.ComRing.sort -> coq_Z -> coq_Z -> sem_tuple

val nzcv_w_of_aluop : wsize -> GRing.ComRing.sort -> coq_Z -> coq_Z -> ltuple

val drop_nz :
  (register, __, __, rflag, condt) instr_desc_t -> (register, __, __, rflag,
  condt) instr_desc_t

val drop_nzc :
  (register, __, __, rflag, condt) instr_desc_t -> (register, __, __, rflag,
  condt) instr_desc_t

val drop_nzcv :
  (register, __, __, rflag, condt) instr_desc_t -> (register, __, __, rflag,
  condt) instr_desc_t

val mk_semi_cond :
  stype list -> stype list -> sem_tuple exec sem_prod -> sem_tuple exec
  sem_prod

val mk_cond :
  (register, __, __, rflag, condt) instr_desc_t -> (register, __, __, rflag,
  condt) instr_desc_t

val mk_semi1_shifted : shift_kind -> 'a1 exec sem_prod -> 'a1 exec sem_prod

val mk_semi2_2_shifted :
  stype -> shift_kind -> 'a1 exec sem_prod -> 'a1 exec sem_prod

val mk_semi3_2_shifted :
  stype -> stype -> shift_kind -> 'a1 exec sem_prod -> 'a1 exec sem_prod

val mk_shifted :
  shift_kind -> (register, __, __, rflag, condt) instr_desc_t -> sem_tuple
  exec sem_prod -> (register, __, __, rflag, condt) instr_desc_t

val pp_arm_op :
  arm_mnemonic -> arm_options -> (register, __, __, rflag, condt) asm_arg
  list -> (register, __, __, rflag, condt) pp_asm_op

val arm_ADD_semi : sem_tuple -> sem_tuple -> sem_tuple exec

val arm_ADD_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_ADC_semi : sem_tuple -> sem_tuple -> bool -> sem_tuple exec

val arm_ADC_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_MUL_semi : sem_tuple -> sem_tuple -> sem_tuple exec

val arm_MUL_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_MLA_semi : sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple exec

val arm_MLA_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_MLS_semi : sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple exec

val arm_MLS_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_SDIV_semi : sem_tuple -> sem_tuple -> sem_tuple exec

val arm_SDIV_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_SUB_semi : sem_tuple -> sem_tuple -> sem_tuple exec

val arm_SUB_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_RSB_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_UDIV_semi : sem_tuple -> sem_tuple -> sem_tuple exec

val arm_UDIV_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_UMULL_semi : sem_tuple -> sem_tuple -> sem_tuple exec

val arm_UMULL_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_UMAAL_semi :
  sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple exec

val arm_UMAAL_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_UMLAL_semi :
  sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple exec

val arm_UMLAL_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_SMULL_semi : sem_tuple -> sem_tuple -> sem_tuple exec

val arm_SMULL_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_SMLAL_semi :
  sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple exec

val arm_SMLAL_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_SMMUL_semi : sem_tuple -> sem_tuple -> sem_tuple exec

val arm_SMMUL_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_SMMULR_semi : sem_tuple -> sem_tuple -> sem_tuple exec

val arm_SMMULR_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val get_hw :
  halfword -> (register, __, __, rflag, condt) wreg -> GRing.ComRing.sort

val arm_smul_hw_semi :
  halfword -> halfword -> (register, __, __, rflag, condt) wreg -> (register,
  __, __, rflag, condt) wreg -> (register, __, __, rflag, condt) wreg exec

val arm_smul_hw_instr :
  arm_options -> halfword -> halfword -> (register, __, __, rflag, condt)
  instr_desc_t

val arm_smla_hw_semi :
  halfword -> halfword -> (register, __, __, rflag, condt) wreg -> (register,
  __, __, rflag, condt) wreg -> (register, __, __, rflag, condt) wreg ->
  (register, __, __, rflag, condt) wreg exec

val arm_smla_hw_instr :
  arm_options -> halfword -> halfword -> (register, __, __, rflag, condt)
  instr_desc_t

val arm_smulw_hw_semi :
  halfword -> (register, __, __, rflag, condt) wreg -> (register, __, __,
  rflag, condt) wreg -> (register, __, __, rflag, condt) wreg exec

val arm_smulw_hw_instr :
  arm_options -> halfword -> (register, __, __, rflag, condt) instr_desc_t

val arm_bitwise_semi :
  wsize -> (GRing.ComRing.sort -> GRing.ComRing.sort) -> (GRing.ComRing.sort
  -> GRing.ComRing.sort) -> (GRing.ComRing.sort -> GRing.ComRing.sort ->
  GRing.ComRing.sort) -> sem_tuple -> sem_tuple -> sem_tuple exec

val arm_AND_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_BFC_semi :
  (register, __, __, rflag, condt) wreg -> GRing.ComRing.sort ->
  GRing.ComRing.sort -> (register, __, __, rflag, condt) wreg exec

val arm_BFC_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_BFI_semi :
  (register, __, __, rflag, condt) wreg -> (register, __, __, rflag, condt)
  wreg -> GRing.ComRing.sort -> GRing.ComRing.sort -> (register, __, __,
  rflag, condt) wreg exec

val arm_BFI_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_BIC_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_EOR_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_MVN_semi : sem_tuple -> sem_tuple exec

val arm_MVN_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_ORR_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_ASR_semi : sem_tuple -> GRing.ComRing.sort -> sem_tuple exec

val arm_ASR_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_LSL_semi : sem_tuple -> GRing.ComRing.sort -> sem_tuple exec

val arm_LSL_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_LSR_semi : sem_tuple -> GRing.ComRing.sort -> sem_tuple exec

val arm_LSR_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_ROR_semi : sem_tuple -> GRing.ComRing.sort -> sem_tuple exec

val arm_ROR_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val mk_rev_instr :
  arm_options -> arm_mnemonic -> sem_tuple exec sem_prod -> (register, __,
  __, rflag, condt) instr_desc_t

val arm_REV_semi : sem_tuple -> sem_tuple exec

val arm_REV16_semi : sem_tuple -> sem_tuple exec

val arm_REVSH_semi : sem_tuple -> sem_tuple exec

val arm_REV_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_REV16_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_REVSH_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_ADR_semi : sem_tuple -> sem_tuple exec

val arm_ADR_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_MOV_semi : sem_tuple -> sem_tuple exec

val arm_MOV_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_MOVT_semi : sem_tuple -> GRing.ComRing.sort -> sem_tuple exec

val arm_MOVT_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val bit_field_extract_semi :
  ((register, __, __, rflag, condt) wreg -> coq_Z -> (register, __, __,
  rflag, condt) wreg) -> (register, __, __, rflag, condt) wreg ->
  GRing.ComRing.sort -> GRing.ComRing.sort -> (register, __, __, rflag,
  condt) wreg exec

val arm_UBFX_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val extend_bits_semi :
  coq_Z -> (register, __, __, rflag, condt) wreg -> GRing.ComRing.sort ->
  (register, __, __, rflag, condt) wreg exec

val arm_UXTB_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_UXTH_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_SBFX_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_CMP_semi : sem_tuple -> sem_tuple -> sem_tuple exec

val arm_CMP_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_TST_semi : sem_tuple -> sem_tuple -> sem_tuple exec

val arm_TST_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_CMN_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val arm_extend_semi :
  wsize -> bool -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort exec

val arm_load_instr :
  arm_options -> arm_mnemonic -> (register, __, __, rflag, condt) instr_desc_t

val arm_store_instr :
  arm_options -> arm_mnemonic -> (register, __, __, rflag, condt) instr_desc_t

val arm_CLZ_instr :
  arm_options -> (register, __, __, rflag, condt) instr_desc_t

val mn_desc :
  arm_options -> arm_mnemonic -> (register, __, __, rflag, condt) instr_desc_t

val arm_instr_desc : arm_op -> (register, __, __, rflag, condt) instr_desc_t

val arm_prim_string : (char list * arm_op prim_constructor) list

val arm_op_decl : (register, __, __, rflag, condt, arm_op) asm_op_decl

type arm_prog = (register, __, __, rflag, condt, arm_op) asm_prog
