open BinInt
open BinNums
open Bool
open Datatypes
open String0
open Eqtype
open Pseudo_operator
open Sem_type
open Seq
open Slh_ops
open Ssralg
open Ssrbool
open Ssrfun
open Ssrfun0
open Type
open Utils0
open Values
open Var0
open Warray_
open Word0
open Wsize

type arg_desc =
| ADImplicit of Var.var
| ADExplicit of nat * Var.var option

type instruction_desc = { str : (unit -> char list); tin : stype list;
                          i_in : arg_desc list; tout : stype list;
                          i_out : arg_desc list;
                          semi : sem_tuple exec sem_prod;
                          i_safe : safe_cond list }

val str : instruction_desc -> unit -> char list

val tin : instruction_desc -> stype list

val i_in : instruction_desc -> arg_desc list

val tout : instruction_desc -> stype list

val i_out : instruction_desc -> arg_desc list

val semi : instruction_desc -> sem_tuple exec sem_prod

val i_safe : instruction_desc -> safe_cond list

type prim_x86_suffix =
| PVp of wsize
| PVv of velem * wsize
| PVsv of signedness * velem * wsize
| PVx of wsize * wsize
| PVvv of velem * wsize * velem * wsize

type 'asm_op prim_constructor =
| PrimX86 of prim_x86_suffix list * (prim_x86_suffix -> 'asm_op option)
| PrimARM of (bool -> bool -> 'asm_op)

type 'asm_op asmOp = { _eqT : 'asm_op eqTypeC;
                       asm_op_instr : ('asm_op -> instruction_desc);
                       prim_string : (char list * 'asm_op prim_constructor)
                                     list }

val _eqT : 'a1 asmOp -> 'a1 eqTypeC

val asm_op_instr : 'a1 asmOp -> 'a1 -> instruction_desc

val prim_string : 'a1 asmOp -> (char list * 'a1 prim_constructor) list

type 'asm_op asm_op_t = 'asm_op

type internal_reason =
| IRpc_load_scratch
| IRpc_load_msf
| IRpc_save_scratch

val internal_reason_beq : internal_reason -> internal_reason -> bool

val internal_reason_eq_dec : internal_reason -> internal_reason -> bool

val internal_reason_eq_axiom : internal_reason Equality.axiom

val internal_reason_eqMixin : internal_reason Equality.mixin_of

val internal_reason_eqType : Equality.coq_type

val string_of_internal_reason : internal_reason -> char list

type internal_op =
| Ouse_vars of internal_reason * stype list * stype list

val internal_op_beq : internal_op -> internal_op -> bool

val internal_op_eq_axiom : internal_op Equality.axiom

val internal_op_eqMixin : internal_op Equality.mixin_of

val internal_op_eqType : Equality.coq_type

type 'asm_op sopn =
| Opseudo_op of pseudo_operator
| Oslh of slh_op
| Oasm of 'asm_op asm_op_t
| Ointernal of internal_op

val sopn_beq : 'a1 asmOp -> 'a1 sopn -> 'a1 sopn -> bool

val sopn_eq_axiom : 'a1 asmOp -> 'a1 sopn Equality.axiom

val sopn_eqMixin : 'a1 asmOp -> 'a1 sopn Equality.mixin_of

val sopn_eqType : 'a1 asmOp -> Equality.coq_type

val sopn_copy : 'a1 asmOp -> wsize -> positive -> 'a1 sopn

val sopn_nop : 'a1 asmOp -> 'a1 sopn

val sopn_mulu : 'a1 asmOp -> wsize -> 'a1 sopn

val sopn_addcarry : 'a1 asmOp -> wsize -> 'a1 sopn

val sopn_subcarry : 'a1 asmOp -> wsize -> 'a1 sopn

val coq_Ocopy_instr : wsize -> positive -> instruction_desc

val coq_Onop_instr : instruction_desc

val coq_Omulu_instr : wsize -> instruction_desc

val coq_Oaddcarry_instr : wsize -> instruction_desc

val coq_Osubcarry_instr : wsize -> instruction_desc

val spill_semi : stype list -> sem_tuple exec sem_prod

val coq_Ospill_instr : spill_op -> stype list -> instruction_desc

val coq_Oswap_instr : stype -> instruction_desc

val pseudo_op_get_instr_desc : pseudo_operator -> instruction_desc

val se_init_sem : coq_MSFsize -> GRing.ComRing.sort exec

val se_update_sem :
  coq_MSFsize -> bool -> GRing.ComRing.sort -> GRing.ComRing.sort exec

val se_move_sem : coq_MSFsize -> GRing.ComRing.sort -> GRing.ComRing.sort exec

val se_protect_sem :
  coq_MSFsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  GRing.ComRing.sort exec

val se_protect_ptr_sem :
  coq_MSFsize -> positive -> WArray.array -> GRing.ComRing.sort ->
  WArray.array exec

val se_protect_ptr_fail_sem :
  coq_MSFsize -> positive -> WArray.array -> GRing.ComRing.sort ->
  WArray.array exec

val coq_SLHinit_str : char list

val coq_SLHinit_instr : coq_MSFsize -> instruction_desc

val coq_SLHupdate_str : char list

val coq_SLHupdate_instr : coq_MSFsize -> instruction_desc

val coq_SLHmove_str : char list

val coq_SLHmove_instr : coq_MSFsize -> instruction_desc

val coq_SLHprotect_str : char list

val coq_SLHprotect_instr : coq_MSFsize -> wsize -> instruction_desc

val coq_SLHprotect_ptr_str : char list

val coq_SLHprotect_ptr_instr : coq_MSFsize -> positive -> instruction_desc

val coq_SLHprotect_ptr_fail_str : char list

val coq_SLHprotect_ptr_fail_instr :
  coq_MSFsize -> positive -> instruction_desc

val slh_op_instruction_desc : coq_MSFsize -> slh_op -> instruction_desc

val mk_ltuple : (stype -> sem_ot) -> stype list -> sem_tuple

val default_value : stype -> sem_ot

val use_vars_semi : stype list -> stype list -> sem_tuple exec sem_prod

val use_vars_instr :
  internal_reason -> stype list -> stype list -> instruction_desc

val internal_op_instr_desc : internal_op -> instruction_desc

val get_instr_desc : coq_MSFsize -> 'a1 asmOp -> 'a1 sopn -> instruction_desc

val string_of_sopn : coq_MSFsize -> 'a1 asmOp -> 'a1 sopn -> char list

val sopn_tin : coq_MSFsize -> 'a1 asmOp -> 'a1 sopn -> stype list

val sopn_tout : coq_MSFsize -> 'a1 asmOp -> 'a1 sopn -> stype list

val sopn_sem : coq_MSFsize -> 'a1 asmOp -> 'a1 sopn -> sem_tuple exec sem_prod

val eqC_sopn : 'a1 asmOp -> 'a1 sopn eqTypeC

val map_prim_constructor :
  ('a1 -> 'a2) -> 'a1 prim_constructor -> 'a2 prim_constructor

val primM : 'a1 -> 'a1 prim_constructor

val primP : coq_PointerData -> (wsize -> 'a1) -> 'a1 prim_constructor

val sopn_prim_string :
  coq_PointerData -> 'a1 asmOp -> (char list * 'a1 sopn prim_constructor) list

val asmOp_sopn : coq_PointerData -> coq_MSFsize -> 'a1 asmOp -> 'a1 sopn asmOp
