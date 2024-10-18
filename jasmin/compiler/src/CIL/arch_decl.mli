open BinNums
open Bool
open Datatypes
open Eqtype
open Expr
open Flag_combination
open Label
open Sem_type
open Seq
open Sopn
open Ssralg
open Ssrbool
open Ssrnat
open Strings
open Type
open Utils0
open Var0
open Word0
open Word_ssrZ
open Wsize

type __ = Obj.t

type 't coq_ToString = { category : char list; _finC : 't finTypeC;
                         to_string : ('t -> char list) }

val category : stype -> 'a1 coq_ToString -> char list

val _finC : stype -> 'a1 coq_ToString -> 'a1 finTypeC

val to_string : stype -> 'a1 coq_ToString -> 'a1 -> char list

val rtype : stype -> 'a1 coq_ToString -> stype

type ('reg, 'regx, 'xreg, 'rflag, 'cond) arch_decl = { reg_size : wsize;
                                                       xreg_size : wsize;
                                                       cond_eqC : 'cond
                                                                  eqTypeC;
                                                       toS_r : 'reg
                                                               coq_ToString;
                                                       toS_rx : 'regx
                                                                coq_ToString;
                                                       toS_x : 'xreg
                                                               coq_ToString;
                                                       toS_f : 'rflag
                                                               coq_ToString;
                                                       ad_rsp : 'reg;
                                                       ad_fcp : coq_FlagCombinationParams }

val reg_size : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> wsize

val xreg_size : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> wsize

val cond_eqC : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> 'a5 eqTypeC

val toS_r : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> 'a1 coq_ToString

val toS_rx : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> 'a2 coq_ToString

val toS_x : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> 'a3 coq_ToString

val toS_f : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> 'a4 coq_ToString

val ad_rsp : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> 'a1

val ad_fcp : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> coq_FlagCombinationParams

val arch_pd : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> coq_PointerData

val arch_msfsz : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> coq_MSFsize

val mk_ptr :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> Ident.Ident.ident -> Var.var

type ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_t = 'reg

type ('reg, 'regx, 'xreg, 'rflag, 'cond) regx_t = 'regx

type ('reg, 'regx, 'xreg, 'rflag, 'cond) xreg_t = 'xreg

type ('reg, 'regx, 'xreg, 'rflag, 'cond) rflag_t = 'rflag

type ('reg, 'regx, 'xreg, 'rflag, 'cond) cond_t = 'cond

val sreg : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> stype

type ('reg, 'regx, 'xreg, 'rflag, 'cond) wreg = sem_t

val sxreg : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> stype

type ('reg, 'regx, 'xreg, 'rflag, 'cond) wxreg = sem_t

type ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_address = { ad_disp : GRing.ComRing.sort;
                                                         ad_base : ('reg,
                                                                   'regx,
                                                                   'xreg,
                                                                   'rflag,
                                                                   'cond)
                                                                   reg_t
                                                                   option;
                                                         ad_scale : nat;
                                                         ad_offset : 
                                                         ('reg, 'regx, 'xreg,
                                                         'rflag, 'cond) reg_t
                                                         option }

val ad_disp :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  reg_address -> GRing.ComRing.sort

val ad_base :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  reg_address -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t option

val ad_scale :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  reg_address -> nat

val ad_offset :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  reg_address -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t option

type ('reg, 'regx, 'xreg, 'rflag, 'cond) address =
| Areg of ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_address
| Arip of GRing.ComRing.sort

val oeq_reg :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t
  option -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t option -> bool

val reg_address_beq :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  reg_address -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_address -> bool

val reg_address_eq_axiom :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  reg_address Equality.axiom

val reg_address_eqMixin :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  reg_address Equality.mixin_of

val reg_address_eqType :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> Equality.coq_type

val address_beq :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) address ->
  ('a1, 'a2, 'a3, 'a4, 'a5) address -> bool

val address_eq_axiom :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) address
  Equality.axiom

val address_eqMixin :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) address
  Equality.mixin_of

val address_eqType : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> Equality.coq_type

type ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_arg =
| Condt of ('reg, 'regx, 'xreg, 'rflag, 'cond) cond_t
| Imm of wsize * GRing.ComRing.sort
| Reg of ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_t
| Regx of ('reg, 'regx, 'xreg, 'rflag, 'cond) regx_t
| Addr of ('reg, 'regx, 'xreg, 'rflag, 'cond) address
| XReg of ('reg, 'regx, 'xreg, 'rflag, 'cond) xreg_t

type ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_args =
  ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_arg list

val is_Condt :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg ->
  ('a1, 'a2, 'a3, 'a4, 'a5) cond_t option

val asm_arg_beq :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg ->
  ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg -> bool

val asm_arg_eq_axiom :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg
  Equality.axiom

val asm_arg_eqMixin :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg
  Equality.mixin_of

val asm_arg_eqType : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> Equality.coq_type

type msb_flag =
| MSB_CLEAR
| MSB_MERGE

val msb_flag_beq : msb_flag -> msb_flag -> bool

val msb_flag_eq_dec : msb_flag -> msb_flag -> bool

val msb_flag_eq_axiom : msb_flag Equality.axiom

val msb_flag_eqMixin : msb_flag Equality.mixin_of

val msb_flag_eqType : Equality.coq_type

type ('reg, 'regx, 'xreg, 'rflag, 'cond) implicit_arg =
| IArflag of ('reg, 'regx, 'xreg, 'rflag, 'cond) rflag_t
| IAreg of ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_t

val implicit_arg_beq :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  implicit_arg -> ('a1, 'a2, 'a3, 'a4, 'a5) implicit_arg -> bool

val implicit_arg_eq_axiom :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  implicit_arg Equality.axiom

val implicit_arg_eqMixin :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  implicit_arg Equality.mixin_of

val implicit_arg_eqType :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> Equality.coq_type

type addr_kind =
| AK_compute
| AK_mem

type ('reg, 'regx, 'xreg, 'rflag, 'cond) arg_desc =
| ADImplicit of ('reg, 'regx, 'xreg, 'rflag, 'cond) implicit_arg
| ADExplicit of addr_kind * nat
   * ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_t option

val coq_F :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) rflag_t ->
  ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc

val coq_R :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t ->
  ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc

val coq_E :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> nat -> ('a1, 'a2, 'a3, 'a4, 'a5)
  arg_desc

val coq_Ec :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> nat -> ('a1, 'a2, 'a3, 'a4, 'a5)
  arg_desc

val coq_Ef :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> nat -> ('a1, 'a2, 'a3, 'a4, 'a5)
  reg_t -> ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc

val check_oreg :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> Equality.sort option -> ('a1, 'a2,
  'a3, 'a4, 'a5) asm_arg -> bool

type arg_kind =
| CAcond
| CAreg
| CAregx
| CAxmm
| CAmem of bool
| CAimm of wsize

val arg_kind_beq : arg_kind -> arg_kind -> bool

val arg_kind_eq_dec : arg_kind -> arg_kind -> bool

val arg_kind_eq_axiom : arg_kind Equality.axiom

val arg_kind_eqMixin : arg_kind Equality.mixin_of

val arg_kind_eqType : Equality.coq_type

type arg_kinds = arg_kind list

type args_kinds = arg_kinds list

type i_args_kinds = args_kinds list

val check_arg_kind :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg ->
  arg_kind -> bool

val check_arg_kinds :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg ->
  arg_kinds -> bool

val check_args_kinds :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_args
  -> args_kinds -> bool

val check_i_args_kinds :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> i_args_kinds -> ('a1, 'a2, 'a3, 'a4,
  'a5) asm_args -> bool

val check_arg_dest :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc
  -> stype -> bool

type ('reg, 'regx, 'xreg, 'rflag, 'cond) pp_asm_op_ext =
| PP_error
| PP_name
| PP_iname of wsize
| PP_iname2 of char list * wsize * wsize
| PP_viname of velem * bool
| PP_viname2 of velem * velem
| PP_ct of ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_arg

type ('reg, 'regx, 'xreg, 'rflag, 'cond) pp_asm_op = { pp_aop_name : 
                                                       char list;
                                                       pp_aop_ext : ('reg,
                                                                    'regx,
                                                                    'xreg,
                                                                    'rflag,
                                                                    'cond)
                                                                    pp_asm_op_ext;
                                                       pp_aop_args : 
                                                       (wsize * ('reg, 'regx,
                                                       'xreg, 'rflag, 'cond)
                                                       asm_arg) list }

val pp_aop_name :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) pp_asm_op
  -> char list

val pp_aop_ext :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) pp_asm_op
  -> ('a1, 'a2, 'a3, 'a4, 'a5) pp_asm_op_ext

val pp_aop_args :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) pp_asm_op
  -> (wsize * ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg) list

type ('reg, 'regx, 'xreg, 'rflag, 'cond) instr_desc_t = { id_msb_flag : 
                                                          msb_flag;
                                                          id_tin : stype list;
                                                          id_in : ('reg,
                                                                  'regx,
                                                                  'xreg,
                                                                  'rflag,
                                                                  'cond)
                                                                  arg_desc
                                                                  list;
                                                          id_tout : stype list;
                                                          id_out : ('reg,
                                                                   'regx,
                                                                   'xreg,
                                                                   'rflag,
                                                                   'cond)
                                                                   arg_desc
                                                                   list;
                                                          id_semi : sem_tuple
                                                                    exec
                                                                    sem_prod;
                                                          id_args_kinds : 
                                                          i_args_kinds;
                                                          id_nargs : 
                                                          nat;
                                                          id_str_jas : 
                                                          (unit -> char list);
                                                          id_safe : safe_cond
                                                                    list;
                                                          id_pp_asm : 
                                                          (('reg, 'regx,
                                                          'xreg, 'rflag,
                                                          'cond) asm_args ->
                                                          ('reg, 'regx,
                                                          'xreg, 'rflag,
                                                          'cond) pp_asm_op) }

val id_msb_flag :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  instr_desc_t -> msb_flag

val id_tin :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  instr_desc_t -> stype list

val id_in :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  instr_desc_t -> ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc list

val id_tout :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  instr_desc_t -> stype list

val id_out :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  instr_desc_t -> ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc list

val id_semi :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  instr_desc_t -> sem_tuple exec sem_prod

val id_args_kinds :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  instr_desc_t -> i_args_kinds

val id_nargs :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  instr_desc_t -> nat

val id_str_jas :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  instr_desc_t -> unit -> char list

val id_safe :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  instr_desc_t -> safe_cond list

val id_pp_asm :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  instr_desc_t -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_args -> ('a1, 'a2, 'a3, 'a4,
  'a5) pp_asm_op

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_op_decl = { _eqT : 
                                                                  'asm_op
                                                                  eqTypeC;
                                                                  instr_desc_op : 
                                                                  ('asm_op ->
                                                                  ('reg,
                                                                  'regx,
                                                                  'xreg,
                                                                  'rflag,
                                                                  'cond)
                                                                  instr_desc_t);
                                                                  prim_string : 
                                                                  (char list * 'asm_op
                                                                  prim_constructor)
                                                                  list }

val _eqT :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> 'a6 eqTypeC

val instr_desc_op :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> 'a6 -> ('a1, 'a2, 'a3, 'a4, 'a5) instr_desc_t

val prim_string :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> (char list * 'a6 prim_constructor) list

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_op_t' = 'asm_op

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_op_msb_t =
  wsize option * 'asm_op

val extend_size : wsize -> stype -> stype

val wextend_size : wsize -> stype -> sem_ot -> sem_ot

val extend_tuple : wsize -> stype list -> sem_tuple -> sem_tuple

val apply_lprod : ('a1 -> 'a2) -> __ list -> 'a1 lprod -> 'a2 lprod

val is_not_CAmem : arg_kind -> bool

val exclude_mem_args_kinds :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc
  -> args_kinds -> args_kinds

val exclude_mem_i_args_kinds :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc
  -> i_args_kinds -> i_args_kinds

val exclude_mem_aux :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> i_args_kinds -> ('a1, 'a2, 'a3, 'a4,
  'a5) arg_desc list -> i_args_kinds

val exclude_mem :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> i_args_kinds -> ('a1, 'a2, 'a3, 'a4,
  'a5) arg_desc list -> i_args_kinds

val instr_desc :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_op_msb_t -> ('a1, 'a2,
  'a3, 'a4, 'a5) instr_desc_t

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_i_r =
| ALIGN
| LABEL of label_kind * label
| STORELABEL of ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_t * label
| JMP of remote_label
| JMPI of ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_arg
| Jcc of label * ('reg, 'regx, 'xreg, 'rflag, 'cond) cond_t
| JAL of ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_t * remote_label
| CALL of remote_label
| POPPC
| AsmOp of ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_op_t'
   * ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_args
| SysCall of BinNums.positive Syscall_t.syscall_t

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_i = { asmi_ii : 
                                                            instr_info;
                                                            asmi_i : 
                                                            ('reg, 'regx,
                                                            'xreg, 'rflag,
                                                            'cond, 'asm_op)
                                                            asm_i_r }

val asmi_ii :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_i -> instr_info

val asmi_i :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_i -> ('a1, 'a2, 'a3, 'a4,
  'a5, 'a6) asm_i_r

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_code =
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_i list

type ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_typed_reg =
| ARReg of ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_t
| ARegX of ('reg, 'regx, 'xreg, 'rflag, 'cond) regx_t
| AXReg of ('reg, 'regx, 'xreg, 'rflag, 'cond) xreg_t
| ABReg of ('reg, 'regx, 'xreg, 'rflag, 'cond) rflag_t

val asm_typed_reg_beq :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_typed_reg -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_typed_reg -> bool

val asm_typed_reg_eq_axiom :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_typed_reg Equality.axiom

val asm_typed_reg_eqMixin :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_typed_reg Equality.mixin_of

val asm_typed_reg_eqType :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> Equality.coq_type

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_fundef = { asm_fd_align : 
                                                                 wsize;
                                                                 asm_fd_arg : 
                                                                 ('reg,
                                                                 'regx,
                                                                 'xreg,
                                                                 'rflag,
                                                                 'cond)
                                                                 asm_typed_reg
                                                                 list;
                                                                 asm_fd_body : 
                                                                 ('reg,
                                                                 'regx,
                                                                 'xreg,
                                                                 'rflag,
                                                                 'cond,
                                                                 'asm_op)
                                                                 asm_code;
                                                                 asm_fd_res : 
                                                                 ('reg,
                                                                 'regx,
                                                                 'xreg,
                                                                 'rflag,
                                                                 'cond)
                                                                 asm_typed_reg
                                                                 list;
                                                                 asm_fd_export : 
                                                                 bool;
                                                                 asm_fd_total_stack : 
                                                                 coq_Z }

val asm_fd_align :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef -> wsize

val asm_fd_arg :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef -> ('a1, 'a2, 'a3,
  'a4, 'a5) asm_typed_reg list

val asm_fd_body :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef -> ('a1, 'a2, 'a3,
  'a4, 'a5, 'a6) asm_code

val asm_fd_res :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef -> ('a1, 'a2, 'a3,
  'a4, 'a5) asm_typed_reg list

val asm_fd_export :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef -> bool

val asm_fd_total_stack :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef -> coq_Z

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_prog = { asm_globs : 
                                                               GRing.ComRing.sort
                                                               list;
                                                               asm_funcs : 
                                                               (funname * ('reg,
                                                               'regx, 'xreg,
                                                               'rflag, 'cond,
                                                               'asm_op)
                                                               asm_fundef)
                                                               list }

val asm_globs :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_prog ->
  GRing.ComRing.sort list

val asm_funcs :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_prog -> (funname * ('a1,
  'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef) list

val is_ABReg :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_typed_reg -> bool

type ('reg, 'regx, 'xreg, 'rflag, 'cond) calling_convention = { callee_saved : 
                                                                ('reg, 'regx,
                                                                'xreg,
                                                                'rflag,
                                                                'cond)
                                                                asm_typed_reg
                                                                list;
                                                                call_reg_args : 
                                                                ('reg, 'regx,
                                                                'xreg,
                                                                'rflag,
                                                                'cond) reg_t
                                                                list;
                                                                call_xreg_args : 
                                                                ('reg, 'regx,
                                                                'xreg,
                                                                'rflag,
                                                                'cond) xreg_t
                                                                list;
                                                                call_reg_ret : 
                                                                ('reg, 'regx,
                                                                'xreg,
                                                                'rflag,
                                                                'cond) reg_t
                                                                list;
                                                                call_xreg_ret : 
                                                                ('reg, 'regx,
                                                                'xreg,
                                                                'rflag,
                                                                'cond) xreg_t
                                                                list }

val callee_saved :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_typed_reg list

val call_reg_args :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t list

val call_xreg_args :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5) xreg_t list

val call_reg_ret :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t list

val call_xreg_ret :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5) xreg_t list

val get_ARReg :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_typed_reg -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t option

val get_ARegX :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_typed_reg -> ('a1, 'a2, 'a3, 'a4, 'a5) regx_t option

val get_AXReg :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_typed_reg -> ('a1, 'a2, 'a3, 'a4, 'a5) xreg_t option

val check_list :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> 'a6 eqTypeC -> (('a1, 'a2, 'a3, 'a4,
  'a5) asm_typed_reg -> 'a6 option) -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_typed_reg list -> 'a6 list -> bool

val check_call_conv :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) calling_convention -> ('a1, 'a2,
  'a3, 'a4, 'a5, 'a6) asm_fundef -> bool

val registers :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t list

val registerxs :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) regx_t list

val xregisters :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) xreg_t list

val rflags :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) rflag_t
  list

type rflagv =
| Def of bool
| Undef

val rflagv_beq : rflagv -> rflagv -> bool

val rflagv_eq_dec : rflagv -> rflagv -> bool

val rflagv_eq_axiom : rflagv Equality.axiom

val rflagv_eqMixin : rflagv Equality.mixin_of

val rflagv_eqType : Equality.coq_type

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm = { _arch_decl : 
                                                          ('reg, 'regx,
                                                          'xreg, 'rflag,
                                                          'cond) arch_decl;
                                                          _asm_op_decl : 
                                                          ('reg, 'regx,
                                                          'xreg, 'rflag,
                                                          'cond, 'asm_op)
                                                          asm_op_decl;
                                                          eval_cond : 
                                                          ((('reg, 'regx,
                                                          'xreg, 'rflag,
                                                          'cond) reg_t ->
                                                          GRing.ComRing.sort)
                                                          -> (('reg, 'regx,
                                                          'xreg, 'rflag,
                                                          'cond) rflag_t ->
                                                          bool exec) ->
                                                          ('reg, 'regx,
                                                          'xreg, 'rflag,
                                                          'cond) cond_t ->
                                                          bool exec) }

val _arch_decl :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm -> ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl

val _asm_op_decl :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_op_decl

val eval_cond :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm -> (('a1, 'a2, 'a3, 'a4, 'a5) reg_t ->
  GRing.ComRing.sort) -> (('a1, 'a2, 'a3, 'a4, 'a5) rflag_t -> bool exec) ->
  ('a1, 'a2, 'a3, 'a4, 'a5) cond_t -> bool exec
