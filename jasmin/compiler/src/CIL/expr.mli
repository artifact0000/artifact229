open BinInt
open BinNums
open Bool
open Datatypes
open Div
open Eqtype
open Global
open Seq
open Sopn
open Ssralg
open Ssrbool
open Ssrfun
open Type
open Utils0
open Var0
open Warray_
open Word0
open Word_ssrZ
open Wsize

type __ = Obj.t

type cmp_kind =
| Cmp_int
| Cmp_w of signedness * wsize

type op_kind =
| Op_int
| Op_w of wsize

type sop1 =
| Oword_of_int of wsize
| Oint_of_word of wsize
| Osignext of wsize * wsize
| Ozeroext of wsize * wsize
| Onot
| Olnot of wsize
| Oneg of op_kind

type sop2 =
| Obeq
| Oand
| Oor
| Oadd of op_kind
| Omul of op_kind
| Osub of op_kind
| Odiv of cmp_kind
| Omod of cmp_kind
| Oland of wsize
| Olor of wsize
| Olxor of wsize
| Olsr of wsize
| Olsl of op_kind
| Oasr of op_kind
| Oror of wsize
| Orol of wsize
| Oeq of op_kind
| Oneq of op_kind
| Olt of cmp_kind
| Ole of cmp_kind
| Ogt of cmp_kind
| Oge of cmp_kind
| Ovadd of velem * wsize
| Ovsub of velem * wsize
| Ovmul of velem * wsize
| Ovlsr of velem * wsize
| Ovlsl of velem * wsize
| Ovasr of velem * wsize

type combine_flags =
| CF_LT of signedness
| CF_LE of signedness
| CF_EQ
| CF_NEQ
| CF_GE of signedness
| CF_GT of signedness

type opN =
| Opack of wsize * pelem
| Ocombine_flags of combine_flags

val internal_op_kind_beq : op_kind -> op_kind -> bool

val sop1_beq : sop1 -> sop1 -> bool

val sop1_eq_dec : sop1 -> sop1 -> bool

val sop1_eq_axiom : sop1 Equality.axiom

val sop1_eqMixin : sop1 Equality.mixin_of

val sop1_eqType : Equality.coq_type

val internal_velem_beq : velem -> velem -> bool

val internal_signedness_beq : signedness -> signedness -> bool

val internal_cmp_kind_beq : cmp_kind -> cmp_kind -> bool

val sop2_beq : sop2 -> sop2 -> bool

val sop2_eq_dec : sop2 -> sop2 -> bool

val sop2_eq_axiom : sop2 Equality.axiom

val sop2_eqMixin : sop2 Equality.mixin_of

val sop2_eqType : Equality.coq_type

val internal_combine_flags_beq : combine_flags -> combine_flags -> bool

val internal_pelem_beq : pelem -> pelem -> bool

val opN_beq : opN -> opN -> bool

val opN_eq_dec : opN -> opN -> bool

val opN_eq_axiom : opN Equality.axiom

val opN_eqMixin : opN Equality.mixin_of

val opN_eqType : Equality.coq_type

val type_of_op1 : sop1 -> stype * stype

val type_of_op2 : sop2 -> (stype * stype) * stype

val tin_combine_flags : stype list

val type_of_opN : opN -> stype list * stype

module type TAG =
 sig
  type t

  val witness : t
 end

module VarInfo :
 TAG

type var_info = Location.t

val dummy_var_info : var_info

type var_i = { v_var : Var.var; v_info : var_info }

val v_var : var_i -> Var.var

val v_info : var_i -> var_info

val mk_var_i : Var.var -> var_i

type v_scope =
| Slocal
| Sglob

val v_scope_beq : v_scope -> v_scope -> bool

val v_scope_eq_dec : v_scope -> v_scope -> bool

val v_scope_eq_axiom : v_scope Equality.axiom

val v_scope_eqMixin : v_scope Equality.mixin_of

val v_scope_eqType : Equality.coq_type

type gvar = { gv : var_i; gs : v_scope }

val gv : gvar -> var_i

val gs : gvar -> v_scope

val mk_gvar : var_i -> gvar

val mk_lvar : var_i -> gvar

val is_lvar : gvar -> bool

val is_glob : gvar -> bool

type pexpr =
| Pconst of coq_Z
| Pbool of bool
| Parr_init of positive
| Pvar of gvar
| Pget of arr_access * wsize * gvar * pexpr
| Psub of arr_access * wsize * positive * gvar * pexpr
| Pload of wsize * var_i * pexpr
| Papp1 of sop1 * pexpr
| Papp2 of sop2 * pexpr * pexpr
| PappN of opN * pexpr list
| Pif of stype * pexpr * pexpr * pexpr

val coq_Plvar : var_i -> pexpr

val enot : pexpr -> pexpr

val eor : pexpr -> pexpr -> pexpr

val eand : pexpr -> pexpr -> pexpr

val eeq : pexpr -> pexpr -> pexpr

val eneq : pexpr -> pexpr -> pexpr

val cf_of_condition : sop2 -> (combine_flags * wsize) option

val pexpr_of_cf : combine_flags -> Var.var list -> pexpr

module Coq__1 : sig
 type lval =
 | Lnone of var_info * stype
 | Lvar of var_i
 | Lmem of wsize * var_i * pexpr
 | Laset of arr_access * wsize * var_i * pexpr
 | Lasub of arr_access * wsize * positive * var_i * pexpr
end
include module type of struct include Coq__1 end

val get_pvar : pexpr -> Var.var exec

val get_lvar : lval -> Var.var exec

val coq_Lnone_b : var_info -> lval

type dir =
| UpTo
| DownTo

val dir_beq : dir -> dir -> bool

val dir_eq_dec : dir -> dir -> bool

val dir_eq_axiom : dir Equality.axiom

val dir_eqMixin : dir Equality.mixin_of

val dir_eqType : Equality.coq_type

type range = (dir * pexpr) * pexpr

val wrange : dir -> coq_Z -> coq_Z -> coq_Z list

module type InstrInfoT =
 sig
  type t

  val witness : t

  val with_location : t -> t

  val is_inline : t -> bool

  val update_after_call : t -> bool
 end

module InstrInfo :
 InstrInfoT

type instr_info = IInfo.t

val dummy_instr_info : instr_info

val ii_with_location : instr_info -> instr_info

val ii_is_inline : instr_info -> bool

val ii_update_after_call : instr_info -> bool

type assgn_tag =
| AT_none
| AT_keep
| AT_rename
| AT_inline
| AT_phinode

val assgn_tag_beq : assgn_tag -> assgn_tag -> bool

val assgn_tag_eq_dec : assgn_tag -> assgn_tag -> bool

val assgn_tag_eq_axiom : assgn_tag Equality.axiom

val assgn_tag_eqMixin : assgn_tag Equality.mixin_of

val assgn_tag_eqType : Equality.coq_type

type align =
| Align
| NoAlign

type 'asm_op instr_r =
| Cassgn of lval * assgn_tag * stype * pexpr
| Copn of lval list * assgn_tag * 'asm_op sopn * pexpr list
| Csyscall of lval list * BinNums.positive Syscall_t.syscall_t * pexpr list
| Cif of pexpr * 'asm_op instr list * 'asm_op instr list
| Cfor of var_i * range * 'asm_op instr list
| Cwhile of align * 'asm_op instr list * pexpr * 'asm_op instr list
| Ccall of lval list * funname * pexpr list
and 'asm_op instr =
| MkI of instr_info * 'asm_op instr_r

val cmd_rect_aux :
  'a1 asmOp -> 'a3 -> ('a1 instr -> 'a1 instr list -> 'a2 -> 'a3 -> 'a3) ->
  ('a1 instr -> 'a2) -> 'a1 instr list -> 'a3

val instr_Rect :
  'a1 asmOp -> ('a1 instr_r -> instr_info -> 'a2 -> 'a3) -> 'a4 -> ('a1 instr
  -> 'a1 instr list -> 'a3 -> 'a4 -> 'a4) -> (lval -> assgn_tag -> stype ->
  pexpr -> 'a2) -> (lval list -> assgn_tag -> 'a1 sopn -> pexpr list -> 'a2)
  -> (lval list -> BinNums.positive Syscall_t.syscall_t -> pexpr list -> 'a2)
  -> (pexpr -> 'a1 instr list -> 'a1 instr list -> 'a4 -> 'a4 -> 'a2) ->
  (var_i -> dir -> pexpr -> pexpr -> 'a1 instr list -> 'a4 -> 'a2) -> (align
  -> 'a1 instr list -> pexpr -> 'a1 instr list -> 'a4 -> 'a4 -> 'a2) -> (lval
  list -> funname -> pexpr list -> 'a2) -> 'a1 instr -> 'a3

val instr_r_Rect :
  'a1 asmOp -> ('a1 instr_r -> instr_info -> 'a2 -> 'a3) -> 'a4 -> ('a1 instr
  -> 'a1 instr list -> 'a3 -> 'a4 -> 'a4) -> (lval -> assgn_tag -> stype ->
  pexpr -> 'a2) -> (lval list -> assgn_tag -> 'a1 sopn -> pexpr list -> 'a2)
  -> (lval list -> BinNums.positive Syscall_t.syscall_t -> pexpr list -> 'a2)
  -> (pexpr -> 'a1 instr list -> 'a1 instr list -> 'a4 -> 'a4 -> 'a2) ->
  (var_i -> dir -> pexpr -> pexpr -> 'a1 instr list -> 'a4 -> 'a2) -> (align
  -> 'a1 instr list -> pexpr -> 'a1 instr list -> 'a4 -> 'a4 -> 'a2) -> (lval
  list -> funname -> pexpr list -> 'a2) -> 'a1 instr_r -> 'a2

val cmd_rect :
  'a1 asmOp -> ('a1 instr_r -> instr_info -> 'a2 -> 'a3) -> 'a4 -> ('a1 instr
  -> 'a1 instr list -> 'a3 -> 'a4 -> 'a4) -> (lval -> assgn_tag -> stype ->
  pexpr -> 'a2) -> (lval list -> assgn_tag -> 'a1 sopn -> pexpr list -> 'a2)
  -> (lval list -> BinNums.positive Syscall_t.syscall_t -> pexpr list -> 'a2)
  -> (pexpr -> 'a1 instr list -> 'a1 instr list -> 'a4 -> 'a4 -> 'a2) ->
  (var_i -> dir -> pexpr -> pexpr -> 'a1 instr list -> 'a4 -> 'a2) -> (align
  -> 'a1 instr list -> pexpr -> 'a1 instr list -> 'a4 -> 'a4 -> 'a2) -> (lval
  list -> funname -> pexpr list -> 'a2) -> 'a1 instr list -> 'a4

module FunInfo :
 TAG

type fun_info = FInfo.t

type progT =
| Build_progT

type extra_fun_t = __

type extra_prog_t = __

type extra_val_t = __

type ('asm_op, 'extra_fun_t) _fundef = { f_info : fun_info;
                                         f_tyin : stype list;
                                         f_params : var_i list;
                                         f_body : 'asm_op instr list;
                                         f_tyout : stype list;
                                         f_res : var_i list;
                                         f_extra : 'extra_fun_t }

val f_info : 'a1 asmOp -> ('a1, 'a2) _fundef -> fun_info

val f_tyin : 'a1 asmOp -> ('a1, 'a2) _fundef -> stype list

val f_params : 'a1 asmOp -> ('a1, 'a2) _fundef -> var_i list

val f_body : 'a1 asmOp -> ('a1, 'a2) _fundef -> 'a1 instr list

val f_tyout : 'a1 asmOp -> ('a1, 'a2) _fundef -> stype list

val f_res : 'a1 asmOp -> ('a1, 'a2) _fundef -> var_i list

val f_extra : 'a1 asmOp -> ('a1, 'a2) _fundef -> 'a2

type ('asm_op, 'extra_fun_t) _fun_decl =
  funname * ('asm_op, 'extra_fun_t) _fundef

type ('asm_op, 'extra_fun_t, 'extra_prog_t) _prog = { p_funcs : ('asm_op,
                                                                'extra_fun_t)
                                                                _fun_decl list;
                                                      p_globs : glob_decl list;
                                                      p_extra : 'extra_prog_t }

val p_funcs : 'a1 asmOp -> ('a1, 'a2, 'a3) _prog -> ('a1, 'a2) _fun_decl list

val p_globs : 'a1 asmOp -> ('a1, 'a2, 'a3) _prog -> glob_decl list

val p_extra : 'a1 asmOp -> ('a1, 'a2, 'a3) _prog -> 'a3

type 'asm_op fundef = ('asm_op, extra_fun_t) _fundef

type function_signature = stype list * stype list

val signature_of_fundef :
  'a1 asmOp -> progT -> 'a1 fundef -> function_signature

type 'asm_op fun_decl = funname * 'asm_op fundef

type 'asm_op prog = ('asm_op, extra_fun_t, extra_prog_t) _prog

val coq_Build_prog :
  'a1 asmOp -> progT -> ('a1, extra_fun_t) _fun_decl list -> glob_decl list
  -> extra_prog_t -> 'a1 prog

val progUnit : progT

type 'asm_op ufundef = 'asm_op fundef

type 'asm_op ufun_decl = 'asm_op fun_decl

type 'asm_op ufun_decls = 'asm_op fun_decl list

type 'asm_op uprog = 'asm_op prog

type 'asm_op _ufundef = ('asm_op, unit) _fundef

type 'asm_op _ufun_decl = ('asm_op, unit) _fun_decl

type 'asm_op _ufun_decls = ('asm_op, unit) _fun_decl list

type 'asm_op _uprog = ('asm_op, unit, unit) _prog

val to_uprog : 'a1 asmOp -> 'a1 _uprog -> 'a1 uprog

type saved_stack =
| SavedStackNone
| SavedStackReg of Var.var
| SavedStackStk of coq_Z

val saved_stack_beq : saved_stack -> saved_stack -> bool

val saved_stack_eq_axiom : saved_stack Equality.axiom

val saved_stack_eqMixin : saved_stack Equality.mixin_of

val saved_stack_eqType : Equality.coq_type

type return_address_location =
| RAnone
| RAreg of Var.var * Var.var option
| RAstack of Var.var option * coq_Z * Var.var option

val is_RAnone : return_address_location -> bool

val is_RAstack : return_address_location -> bool

val is_RAstack_None : return_address_location -> bool

val return_address_location_beq :
  return_address_location -> return_address_location -> bool

val return_address_location_eq_axiom : return_address_location Equality.axiom

val return_address_location_eqMixin :
  return_address_location Equality.mixin_of

val return_address_location_eqType : Equality.coq_type

type stk_fun_extra = { sf_align : wsize; sf_stk_sz : coq_Z;
                       sf_stk_ioff : coq_Z; sf_stk_extra_sz : coq_Z;
                       sf_stk_max : coq_Z; sf_max_call_depth : coq_Z;
                       sf_to_save : (Var.var * coq_Z) list;
                       sf_save_stack : saved_stack;
                       sf_return_address : return_address_location }

val sf_align : stk_fun_extra -> wsize

val sf_stk_sz : stk_fun_extra -> coq_Z

val sf_stk_ioff : stk_fun_extra -> coq_Z

val sf_stk_extra_sz : stk_fun_extra -> coq_Z

val sf_stk_max : stk_fun_extra -> coq_Z

val sf_max_call_depth : stk_fun_extra -> coq_Z

val sf_to_save : stk_fun_extra -> (Var.var * coq_Z) list

val sf_save_stack : stk_fun_extra -> saved_stack

val sf_return_address : stk_fun_extra -> return_address_location

type sprog_extra = { sp_rsp : Ident.Ident.ident; sp_rip : Ident.Ident.ident;
                     sp_globs : GRing.ComRing.sort list }

val sp_rsp : sprog_extra -> Ident.Ident.ident

val sp_rip : sprog_extra -> Ident.Ident.ident

val sp_globs : sprog_extra -> GRing.ComRing.sort list

val progStack : coq_PointerData -> progT

type 'asm_op sfundef = 'asm_op fundef

type 'asm_op sfun_decl = 'asm_op fun_decl

type 'asm_op sfun_decls = 'asm_op fun_decl list

type 'asm_op sprog = 'asm_op prog

type 'asm_op _sfundef = ('asm_op, stk_fun_extra) _fundef

type 'asm_op _sfun_decl = ('asm_op, stk_fun_extra) _fun_decl

type 'asm_op _sfun_decls = ('asm_op, stk_fun_extra) _fun_decl list

type 'asm_op _sprog = ('asm_op, stk_fun_extra, sprog_extra) _prog

val to_sprog : coq_PointerData -> 'a1 asmOp -> 'a1 _sprog -> 'a1 sprog

val with_body :
  'a1 asmOp -> ('a1, 'a2) _fundef -> 'a1 instr list -> ('a1, 'a2) _fundef

val swith_extra :
  coq_PointerData -> 'a1 asmOp -> coq_PointerData -> 'a1 ufundef ->
  extra_fun_t -> 'a1 sfundef

val is_const : pexpr -> coq_Z option

val is_bool : pexpr -> bool option

val is_Papp2 : pexpr -> ((sop2 * pexpr) * pexpr) option

val is_array_init : pexpr -> bool

val cast_w : wsize -> pexpr -> pexpr

val cast_ptr : coq_PointerData -> pexpr -> pexpr

val cast_const : coq_PointerData -> coq_Z -> pexpr

val eword_of_int : wsize -> coq_Z -> pexpr

val wconst : wsize -> GRing.ComRing.sort -> pexpr

val is_wconst : wsize -> pexpr -> GRing.ComRing.sort option

val is_wconst_of_size : Equality.sort -> pexpr -> coq_Z option

val vrv_rec : SvExtra.Sv.t -> lval -> SvExtra.Sv.t

val vrvs_rec : SvExtra.Sv.t -> lval list -> SvExtra.Sv.t

val vrv : lval -> SvExtra.Sv.t

val vrvs : lval list -> SvExtra.Sv.t

val lv_write_mem : lval -> bool

val write_i_rec : 'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr_r -> SvExtra.Sv.t

val write_I_rec : 'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr -> SvExtra.Sv.t

val write_i : 'a1 asmOp -> 'a1 instr_r -> SvExtra.Sv.t

val write_I : 'a1 asmOp -> 'a1 instr -> SvExtra.Sv.t

val write_c_rec : 'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr list -> SvExtra.Sv.t

val write_c : 'a1 asmOp -> 'a1 instr list -> SvExtra.Sv.t

val use_mem : pexpr -> bool

val read_gvar : gvar -> SvExtra.Sv.t

val read_e_rec : SvExtra.Sv.t -> pexpr -> SvExtra.Sv.t

val read_e : pexpr -> SvExtra.Sv.t

val read_es_rec : SvExtra.Sv.t -> pexpr list -> SvExtra.Sv.t

val read_es : pexpr list -> SvExtra.Sv.t

val read_rv_rec : SvExtra.Sv.t -> lval -> SvExtra.Sv.t

val read_rv : lval -> SvExtra.Sv.t

val read_rvs_rec : SvExtra.Sv.t -> lval list -> SvExtra.Sv.t

val read_rvs : lval list -> SvExtra.Sv.t

val read_i_rec : 'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr_r -> SvExtra.Sv.t

val read_I_rec : 'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr -> SvExtra.Sv.t

val read_c_rec : 'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr list -> SvExtra.Sv.t

val read_i : 'a1 asmOp -> 'a1 instr_r -> SvExtra.Sv.t

val read_I : 'a1 asmOp -> 'a1 instr -> SvExtra.Sv.t

val read_c : 'a1 asmOp -> 'a1 instr list -> SvExtra.Sv.t

val vars_I : 'a1 asmOp -> 'a1 instr -> SvExtra.Sv.t

val vars_c : 'a1 asmOp -> 'a1 instr list -> SvExtra.Sv.t

val vars_lval : lval -> SvExtra.Sv.t

val vars_lvals : lval list -> SvExtra.Sv.t

val vars_l : var_i list -> SvExtra.Sv.t

val vars_fd : 'a1 asmOp -> progT -> 'a1 fundef -> SvExtra.Sv.t

val vars_p : 'a1 asmOp -> progT -> 'a1 fun_decl list -> SvExtra.Sv.t

val eq_gvar : gvar -> gvar -> bool

val eq_expr : pexpr -> pexpr -> bool

val to_lvals : Var.var list -> lval list

val is_false : pexpr -> bool

val is_zero : Equality.sort -> pexpr -> bool

val instr_of_copn_args :
  'a1 asmOp -> assgn_tag -> ((lval list * 'a1 sopn) * pexpr list) -> 'a1
  instr_r

val gen_use_vars :
  'a1 asmOp -> internal_reason -> Var.var list -> stype list -> 'a1 instr_r

val use_vars_get_reg :
  'a1 asmOp -> coq_PointerData -> internal_reason -> 'a1 instr_r

val use_vars_use_one : 'a1 asmOp -> internal_reason -> Var.var -> 'a1 instr_r

module type OpnArgs =
 sig
  type lval

  type rval

  val lvar : var_i -> lval

  val lmem : coq_PointerData -> wsize -> var_i -> coq_Z -> lval

  val rvar : var_i -> rval

  val rconst : wsize -> coq_Z -> rval
 end

module CopnArgs :
 sig
  type lval = Coq__1.lval

  type rval = pexpr

  val lvar : var_i -> Coq__1.lval

  val lmem : coq_PointerData -> wsize -> var_i -> coq_Z -> Coq__1.lval

  val rvar : var_i -> pexpr

  val rconst : wsize -> coq_Z -> pexpr
 end
