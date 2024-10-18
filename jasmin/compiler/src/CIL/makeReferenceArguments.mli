open Datatypes
open Hexadecimal
open HexadecimalString
open String0
open Compiler_util
open Expr
open Seq
open Sopn
open Syscall
open Type
open Utils0
open Var0

module E :
 sig
  val pass : char list

  val make_ref_error : instr_info -> char list -> pp_error_loc
 end

val with_id :
  (instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident) ->
  instr_info -> uint -> var_info -> Ident.Ident.name -> stype -> var_i

val is_reg_ptr_expr :
  (instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident) ->
  instr_info -> uint -> bool -> Ident.Ident.name -> stype -> pexpr -> var_i
  option

val is_reg_ptr_lval :
  (instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident) ->
  instr_info -> uint -> bool -> Ident.Ident.name -> stype -> lval -> var_i
  option

val make_prologue :
  'a1 asmOp -> (instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident)
  -> instr_info -> SvExtra.Sv.t -> uint ->
  ((bool * Ident.Ident.name) * stype) list -> pexpr list -> (pp_error_loc,
  'a1 instr list * pexpr list) result

type pseudo_instr =
| PI_lv of lval
| PI_i of lval * stype * var_i

val make_pseudo_epilogue :
  (instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident) ->
  instr_info -> SvExtra.Sv.t -> uint -> ((bool * Ident.Ident.name) * stype)
  list -> lval list -> (pp_error_loc, pseudo_instr list) result

val mk_ep_i : 'a1 asmOp -> instr_info -> lval -> stype -> var_i -> 'a1 instr

val wf_lv : lval -> bool

val swapable :
  'a1 asmOp -> instr_info -> pseudo_instr list -> (pp_error_loc, lval
  list * 'a1 instr list) result

val make_epilogue :
  'a1 asmOp -> (instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident)
  -> instr_info -> SvExtra.Sv.t -> ((bool * Ident.Ident.name) * stype) list
  -> lval list -> (pp_error_loc, lval list * 'a1 instr list) result

val update_c :
  'a1 asmOp -> ('a1 instr -> 'a1 instr list cexec) -> 'a1 instr list ->
  (pp_error_loc, 'a1 instr list) result

val mk_info : var_i -> stype -> (bool * Ident.Ident.name) * stype

val get_sig :
  'a1 asmOp -> 'a1 uprog -> funname -> ((bool * Ident.Ident.name) * stype)
  list * ((bool * Ident.Ident.name) * stype) list

val get_syscall_sig :
  BinNums.positive Syscall_t.syscall_t -> ((bool * Ident.Ident.name) * stype)
  list * ((bool * Ident.Ident.name) * stype) list

val update_i :
  'a1 asmOp -> (instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident)
  -> 'a1 uprog -> SvExtra.Sv.t -> 'a1 instr -> 'a1 instr list cexec

val update_fd :
  'a1 asmOp -> (instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident)
  -> 'a1 uprog -> 'a1 ufundef -> (pp_error_loc, ('a1, extra_fun_t) _fundef)
  result

val makereference_prog :
  'a1 asmOp -> (instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident)
  -> 'a1 uprog -> 'a1 uprog cexec
