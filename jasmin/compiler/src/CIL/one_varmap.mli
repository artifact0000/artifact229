open Expr
open Sopn
open Type
open Var0
open Wsize

type ovm_syscall_sig_t = { scs_vin : Var.var list; scs_vout : Var.var list }

type one_varmap_info = { syscall_sig : (BinNums.positive Syscall_t.syscall_t
                                       -> ovm_syscall_sig_t);
                         all_vars : SvExtra.Sv.t;
                         callee_saved : SvExtra.Sv.t; vflags : SvExtra.Sv.t }

val syscall_kill : one_varmap_info -> SvExtra.Sv.t

val magic_variables :
  coq_PointerData -> 'a1 asmOp -> 'a1 sprog -> SvExtra.Sv.t

val savedstackreg : saved_stack -> SvExtra.Sv.t

val saved_stack_vm : 'a1 asmOp -> ('a1, stk_fun_extra) _fundef -> SvExtra.Sv.t

val ra_vm : one_varmap_info -> stk_fun_extra -> SvExtra.Sv.t -> SvExtra.Sv.t

val ra_undef :
  'a1 asmOp -> one_varmap_info -> ('a1, stk_fun_extra) _fundef ->
  SvExtra.Sv.t -> SvExtra.Sv.t

val tmp_call : stk_fun_extra -> SvExtra.Sv.t

val fd_tmp_call :
  coq_PointerData -> 'a1 asmOp -> 'a1 sprog -> funname -> SvExtra.Sv.t
