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

(** val syscall_kill : one_varmap_info -> SvExtra.Sv.t **)

let syscall_kill ovm_i =
  SvExtra.Sv.diff ovm_i.all_vars ovm_i.callee_saved

(** val magic_variables :
    coq_PointerData -> 'a1 asmOp -> 'a1 sprog -> SvExtra.Sv.t **)

let magic_variables pd _ p =
  let vgd =
    (mk_var_i { Var.vtype = (Coq_sword (coq_Uptr pd)); Var.vname =
      (Obj.magic p).p_extra.sp_rip }).v_var
  in
  let vrsp =
    (mk_var_i { Var.vtype = (Coq_sword (coq_Uptr pd)); Var.vname =
      (Obj.magic p).p_extra.sp_rsp }).v_var
  in
  SvExtra.Sv.add (Obj.magic vgd) (SvExtra.Sv.singleton (Obj.magic vrsp))

(** val savedstackreg : saved_stack -> SvExtra.Sv.t **)

let savedstackreg = function
| SavedStackReg r -> SvExtra.Sv.singleton (Obj.magic r)
| _ -> SvExtra.Sv.empty

(** val saved_stack_vm :
    'a1 asmOp -> ('a1, stk_fun_extra) _fundef -> SvExtra.Sv.t **)

let saved_stack_vm _ fd =
  savedstackreg fd.f_extra.sf_save_stack

(** val ra_vm :
    one_varmap_info -> stk_fun_extra -> SvExtra.Sv.t -> SvExtra.Sv.t **)

let ra_vm ovm_i e tmp =
  match e.sf_return_address with
  | RAnone -> SvExtra.Sv.union tmp ovm_i.vflags
  | RAreg (ra, _) -> SvExtra.Sv.singleton (Obj.magic ra)
  | RAstack (ra, _, _) ->
    (match ra with
     | Some ra0 -> SvExtra.Sv.singleton (Obj.magic ra0)
     | None -> SvExtra.Sv.empty)

(** val ra_undef :
    'a1 asmOp -> one_varmap_info -> ('a1, stk_fun_extra) _fundef ->
    SvExtra.Sv.t -> SvExtra.Sv.t **)

let ra_undef asmop ovm_i fd tmp =
  SvExtra.Sv.union (ra_vm ovm_i fd.f_extra tmp) (saved_stack_vm asmop fd)

(** val tmp_call : stk_fun_extra -> SvExtra.Sv.t **)

let tmp_call e =
  match e.sf_return_address with
  | RAnone -> SvExtra.Sv.empty
  | RAreg (_, o) ->
    (match o with
     | Some r -> SvExtra.Sv.singleton (Obj.magic r)
     | None -> SvExtra.Sv.empty)
  | RAstack (_, _, o0) ->
    (match o0 with
     | Some r -> SvExtra.Sv.singleton (Obj.magic r)
     | None -> SvExtra.Sv.empty)

(** val fd_tmp_call :
    coq_PointerData -> 'a1 asmOp -> 'a1 sprog -> funname -> SvExtra.Sv.t **)

let fd_tmp_call _ _ p f =
  match get_fundef p.p_funcs f with
  | Some fd -> tmp_call (Obj.magic fd).f_extra
  | None -> SvExtra.Sv.empty
