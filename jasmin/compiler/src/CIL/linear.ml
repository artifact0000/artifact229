open BinInt
open BinNums
open Datatypes
open Expr
open Fexpr
open Label
open Sopn
open Ssralg
open Type
open Var0
open Word0
open Wsize

type 'asm_op linstr_r =
| Lopn of lexpr list * 'asm_op sopn * rexpr list
| Lsyscall of BinNums.positive Syscall_t.syscall_t
| Lcall of var_i option * remote_label
| Lret
| Lalign
| Llabel of label_kind * label
| Lgoto of remote_label
| Ligoto of rexpr
| LstoreLabel of Var.var * label
| Lcond of fexpr * label

type 'asm_op linstr = { li_ii : instr_info; li_i : 'asm_op linstr_r }

type 'asm_op lcmd = 'asm_op linstr list

type 'asm_op lfundef = { lfd_info : fun_info; lfd_align : wsize;
                         lfd_tyin : stype list; lfd_arg : var_i list;
                         lfd_body : 'asm_op lcmd; lfd_tyout : stype list;
                         lfd_res : var_i list; lfd_export : bool;
                         lfd_callee_saved : Var.var list;
                         lfd_stk_max : coq_Z; lfd_frame_size : coq_Z }

(** val with_lbody : 'a1 asmOp -> 'a1 lfundef -> 'a1 lcmd -> 'a1 lfundef **)

let with_lbody _ lfd lbody =
  { lfd_info = lfd.lfd_info; lfd_align = lfd.lfd_align; lfd_tyin =
    lfd.lfd_tyin; lfd_arg = lfd.lfd_arg; lfd_body = lbody; lfd_tyout =
    lfd.lfd_tyout; lfd_res = lfd.lfd_res; lfd_export = lfd.lfd_export;
    lfd_callee_saved = lfd.lfd_callee_saved; lfd_stk_max = lfd.lfd_stk_max;
    lfd_frame_size = lfd.lfd_frame_size }

(** val lfd_total_stack : 'a1 asmOp -> 'a1 lfundef -> coq_Z **)

let lfd_total_stack _ lfd =
  if lfd.lfd_export
  then Z.sub (Z.add lfd.lfd_stk_max (wsize_size lfd.lfd_align)) (Zpos Coq_xH)
  else lfd.lfd_stk_max

type 'asm_op lprog = { lp_rip : Ident.Ident.ident;
                       lp_rsp : Ident.Ident.ident;
                       lp_globs : GRing.ComRing.sort list;
                       lp_funcs : (funname * 'asm_op lfundef) list }

(** val with_lfds :
    'a1 asmOp -> 'a1 lprog -> (funname * 'a1 lfundef) list -> 'a1 lprog **)

let with_lfds _ lp lfds =
  { lp_rip = lp.lp_rip; lp_rsp = lp.lp_rsp; lp_globs = lp.lp_globs;
    lp_funcs = lfds }

(** val lir_of_fopn_args :
    'a1 asmOp -> ((lexpr list * 'a1 sopn) * rexpr list) -> 'a1 linstr_r **)

let lir_of_fopn_args _ args =
  Lopn ((fst (fst args)), (snd (fst args)), (snd args))

(** val li_of_fopn_args :
    'a1 asmOp -> instr_info -> ((lexpr list * 'a1 sopn) * rexpr list) -> 'a1
    linstr **)

let li_of_fopn_args asmop ii args =
  { li_ii = ii; li_i = (lir_of_fopn_args asmop args) }
