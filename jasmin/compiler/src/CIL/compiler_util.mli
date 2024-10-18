open BinNums
open Datatypes
open Expr
open Fexpr
open Seq
open Sopn
open Utils0
open Var0

type __ = Obj.t

type warning_msg =
| Use_lea

type box =
| Vbox
| Hbox
| HoVbox
| Nobox

type pp_error =
| PPEstring of char list
| PPEz of coq_Z
| PPEvar of Var.var
| PPEvarinfo of var_info
| PPElval of lval
| PPEfunname of funname
| PPEfuninfo of fun_info
| PPEiinfo of instr_info
| PPEexpr of pexpr
| PPErexpr of rexpr
| PPEfexpr of fexpr
| PPEbox of box * pp_error list
| PPEbreak

type pp_error_loc = { pel_msg : pp_error; pel_fn : funname option;
                      pel_fi : fun_info option; pel_ii : instr_info option;
                      pel_vi : var_info option; pel_pass : char list option;
                      pel_internal : bool }

val pp_hov : pp_error list -> pp_error

val pp_box : pp_error list -> pp_error

val pp_vbox : pp_error list -> pp_error

val pp_nobox : pp_error list -> pp_error

val pp_list : pp_error -> ('a1 -> pp_error) -> 'a1 list -> pp_error

val pp_break : pp_error -> pp_error

val pp_break_s : char list -> pp_error

val pp_Sv : SvExtra.Sv.t -> pp_error

type 'a cexec = (pp_error_loc, 'a) result

val pp_at_ii : instr_info -> pp_error_loc -> pp_error_loc

val add_iinfo : instr_info -> 'a1 cexec -> (pp_error_loc, 'a1) result

val pp_at_fi : fun_info -> pp_error_loc -> pp_error_loc

val add_finfo : fun_info -> 'a1 cexec -> 'a1 cexec

val pp_at_fn : funname -> pp_error_loc -> pp_error_loc

val add_funname : funname -> 'a1 cexec -> 'a1 cexec

val map_prog_name :
  'a1 asmOp -> progT -> (funname -> 'a1 fundef -> 'a1 fundef) -> 'a1 prog ->
  'a1 prog

val map_prog :
  'a1 asmOp -> progT -> ('a1 fundef -> 'a1 fundef) -> 'a1 prog -> 'a1 prog

val map_cfprog_name_gen :
  ('a1 -> fun_info) -> (funname -> 'a1 -> 'a2 cexec) -> (funname * 'a1) list
  -> (pp_error_loc, (funname * 'a2) list) result

val map_cfprog_gen :
  ('a1 -> fun_info) -> ('a1 -> 'a2 cexec) -> (funname * 'a1) list ->
  (pp_error_loc, (funname * 'a2) list) result

val pp_internal_error : char list -> pp_error -> pp_error_loc

val pp_internal_error_s : char list -> char list -> pp_error_loc

val pp_internal_error_s_at :
  char list -> instr_info -> char list -> pp_error_loc

module type LoopCounter =
 sig
  val nb : nat
 end

module Loop :
 LoopCounter

val gen_loop_iterator : char list -> instr_info option -> pp_error_loc

val loop_iterator : char list -> pp_error_loc

val ii_loop_iterator : char list -> instr_info -> pp_error_loc
