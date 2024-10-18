open Compiler_util
open Expr
open Seq
open Sopn
open Type
open Utils0
open Var0

type fresh_vars = Ident.Ident.name -> stype -> Ident.Ident.ident

(** val disj_fvars : SvExtra.Sv.t -> SvExtra.Sv.t -> bool **)

let disj_fvars fvars x =
  SvExtra.disjoint x fvars

(** val fvars_correct :
    'a1 asmOp -> progT -> Ident.Ident.ident list -> SvExtra.Sv.t -> 'a1
    fun_decl list -> bool **)

let fvars_correct asmop pT all_fresh_vars fvars fds =
  (&&) (disj_fvars fvars (vars_p asmop pT fds))
    (uniq Ident.ident_eqType (Obj.magic all_fresh_vars))

(** val is_lval_in_memory : lval -> bool **)

let is_lval_in_memory = function
| Lnone (_, _) -> false
| Lvar v -> is_var_in_memory v.v_var
| Lmem (_, _, _) -> true
| Laset (_, _, v, _) -> is_var_in_memory v.v_var
| Lasub (_, _, _, v, _) -> is_var_in_memory v.v_var

(** val lower_cmd :
    'a1 asmOp -> ('a2 -> (instr_info -> warning_msg -> instr_info) ->
    fresh_vars -> 'a1 instr -> 'a1 instr list) -> 'a2 -> (instr_info ->
    warning_msg -> instr_info) -> fresh_vars -> 'a1 instr list -> 'a1 instr
    list **)

let lower_cmd _ lower_i0 options warning fv c =
  conc_map (lower_i0 options warning fv) c

(** val lower_fd :
    'a1 asmOp -> ('a2 -> (instr_info -> warning_msg -> instr_info) ->
    fresh_vars -> 'a1 instr -> 'a1 instr list) -> 'a2 -> (instr_info ->
    warning_msg -> instr_info) -> fresh_vars -> progT -> 'a1 fundef -> 'a1
    fundef **)

let lower_fd asmop lower_i0 options warning fv _ fd =
  { f_info = fd.f_info; f_tyin = fd.f_tyin; f_params = fd.f_params; f_body =
    (lower_cmd asmop lower_i0 options warning fv fd.f_body); f_tyout =
    fd.f_tyout; f_res = fd.f_res; f_extra = fd.f_extra }

(** val lower_prog :
    'a1 asmOp -> ('a2 -> (instr_info -> warning_msg -> instr_info) ->
    fresh_vars -> 'a1 instr -> 'a1 instr list) -> 'a2 -> (instr_info ->
    warning_msg -> instr_info) -> fresh_vars -> progT -> 'a1 prog -> 'a1 prog **)

let lower_prog asmop lower_i0 options warning fv pT p =
  map_prog asmop pT (lower_fd asmop lower_i0 options warning fv pT) p
