open Datatypes
open Compiler_util
open Eqtype
open Expr
open One_varmap
open Seq
open Sopn
open Ssrfun
open Type
open Utils0
open Var0
open Wsize

module E :
 sig
  val pass_name : char list

  val gen_error : bool -> instr_info option -> pp_error -> pp_error_loc

  val internal_error : instr_info -> char list -> pp_error_loc

  val ii_loop_iterator : instr_info -> pp_error_loc
 end

val writefun_ra :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1 sprog ->
  SvExtra.Sv.t -> (funname -> SvExtra.Sv.t) -> funname -> SvExtra.Sv.t

val writefun_ra_call :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1 sprog ->
  SvExtra.Sv.t -> (funname -> SvExtra.Sv.t) -> funname -> SvExtra.Sv.t

val write_I_rec :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1 sprog ->
  SvExtra.Sv.t -> (funname -> SvExtra.Sv.t) -> SvExtra.Sv.t -> 'a1 instr ->
  SvExtra.Sv.t

val write_c_rec :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1 sprog ->
  SvExtra.Sv.t -> (funname -> SvExtra.Sv.t) -> SvExtra.Sv.t -> 'a1 instr list
  -> SvExtra.Sv.t

val write_c :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1 sprog ->
  SvExtra.Sv.t -> (funname -> SvExtra.Sv.t) -> 'a1 instr list -> SvExtra.Sv.t

val write_fd :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1 sprog ->
  SvExtra.Sv.t -> (funname -> SvExtra.Sv.t) -> 'a1 sfundef -> SvExtra.Sv.t

val get_wmap : SvExtra.Sv.t Mf.t -> funname -> SvExtra.Sv.t

val mk_wmap :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1 sprog ->
  SvExtra.Sv.t -> SvExtra.Sv.t Mf.t

val check_wmap :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1 sprog ->
  SvExtra.Sv.t -> SvExtra.Sv.t Mf.t -> bool

val check_fv :
  instr_info -> SvExtra.Sv.t -> SvExtra.Sv.t -> (pp_error_loc, unit) result

val check_e :
  instr_info -> SvExtra.Sv.t -> pexpr -> (pp_error_loc, unit) result

val check_es :
  instr_info -> SvExtra.Sv.t -> pexpr list -> (pp_error_loc, unit) result

val check_c :
  'a1 asmOp -> (SvExtra.Sv.t -> 'a1 instr -> SvExtra.Sv.t cexec) ->
  SvExtra.Sv.t -> 'a1 instr list -> (pp_error_loc, SvExtra.Sv.t) result

val wloop :
  'a1 asmOp -> (SvExtra.Sv.t -> 'a1 instr -> SvExtra.Sv.t cexec) ->
  instr_info -> 'a1 instr list -> SvExtra.Sv.t -> 'a1 instr list -> nat ->
  SvExtra.Sv.t -> (pp_error_loc, SvExtra.Sv.t) result

val check_lv :
  instr_info -> SvExtra.Sv.t -> lval -> (pp_error_loc, SvExtra.Sv.t) result

val check_lvs :
  instr_info -> SvExtra.Sv.t -> lval list -> (pp_error_loc, SvExtra.Sv.t)
  result

val check_i :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1 sprog ->
  SvExtra.Sv.t -> (funname -> SvExtra.Sv.t) -> wsize -> SvExtra.Sv.t -> 'a1
  instr -> SvExtra.Sv.t cexec

val check_fd :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1 sprog ->
  SvExtra.Sv.t -> (funname -> SvExtra.Sv.t) -> funname -> 'a1 sfundef ->
  (pp_error_loc, unit) result

val check_prog :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1 sprog ->
  SvExtra.Sv.t -> (funname -> SvExtra.Sv.t) -> (pp_error_loc,
  (funname * unit) list) result

val check :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1 sprog ->
  SvExtra.Sv.t -> (pp_error_loc, unit) result
