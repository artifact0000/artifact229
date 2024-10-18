open BinNums
open Expr
open Ssrfun
open Type
open Var0
open Wsize

type fexpr =
| Fconst of coq_Z
| Fvar of var_i
| Fapp1 of sop1 * fexpr
| Fapp2 of sop2 * fexpr * fexpr
| Fif of fexpr * fexpr * fexpr

val fconst : wsize -> coq_Z -> fexpr

type rexpr =
| Load of wsize * var_i * fexpr
| Rexpr of fexpr

type lexpr =
| Store of wsize * var_i * fexpr
| LLvar of var_i

val fexpr_of_pexpr : pexpr -> fexpr option

val rexpr_of_pexpr : pexpr -> rexpr option

val lexpr_of_lval : lval -> lexpr option

val free_vars_rec : SvExtra.Sv.t -> fexpr -> SvExtra.Sv.t

val free_vars : fexpr -> SvExtra.Sv.t

val free_vars_r : rexpr -> SvExtra.Sv.t

val rvar : var_i -> rexpr

val rconst : wsize -> coq_Z -> rexpr

module FopnArgs :
 sig
  type lval = lexpr

  type rval = rexpr

  val lvar : var_i -> lexpr

  val lmem : coq_PointerData -> wsize -> var_i -> coq_Z -> lexpr

  val rvar : var_i -> rexpr

  val rconst : wsize -> coq_Z -> rexpr
 end
