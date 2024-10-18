open BinInt
open BinNums
open Eqtype
open Expr
open Fexpr
open Ssrfun
open Word0
open Word_ssrZ
open Wsize

type lea = { lea_disp : coq_Z; lea_base : var_i option; lea_scale : coq_Z;
             lea_offset : var_i option }

val lea_const : coq_Z -> lea

val lea_var : var_i -> lea

val mkLea : coq_Z -> var_i option -> Equality.sort -> var_i option -> lea

val lea_mul : lea -> lea -> lea option

val lea_add : lea -> lea -> lea option

val lea_sub : lea -> lea -> lea option

val mk_lea_rec : wsize -> fexpr -> lea option

val mk_lea : wsize -> pexpr -> lea option
