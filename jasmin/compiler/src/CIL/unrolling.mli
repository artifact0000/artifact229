open List0
open Expr
open Seq
open Sopn
open Var0

val map_repeat : ('a1 -> 'a2 * bool) -> 'a1 list -> 'a2 list * bool

val unroll_cmd :
  'a1 asmOp -> ('a1 instr -> 'a1 instr list * bool) -> 'a1 instr list -> 'a1
  instr list * bool

val assgn : 'a1 asmOp -> instr_info -> var_i -> pexpr -> 'a1 instr

val unroll_i : 'a1 asmOp -> 'a1 instr -> 'a1 instr list * bool

val unroll_fun :
  'a1 asmOp -> progT -> 'a1 fun_decl -> (funname * ('a1, extra_fun_t)
  _fundef) * bool

val unroll_prog : 'a1 asmOp -> progT -> 'a1 prog -> 'a1 prog * bool
