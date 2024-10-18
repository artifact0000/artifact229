open Datatypes
open Compiler_util
open Expr
open Seq
open Sopn
open Utils0
open Var0

module E :
 sig
  val pass : char list

  val dead_calls_error : char list -> pp_error_loc
 end

val i_calls : 'a1 asmOp -> Sf.t -> 'a1 instr -> Sf.t

val c_calls : 'a1 asmOp -> Sf.t -> 'a1 instr list -> Sf.t

val live_calls : 'a1 asmOp -> progT -> Sf.t -> 'a1 fun_decl list -> Sf.t

val dead_calls :
  'a1 asmOp -> progT -> Sf.t -> 'a1 fun_decl list -> (Sf.elt * 'a1 fundef)
  list

val dead_calls_err : 'a1 asmOp -> progT -> Sf.t -> 'a1 prog -> 'a1 prog cexec

val dead_calls_err_seq :
  'a1 asmOp -> progT -> funname list -> 'a1 prog -> 'a1 prog cexec
