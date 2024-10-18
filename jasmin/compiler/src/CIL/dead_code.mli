open Datatypes
open Compiler_util
open Eqtype
open Expr
open Seq
open Sopn
open Utils0
open Var0

module E :
 sig
  val pass : char list

  val ii_loop_iterator : instr_info -> pp_error_loc

  val dead_code_error : char list -> pp_error_loc
 end

val dead_code_c :
  'a1 asmOp -> ('a1 instr -> SvExtra.Sv.t -> (SvExtra.Sv.t * 'a1 instr
  option) cexec) -> 'a1 instr list -> SvExtra.Sv.t -> (SvExtra.Sv.t * 'a1
  instr list) cexec

val loop :
  'a1 asmOp -> (SvExtra.Sv.t -> (SvExtra.Sv.t * 'a1 instr list) cexec) ->
  instr_info -> nat -> SvExtra.Sv.t -> SvExtra.Sv.t -> SvExtra.Sv.t ->
  (SvExtra.Sv.t * 'a1 instr list) cexec

val wloop :
  'a1 asmOp -> (SvExtra.Sv.t -> (SvExtra.Sv.t * (SvExtra.Sv.t * ('a1 instr
  list * 'a1 instr list))) cexec) -> instr_info -> nat -> SvExtra.Sv.t ->
  (SvExtra.Sv.t * ('a1 instr list * 'a1 instr list)) cexec

val check_nop : lval -> pexpr -> bool

val check_nop_opn :
  'a1 asmOp -> ('a1 asm_op_t -> bool) -> lval list -> 'a1 sopn -> pexpr list
  -> bool

val keep_only : 'a1 list -> bool list -> 'a1 list

val fn_keep_only :
  (funname -> bool list option) -> funname -> 'a1 list -> 'a1 list

val check_keep_only :
  lval list -> bool list -> SvExtra.Sv.t -> (SvExtra.Sv.t * lval list) cexec

val dead_code_i :
  'a1 asmOp -> ('a1 asm_op_t -> bool) -> bool -> (funname -> bool list
  option) -> 'a1 instr -> SvExtra.Sv.t -> (SvExtra.Sv.t * 'a1 instr option)
  cexec

val dead_code_fd :
  'a1 asmOp -> ('a1 asm_op_t -> bool) -> bool -> (funname -> bool list
  option) -> funname -> ('a1, 'a2) _fundef -> ('a1, 'a2) _fundef cexec

val dead_code_prog_tokeep :
  'a1 asmOp -> ('a1 asm_op_t -> bool) -> bool -> (funname -> bool list
  option) -> progT -> 'a1 prog -> 'a1 prog cexec

val dead_code_prog :
  'a1 asmOp -> ('a1 asm_op_t -> bool) -> progT -> 'a1 prog -> bool -> 'a1
  prog cexec
