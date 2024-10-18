open BinInt
open BinNums
open Datatypes
open String0
open Compiler_util
open Expr
open Label
open Linear
open Linear_util
open Memory_model
open One_varmap
open Seq
open Sopn
open Stack_zero_strategy
open Type
open Utils0
open Var0
open Warray_
open Word_ssrZ
open Wsize

module E :
 sig
  val pass : char list

  val error : pp_error -> pp_error_loc
 end

type 'asm_op stack_zeroization_params =
  stack_zero_strategy -> Ident.Ident.ident -> label -> wsize -> wsize ->
  coq_Z -> ('asm_op lcmd * SvExtra.Sv.t) cexec
  (* singleton inductive, whose constructor was Build_stack_zeroization_params *)

val szp_cmd :
  'a1 asmOp -> 'a1 stack_zeroization_params -> stack_zero_strategy ->
  Ident.Ident.ident -> label -> wsize -> wsize -> coq_Z -> ('a1
  lcmd * SvExtra.Sv.t) cexec

val stack_zeroization_lfd_body :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1
  stack_zeroization_params -> Ident.Ident.ident -> 'a1 lfundef ->
  stack_zero_strategy -> wsize -> 'a1 lfundef cexec

val stack_zeroization_lfd :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1
  stack_zeroization_params -> (funname -> (stack_zero_strategy * wsize)
  option) -> Ident.Ident.ident -> funname -> 'a1 lfundef -> 'a1 lfundef cexec

val stack_zeroization_lprog :
  coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1
  stack_zeroization_params -> (funname -> (stack_zero_strategy * wsize)
  option) -> 'a1 lprog -> 'a1 lprog cexec
