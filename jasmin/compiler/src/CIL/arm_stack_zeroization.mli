open BinInt
open BinNums
open Arch_decl
open Arch_extra
open Arm_decl
open Arm_extra
open Arm_instr_decl
open Arm_params_common
open Compiler_util
open Expr
open Fexpr
open Label
open Linear
open Seq
open Stack_zero_strategy
open Type
open Utils0
open Var0
open Word0
open Wsize

type __ = Obj.t

val sz_init :
  (register, __, __, rflag, condt) arch_toIdent -> var_i -> wsize -> coq_Z ->
  (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op lcmd

val store_zero :
  (register, __, __, rflag, condt) arch_toIdent -> var_i -> wsize -> fexpr ->
  (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op linstr_r

val sz_loop :
  (register, __, __, rflag, condt) arch_toIdent -> var_i -> label -> wsize ->
  (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op lcmd

val restore_sp :
  (register, __, __, rflag, condt) arch_toIdent -> var_i -> arm_extended_op
  linstr list

val stack_zero_loop :
  (register, __, __, rflag, condt) arch_toIdent -> var_i -> label -> wsize ->
  wsize -> coq_Z -> (register, __, __, rflag, condt, arm_op, arm_extra_op)
  extended_op lcmd

val stack_zero_loop_vars :
  (register, __, __, rflag, condt) arch_toIdent -> SvExtra.Sv.t

val sz_unrolled :
  (register, __, __, rflag, condt) arch_toIdent -> var_i -> wsize -> coq_Z ->
  (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op lcmd

val stack_zero_unrolled :
  (register, __, __, rflag, condt) arch_toIdent -> var_i -> wsize -> wsize ->
  coq_Z -> (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op
  lcmd

val stack_zero_unrolled_vars :
  (register, __, __, rflag, condt) arch_toIdent -> SvExtra.Sv.t

val stack_zeroization_cmd :
  (register, __, __, rflag, condt) arch_toIdent -> stack_zero_strategy ->
  Ident.Ident.ident -> label -> wsize -> wsize -> coq_Z -> ((register, __,
  __, rflag, condt, arm_op, arm_extra_op) extended_op lcmd * SvExtra.Sv.t)
  cexec
