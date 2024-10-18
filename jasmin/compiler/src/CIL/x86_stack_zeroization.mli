open BinInt
open BinNums
open Arch_decl
open Arch_extra
open Compiler_util
open Expr
open Fexpr
open Label
open Linear
open Seq
open Sopn
open Stack_zero_strategy
open Type
open Utils0
open Var0
open Word0
open Wsize
open X86_decl
open X86_extra
open X86_instr_decl

val loop_small_cmd :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  Ident.Ident.ident -> label -> wsize -> wsize -> coq_Z -> (register,
  register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op
  lcmd

val loop_small_vars :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  SvExtra.Sv.t

val loop_large_cmd :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  Ident.Ident.ident -> label -> wsize -> wsize -> coq_Z -> (register,
  register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op
  lcmd

val loop_large_vars :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  SvExtra.Sv.t

val x86_stack_zero_loop :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  Ident.Ident.ident -> label -> wsize -> wsize -> coq_Z -> (register,
  register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op
  lcmd * SvExtra.Sv.t

val x86_stack_zero_loopSCT :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  Ident.Ident.ident -> label -> wsize -> wsize -> coq_Z -> (register,
  register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op
  linstr list * SvExtra.Sv.t

val unrolled_small_cmd :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  Ident.Ident.ident -> wsize -> wsize -> coq_Z -> (register, register_ext,
  xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op lcmd

val unrolled_small_vars :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  SvExtra.Sv.t

val unrolled_large_cmd :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  Ident.Ident.ident -> wsize -> wsize -> coq_Z -> (register, register_ext,
  xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op lcmd

val unrolled_large_vars :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  SvExtra.Sv.t

val x86_stack_zero_unrolled :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  Ident.Ident.ident -> wsize -> wsize -> coq_Z -> (register, register_ext,
  xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op
  lcmd * SvExtra.Sv.t

val x86_stack_zero_cmd :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  stack_zero_strategy -> Ident.Ident.ident -> label -> wsize -> wsize ->
  coq_Z -> ((register, register_ext, xmm_register, rflag, condt, x86_op,
  x86_extra_op) extended_op lcmd * SvExtra.Sv.t) cexec
