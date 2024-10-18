open BinInt
open BinNums
open Arch_decl
open Arch_extra
open Arm_decl
open Arm_extra
open Arm_instr_decl
open Arm_params_core
open Expr
open Fexpr
open Seq
open Sopn
open Word0
open Wsize

type __ = Obj.t

module ARMOpn :
 functor (Args:OpnArgs) ->
 sig
  module Core :
   sig
    type opn_args = (Args.lval list * arm_op) * Args.rval list

    val mov : var_i -> var_i -> opn_args

    val add : var_i -> var_i -> var_i -> opn_args

    val sub : var_i -> var_i -> var_i -> opn_args

    val movi : var_i -> coq_Z -> opn_args

    val movt : var_i -> coq_Z -> opn_args

    val addi : var_i -> var_i -> coq_Z -> opn_args

    val subi : var_i -> var_i -> coq_Z -> opn_args

    val li : var_i -> coq_Z -> opn_args list

    val smart_mov : var_i -> var_i -> opn_args list

    val gen_smart_opi :
      (var_i -> var_i -> var_i -> opn_args) -> (var_i -> var_i -> coq_Z ->
      opn_args) -> (coq_Z -> bool) -> coq_Z option -> var_i -> var_i -> var_i
      -> coq_Z -> opn_args list

    val smart_addi : var_i -> var_i -> coq_Z -> opn_args list

    val smart_subi : var_i -> var_i -> coq_Z -> opn_args list

    val gen_smart_opi_tmp :
      (var_i -> var_i -> var_i -> opn_args) -> (var_i -> var_i -> coq_Z ->
      opn_args) -> var_i -> var_i -> coq_Z -> opn_args list

    val smart_addi_tmp : var_i -> var_i -> coq_Z -> opn_args list

    val smart_subi_tmp : var_i -> var_i -> coq_Z -> opn_args list
   end

  val to_opn :
    (register, __, __, rflag, condt) arch_toIdent -> ((Args.lval
    list * arm_op) * Args.rval list) -> (Args.lval list * arm_extended_op
    sopn) * Args.rval list

  val mov :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
    (Args.lval list * arm_extended_op sopn) * Args.rval list

  val add :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> var_i
    -> (Args.lval list * arm_extended_op sopn) * Args.rval list

  val sub :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> var_i
    -> (Args.lval list * arm_extended_op sopn) * Args.rval list

  val movi :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z ->
    (Args.lval list * arm_extended_op sopn) * Args.rval list

  val movt :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z ->
    (Args.lval list * arm_extended_op sopn) * Args.rval list

  val addi :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> (Args.lval list * arm_extended_op sopn) * Args.rval list

  val subi :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> (Args.lval list * arm_extended_op sopn) * Args.rval list

  val bici :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> (Args.lval list * (register, __, __, rflag, condt, arm_op,
    arm_extra_op) extended_op sopn) * Args.rval list

  val str :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> (Args.lval list * arm_extended_op sopn) * Args.rval list

  val align :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> wsize
    -> (Args.lval list * (register, __, __, rflag, condt, arm_op,
    arm_extra_op) extended_op sopn) * Args.rval list

  val li :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z ->
    ((Args.lval list * arm_extended_op sopn) * Args.rval list) list

  val smart_mov :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
    ((Args.lval list * arm_extended_op sopn) * Args.rval list) list

  val smart_addi :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> ((Args.lval list * arm_extended_op sopn) * Args.rval list) list

  val smart_subi :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> ((Args.lval list * arm_extended_op sopn) * Args.rval list) list

  val smart_addi_tmp :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> ((Args.lval list * arm_extended_op sopn) * Args.rval list) list

  val smart_subi_tmp :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> ((Args.lval list * arm_extended_op sopn) * Args.rval list) list
 end

module ARMFopn :
 sig
  module Core :
   sig
    type opn_args = (FopnArgs.lval list * arm_op) * FopnArgs.rval list

    val mov : var_i -> var_i -> opn_args

    val add : var_i -> var_i -> var_i -> opn_args

    val sub : var_i -> var_i -> var_i -> opn_args

    val movi : var_i -> coq_Z -> opn_args

    val movt : var_i -> coq_Z -> opn_args

    val addi : var_i -> var_i -> coq_Z -> opn_args

    val subi : var_i -> var_i -> coq_Z -> opn_args

    val li : var_i -> coq_Z -> opn_args list

    val smart_mov : var_i -> var_i -> opn_args list

    val gen_smart_opi :
      (var_i -> var_i -> var_i -> opn_args) -> (var_i -> var_i -> coq_Z ->
      opn_args) -> (coq_Z -> bool) -> coq_Z option -> var_i -> var_i -> var_i
      -> coq_Z -> opn_args list

    val smart_addi : var_i -> var_i -> coq_Z -> opn_args list

    val smart_subi : var_i -> var_i -> coq_Z -> opn_args list

    val gen_smart_opi_tmp :
      (var_i -> var_i -> var_i -> opn_args) -> (var_i -> var_i -> coq_Z ->
      opn_args) -> var_i -> var_i -> coq_Z -> opn_args list

    val smart_addi_tmp : var_i -> var_i -> coq_Z -> opn_args list

    val smart_subi_tmp : var_i -> var_i -> coq_Z -> opn_args list
   end

  val to_opn :
    (register, __, __, rflag, condt) arch_toIdent -> ((FopnArgs.lval
    list * arm_op) * FopnArgs.rval list) -> (FopnArgs.lval
    list * arm_extended_op sopn) * FopnArgs.rval list

  val mov :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
    (FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list

  val add :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> var_i
    -> (FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list

  val sub :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> var_i
    -> (FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list

  val movi :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z ->
    (FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list

  val movt :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z ->
    (FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list

  val addi :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> (FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list

  val subi :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> (FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list

  val bici :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> (FopnArgs.lval list * (register, __, __, rflag, condt, arm_op,
    arm_extra_op) extended_op sopn) * FopnArgs.rval list

  val str :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> (FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list

  val align :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> wsize
    -> (FopnArgs.lval list * (register, __, __, rflag, condt, arm_op,
    arm_extra_op) extended_op sopn) * FopnArgs.rval list

  val li :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z ->
    ((FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list) list

  val smart_mov :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
    ((FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list) list

  val smart_addi :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> ((FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list) list

  val smart_subi :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> ((FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list) list

  val smart_addi_tmp :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> ((FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list) list

  val smart_subi_tmp :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> ((FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list) list
 end
