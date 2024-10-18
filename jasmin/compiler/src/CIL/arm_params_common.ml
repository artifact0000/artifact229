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

module ARMOpn =
 functor (Args:OpnArgs) ->
 struct
  module Core = ARMOpn_core(Args)

  (** val to_opn :
      (register, __, __, rflag, condt) arch_toIdent -> ((Args.lval
      list * arm_op) * Args.rval list) -> (Args.lval list * arm_extended_op
      sopn) * Args.rval list **)

  let to_opn atoI = function
  | (y, e) -> let (d, o) = y in ((d, (coq_Oarm atoI o)), e)

  (** val mov :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
      (Args.lval list * arm_extended_op sopn) * Args.rval list **)

  let mov atoI x y =
    to_opn atoI (Core.mov x y)

  (** val add :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
      var_i -> (Args.lval list * arm_extended_op sopn) * Args.rval list **)

  let add atoI x y z =
    to_opn atoI (Core.add x y z)

  (** val sub :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
      var_i -> (Args.lval list * arm_extended_op sopn) * Args.rval list **)

  let sub atoI x y z =
    to_opn atoI (Core.sub x y z)

  (** val movi :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z ->
      (Args.lval list * arm_extended_op sopn) * Args.rval list **)

  let movi atoI x imm =
    to_opn atoI (Core.movi x imm)

  (** val movt :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z ->
      (Args.lval list * arm_extended_op sopn) * Args.rval list **)

  let movt atoI x imm =
    to_opn atoI (Core.movt x imm)

  (** val addi :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
      coq_Z -> (Args.lval list * arm_extended_op sopn) * Args.rval list **)

  let addi atoI x y imm =
    to_opn atoI (Core.addi x y imm)

  (** val subi :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
      coq_Z -> (Args.lval list * arm_extended_op sopn) * Args.rval list **)

  let subi atoI x y imm =
    to_opn atoI (Core.subi x y imm)

  (** val bici :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
      coq_Z -> (Args.lval list * (register, __, __, rflag, condt, arm_op,
      arm_extra_op) extended_op sopn) * Args.rval list **)

  let bici atoI =
    let op_gen = fun mn x res -> ((((Args.lvar x) :: []),
      (coq_Oarm atoI (ARM_op (mn, default_opts)))), res)
    in
    let mn = BIC in
    (fun x y imm ->
    op_gen mn x ((Args.rvar y) :: ((Args.rconst arm_decl.reg_size imm) :: [])))

  (** val str :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
      coq_Z -> (Args.lval list * arm_extended_op sopn) * Args.rval list **)

  let str atoI x y off =
    let lv = Args.lmem (arch_pd arm_decl) arm_decl.reg_size y off in
    (((lv :: []), (coq_Oarm atoI (ARM_op (STR, default_opts)))),
    ((Args.rvar x) :: []))

  (** val align :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
      wsize -> (Args.lval list * (register, __, __, rflag, condt, arm_op,
      arm_extra_op) extended_op sopn) * Args.rval list **)

  let align atoI x y al =
    bici atoI x y (Z.sub (wsize_size al) (Zpos Coq_xH))

  (** val li :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z ->
      ((Args.lval list * arm_extended_op sopn) * Args.rval list) list **)

  let li atoI x imm =
    map (to_opn atoI) (Core.li x imm)

  (** val smart_mov :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
      ((Args.lval list * arm_extended_op sopn) * Args.rval list) list **)

  let smart_mov atoI x y =
    map (to_opn atoI) (Core.smart_mov x y)

  (** val smart_addi :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
      coq_Z -> ((Args.lval list * arm_extended_op sopn) * Args.rval list) list **)

  let smart_addi atoI x y imm =
    map (to_opn atoI) (Core.smart_addi x y imm)

  (** val smart_subi :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
      coq_Z -> ((Args.lval list * arm_extended_op sopn) * Args.rval list) list **)

  let smart_subi atoI x y imm =
    map (to_opn atoI) (Core.smart_subi x y imm)

  (** val smart_addi_tmp :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
      coq_Z -> ((Args.lval list * arm_extended_op sopn) * Args.rval list) list **)

  let smart_addi_tmp atoI x tmp imm =
    map (to_opn atoI) (Core.smart_addi_tmp x tmp imm)

  (** val smart_subi_tmp :
      (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i ->
      coq_Z -> ((Args.lval list * arm_extended_op sopn) * Args.rval list) list **)

  let smart_subi_tmp atoI x tmp imm =
    map (to_opn atoI) (Core.smart_subi_tmp x tmp imm)
 end

module ARMFopn = ARMOpn(FopnArgs)
