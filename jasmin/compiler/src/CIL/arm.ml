open Datatypes
open Arch_decl
open Arm_decl
open Arm_instr_decl
open Eqtype
open Utils0

type __ = Obj.t

(** val arm_eval_cond :
    (rflag -> (error, bool) result) -> condt -> (error, bool) result **)

let arm_eval_cond get = function
| EQ_ct -> get ZF
| NE_ct -> (match get ZF with
            | Ok x -> Ok (negb x)
            | Error s -> Error s)
| CS_ct -> get CF
| CC_ct -> (match get CF with
            | Ok x -> Ok (negb x)
            | Error s -> Error s)
| MI_ct -> get NF
| PL_ct -> (match get NF with
            | Ok x -> Ok (negb x)
            | Error s -> Error s)
| VS_ct -> get VF
| VC_ct -> (match get VF with
            | Ok x -> Ok (negb x)
            | Error s -> Error s)
| HI_ct ->
  (match get CF with
   | Ok x ->
     (match get ZF with
      | Ok x0 -> Ok ((&&) x (negb x0))
      | Error s -> Error s)
   | Error s -> Error s)
| LS_ct ->
  (match get CF with
   | Ok x ->
     (match get ZF with
      | Ok x0 -> Ok ((||) (negb x) x0)
      | Error s -> Error s)
   | Error s -> Error s)
| GE_ct ->
  (match get NF with
   | Ok x ->
     (match get VF with
      | Ok x0 -> Ok (eq_op bool_eqType (Obj.magic x) (Obj.magic x0))
      | Error s -> Error s)
   | Error s -> Error s)
| LT_ct ->
  (match get NF with
   | Ok x ->
     (match get VF with
      | Ok x0 -> Ok (negb (eq_op bool_eqType (Obj.magic x) (Obj.magic x0)))
      | Error s -> Error s)
   | Error s -> Error s)
| GT_ct ->
  (match get ZF with
   | Ok x ->
     (match get NF with
      | Ok x0 ->
        (match get VF with
         | Ok x1 ->
           Ok
             ((&&) (negb x) (eq_op bool_eqType (Obj.magic x0) (Obj.magic x1)))
         | Error s -> Error s)
      | Error s -> Error s)
   | Error s -> Error s)
| LE_ct ->
  (match get ZF with
   | Ok x ->
     (match get NF with
      | Ok x0 ->
        (match get VF with
         | Ok x1 ->
           Ok
             ((||) x (negb (eq_op bool_eqType (Obj.magic x0) (Obj.magic x1))))
         | Error s -> Error s)
      | Error s -> Error s)
   | Error s -> Error s)

(** val arm : (register, __, __, rflag, condt, arm_op) asm **)

let arm =
  { _arch_decl = arm_decl; _asm_op_decl = arm_op_decl; eval_cond = (fun _ ->
    arm_eval_cond) }
