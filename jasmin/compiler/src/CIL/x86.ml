open Datatypes
open Arch_decl
open Eqtype
open Utils0
open X86_decl
open X86_instr_decl

(** val x86_eval_cond :
    (rflag -> (error, bool) result) -> condt -> (error, bool) result **)

let x86_eval_cond get = function
| O_ct -> get OF
| NO_ct -> (match get OF with
            | Ok x -> Ok (negb x)
            | Error s -> Error s)
| B_ct -> get CF
| NB_ct -> (match get CF with
            | Ok x -> Ok (negb x)
            | Error s -> Error s)
| E_ct -> get ZF
| NE_ct -> (match get ZF with
            | Ok x -> Ok (negb x)
            | Error s -> Error s)
| BE_ct ->
  (match get CF with
   | Ok x -> (match get ZF with
              | Ok x0 -> Ok ((||) x x0)
              | Error s -> Error s)
   | Error s -> Error s)
| NBE_ct ->
  (match get CF with
   | Ok x ->
     (match get ZF with
      | Ok x0 -> Ok ((&&) (negb x) (negb x0))
      | Error s -> Error s)
   | Error s -> Error s)
| S_ct -> get SF
| NS_ct -> (match get SF with
            | Ok x -> Ok (negb x)
            | Error s -> Error s)
| P_ct -> get PF
| NP_ct -> (match get PF with
            | Ok x -> Ok (negb x)
            | Error s -> Error s)
| L_ct ->
  (match get SF with
   | Ok x ->
     (match get OF with
      | Ok x0 -> Ok (negb (eq_op bool_eqType (Obj.magic x) (Obj.magic x0)))
      | Error s -> Error s)
   | Error s -> Error s)
| NL_ct ->
  (match get SF with
   | Ok x ->
     (match get OF with
      | Ok x0 -> Ok (eq_op bool_eqType (Obj.magic x) (Obj.magic x0))
      | Error s -> Error s)
   | Error s -> Error s)
| LE_ct ->
  (match get ZF with
   | Ok x ->
     (match get SF with
      | Ok x0 ->
        (match get OF with
         | Ok x1 ->
           Ok
             ((||) x (negb (eq_op bool_eqType (Obj.magic x0) (Obj.magic x1))))
         | Error s -> Error s)
      | Error s -> Error s)
   | Error s -> Error s)
| NLE_ct ->
  (match get ZF with
   | Ok x ->
     (match get SF with
      | Ok x0 ->
        (match get OF with
         | Ok x1 ->
           Ok
             ((&&) (negb x) (eq_op bool_eqType (Obj.magic x0) (Obj.magic x1)))
         | Error s -> Error s)
      | Error s -> Error s)
   | Error s -> Error s)

(** val x86 :
    (register, register_ext, xmm_register, rflag, condt, x86_op) asm **)

let x86 =
  { _arch_decl = x86_decl; _asm_op_decl = x86_op_decl; eval_cond = (fun _ ->
    x86_eval_cond) }
