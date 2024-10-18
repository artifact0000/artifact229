open Datatypes
open Arch_decl
open Sem_type
open Seq
open Ssrnat
open Type
open Utils0
open Wsize

type __ = Obj.t

(** val of_empty : __ -> 'a1 **)

let of_empty _ =
  assert false (* absurd case *)

(** val eqTC_empty : __ eqTypeC **)

let eqTC_empty =
  { beq = of_empty; ceqP = (fun _ _ -> assert false (* absurd case *)) }

(** val finTC_empty : __ finTypeC **)

let finTC_empty =
  { _eqC = eqTC_empty; cenum = [] }

(** val empty_toS : stype -> __ coq_ToString **)

let empty_toS _ =
  { category = ('e'::('m'::('p'::('t'::('y'::[]))))); _finC = finTC_empty;
    to_string = of_empty }

(** val ak_reg_reg : i_args_kinds **)

let ak_reg_reg =
  ((CAreg :: []) :: ((CAreg :: []) :: [])) :: []

(** val ak_reg_imm : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> i_args_kinds **)

let ak_reg_imm ad =
  ((CAreg :: []) :: (((CAimm ad.reg_size) :: []) :: [])) :: []

(** val ak_reg_addr : i_args_kinds **)

let ak_reg_addr =
  ((CAreg :: []) :: (((CAmem true) :: []) :: [])) :: []

(** val ak_reg_imm8_imm8 : i_args_kinds **)

let ak_reg_imm8_imm8 =
  ((CAreg :: []) :: (((CAimm U8) :: []) :: (((CAimm U8) :: []) :: []))) :: []

(** val ak_reg_reg_reg : i_args_kinds **)

let ak_reg_reg_reg =
  ((CAreg :: []) :: ((CAreg :: []) :: ((CAreg :: []) :: []))) :: []

(** val ak_reg_reg_imm :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> i_args_kinds **)

let ak_reg_reg_imm ad =
  ((CAreg :: []) :: ((CAreg :: []) :: (((CAimm
    ad.reg_size) :: []) :: []))) :: []

(** val ak_reg_reg_imm8 : i_args_kinds **)

let ak_reg_reg_imm8 =
  ((CAreg :: []) :: ((CAreg :: []) :: (((CAimm U8) :: []) :: []))) :: []

(** val ak_reg_reg_imm16 : i_args_kinds **)

let ak_reg_reg_imm16 =
  ((CAreg :: []) :: ((CAreg :: []) :: (((CAimm U16) :: []) :: []))) :: []

(** val ak_reg_reg_imm8_imm8 : i_args_kinds **)

let ak_reg_reg_imm8_imm8 =
  ((CAreg :: []) :: ((CAreg :: []) :: (((CAimm U8) :: []) :: (((CAimm
    U8) :: []) :: [])))) :: []

(** val ak_reg_reg_reg_reg : i_args_kinds **)

let ak_reg_reg_reg_reg =
  ((CAreg :: []) :: ((CAreg :: []) :: ((CAreg :: []) :: ((CAreg :: []) :: [])))) :: []

(** val semi_drop2 :
    stype list -> stype list -> sem_tuple exec sem_prod -> sem_tuple exec
    sem_prod **)

let semi_drop2 tin tout semi =
  behead_tuple tin (behead tout) (behead_tuple tin tout semi)

(** val semi_drop3 :
    stype list -> stype list -> sem_tuple exec sem_prod -> sem_tuple exec
    sem_prod **)

let semi_drop3 tin tout semi =
  behead_tuple tin (behead (behead tout))
    (behead_tuple tin (behead tout) (behead_tuple tin tout semi))

(** val semi_drop4 :
    stype list -> stype list -> sem_tuple exec sem_prod -> sem_tuple exec
    sem_prod **)

let semi_drop4 tin tout semi =
  behead_tuple tin (behead (behead (behead tout)))
    (behead_tuple tin (behead (behead tout))
      (behead_tuple tin (behead tout) (behead_tuple tin tout semi)))

(** val idt_drop2 :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    instr_desc_t -> ('a1, 'a2, 'a3, 'a4, 'a5) instr_desc_t **)

let idt_drop2 _ idt =
  { id_msb_flag = idt.id_msb_flag; id_tin = idt.id_tin; id_in = idt.id_in;
    id_tout = (iter (S (S O)) behead idt.id_tout); id_out =
    (iter (S (S O)) behead idt.id_out); id_semi =
    (semi_drop2 idt.id_tin idt.id_tout idt.id_semi); id_args_kinds =
    idt.id_args_kinds; id_nargs = idt.id_nargs; id_str_jas = idt.id_str_jas;
    id_safe = idt.id_safe; id_pp_asm = idt.id_pp_asm }

(** val idt_drop3 :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    instr_desc_t -> ('a1, 'a2, 'a3, 'a4, 'a5) instr_desc_t **)

let idt_drop3 _ idt =
  { id_msb_flag = idt.id_msb_flag; id_tin = idt.id_tin; id_in = idt.id_in;
    id_tout = (iter (S (S (S O))) behead idt.id_tout); id_out =
    (iter (S (S (S O))) behead idt.id_out); id_semi =
    (semi_drop3 idt.id_tin idt.id_tout idt.id_semi); id_args_kinds =
    idt.id_args_kinds; id_nargs = idt.id_nargs; id_str_jas = idt.id_str_jas;
    id_safe = idt.id_safe; id_pp_asm = idt.id_pp_asm }

(** val idt_drop4 :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    instr_desc_t -> ('a1, 'a2, 'a3, 'a4, 'a5) instr_desc_t **)

let idt_drop4 _ idt =
  { id_msb_flag = idt.id_msb_flag; id_tin = idt.id_tin; id_in = idt.id_in;
    id_tout = (iter (S (S (S (S O)))) behead idt.id_tout); id_out =
    (iter (S (S (S (S O)))) behead idt.id_out); id_semi =
    (semi_drop4 idt.id_tin idt.id_tout idt.id_semi); id_args_kinds =
    idt.id_args_kinds; id_nargs = idt.id_nargs; id_str_jas = idt.id_str_jas;
    id_safe = idt.id_safe; id_pp_asm = idt.id_pp_asm }

(** val rtuple_drop5th :
    stype -> stype -> stype -> stype -> stype -> sem_tuple exec -> (error,
    sem_ot * (sem_ot * (sem_ot * sem_ot))) result **)

let rtuple_drop5th _ _ _ _ _ = function
| Ok x ->
  let (x0, y) = Obj.magic x in
  let (x1, y0) = y in
  let (x2, y1) = y0 in let (x3, _) = y1 in Ok (x0, (x1, (x2, x3)))
| Error s -> Error s
