open BinInt
open BinNums
open Datatypes
open Arch_decl
open Arch_utils
open Eqtype
open Expr
open Fintype
open Flag_combination
open Seq
open Shift_kind
open Ssralg
open Ssrint
open Type
open Utils0
open Word0
open Word_ssrZ
open Wsize

type __ = Obj.t

(** val arm_reg_size : wsize **)

let arm_reg_size =
  U32

(** val arm_xreg_size : wsize **)

let arm_xreg_size =
  U64

type register =
| R00
| R01
| R02
| R03
| R04
| R05
| R06
| R07
| R08
| R09
| R10
| R11
| R12
| LR
| SP

(** val register_beq : register -> register -> bool **)

let register_beq x y =
  match x with
  | R00 -> (match y with
            | R00 -> true
            | _ -> false)
  | R01 -> (match y with
            | R01 -> true
            | _ -> false)
  | R02 -> (match y with
            | R02 -> true
            | _ -> false)
  | R03 -> (match y with
            | R03 -> true
            | _ -> false)
  | R04 -> (match y with
            | R04 -> true
            | _ -> false)
  | R05 -> (match y with
            | R05 -> true
            | _ -> false)
  | R06 -> (match y with
            | R06 -> true
            | _ -> false)
  | R07 -> (match y with
            | R07 -> true
            | _ -> false)
  | R08 -> (match y with
            | R08 -> true
            | _ -> false)
  | R09 -> (match y with
            | R09 -> true
            | _ -> false)
  | R10 -> (match y with
            | R10 -> true
            | _ -> false)
  | R11 -> (match y with
            | R11 -> true
            | _ -> false)
  | R12 -> (match y with
            | R12 -> true
            | _ -> false)
  | LR -> (match y with
           | LR -> true
           | _ -> false)
  | SP -> (match y with
           | SP -> true
           | _ -> false)

(** val register_eq_dec : register -> register -> bool **)

let register_eq_dec x y =
  let b = register_beq x y in if b then true else false

(** val register_eq_axiom : register Equality.axiom **)

let register_eq_axiom =
  eq_axiom_of_scheme register_beq

(** val eqTC_register : register eqTypeC **)

let eqTC_register =
  { beq = register_beq; ceqP = register_eq_axiom }

(** val arm_register_eqType : Equality.coq_type **)

let arm_register_eqType =
  ceqT_eqType eqTC_register

(** val registers : register list **)

let registers =
  R00 :: (R01 :: (R02 :: (R03 :: (R04 :: (R05 :: (R06 :: (R07 :: (R08 :: (R09 :: (R10 :: (R11 :: (R12 :: (LR :: (SP :: []))))))))))))))

(** val finTC_register : register finTypeC **)

let finTC_register =
  { _eqC = eqTC_register; cenum = registers }

(** val register_finType : Finite.coq_type **)

let register_finType =
  cfinT_finType finTC_register

(** val register_to_string : register -> char list **)

let register_to_string = function
| R00 -> 'r'::('0'::[])
| R01 -> 'r'::('1'::[])
| R02 -> 'r'::('2'::[])
| R03 -> 'r'::('3'::[])
| R04 -> 'r'::('4'::[])
| R05 -> 'r'::('5'::[])
| R06 -> 'r'::('6'::[])
| R07 -> 'r'::('7'::[])
| R08 -> 'r'::('8'::[])
| R09 -> 'r'::('9'::[])
| R10 -> 'r'::('1'::('0'::[]))
| R11 -> 'r'::('1'::('1'::[]))
| R12 -> 'r'::('1'::('2'::[]))
| LR -> 'l'::('r'::[])
| SP -> 's'::('p'::[])

(** val reg_toS : register coq_ToString **)

let reg_toS =
  { category = ('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[]))))))));
    _finC = finTC_register; to_string = register_to_string }

type rflag =
| NF
| ZF
| CF
| VF

(** val rflag_beq : rflag -> rflag -> bool **)

let rflag_beq x y =
  match x with
  | NF -> (match y with
           | NF -> true
           | _ -> false)
  | ZF -> (match y with
           | ZF -> true
           | _ -> false)
  | CF -> (match y with
           | CF -> true
           | _ -> false)
  | VF -> (match y with
           | VF -> true
           | _ -> false)

(** val rflag_eq_dec : rflag -> rflag -> bool **)

let rflag_eq_dec x y =
  let b = rflag_beq x y in if b then true else false

(** val rflag_eq_axiom : rflag Equality.axiom **)

let rflag_eq_axiom =
  eq_axiom_of_scheme rflag_beq

(** val eqTC_rflag : rflag eqTypeC **)

let eqTC_rflag =
  { beq = rflag_beq; ceqP = rflag_eq_axiom }

(** val rflag_eqType : Equality.coq_type **)

let rflag_eqType =
  ceqT_eqType eqTC_rflag

(** val rflags : rflag list **)

let rflags =
  NF :: (ZF :: (CF :: (VF :: [])))

(** val finTC_rflag : rflag finTypeC **)

let finTC_rflag =
  { _eqC = eqTC_rflag; cenum = rflags }

(** val rflag_finType : Finite.coq_type **)

let rflag_finType =
  cfinT_finType finTC_rflag

(** val flag_to_string : rflag -> char list **)

let flag_to_string = function
| NF -> 'N'::('F'::[])
| ZF -> 'Z'::('F'::[])
| CF -> 'C'::('F'::[])
| VF -> 'V'::('F'::[])

(** val rflag_toS : rflag coq_ToString **)

let rflag_toS =
  { category = ('r'::('f'::('l'::('a'::('g'::[]))))); _finC = finTC_rflag;
    to_string = flag_to_string }

type condt =
| EQ_ct
| NE_ct
| CS_ct
| CC_ct
| MI_ct
| PL_ct
| VS_ct
| VC_ct
| HI_ct
| LS_ct
| GE_ct
| LT_ct
| GT_ct
| LE_ct

(** val condt_beq : condt -> condt -> bool **)

let condt_beq x y =
  match x with
  | EQ_ct -> (match y with
              | EQ_ct -> true
              | _ -> false)
  | NE_ct -> (match y with
              | NE_ct -> true
              | _ -> false)
  | CS_ct -> (match y with
              | CS_ct -> true
              | _ -> false)
  | CC_ct -> (match y with
              | CC_ct -> true
              | _ -> false)
  | MI_ct -> (match y with
              | MI_ct -> true
              | _ -> false)
  | PL_ct -> (match y with
              | PL_ct -> true
              | _ -> false)
  | VS_ct -> (match y with
              | VS_ct -> true
              | _ -> false)
  | VC_ct -> (match y with
              | VC_ct -> true
              | _ -> false)
  | HI_ct -> (match y with
              | HI_ct -> true
              | _ -> false)
  | LS_ct -> (match y with
              | LS_ct -> true
              | _ -> false)
  | GE_ct -> (match y with
              | GE_ct -> true
              | _ -> false)
  | LT_ct -> (match y with
              | LT_ct -> true
              | _ -> false)
  | GT_ct -> (match y with
              | GT_ct -> true
              | _ -> false)
  | LE_ct -> (match y with
              | LE_ct -> true
              | _ -> false)

(** val condt_eq_dec : condt -> condt -> bool **)

let condt_eq_dec x y =
  let b = condt_beq x y in if b then true else false

(** val condt_eq_axiom : condt Equality.axiom **)

let condt_eq_axiom =
  eq_axiom_of_scheme condt_beq

(** val eqTC_condt : condt eqTypeC **)

let eqTC_condt =
  { beq = condt_beq; ceqP = condt_eq_axiom }

(** val condt_eqType : Equality.coq_type **)

let condt_eqType =
  ceqT_eqType eqTC_condt

(** val condts : condt list **)

let condts =
  EQ_ct :: (NE_ct :: (CS_ct :: (CC_ct :: (MI_ct :: (PL_ct :: (VS_ct :: (VC_ct :: (HI_ct :: (LS_ct :: (GE_ct :: (LT_ct :: (GT_ct :: (LE_ct :: [])))))))))))))

(** val finTC_condt : condt finTypeC **)

let finTC_condt =
  { _eqC = eqTC_condt; cenum = condts }

(** val condt_finType : Finite.coq_type **)

let condt_finType =
  cfinT_finType finTC_condt

(** val string_of_condt : condt -> char list **)

let string_of_condt = function
| EQ_ct -> 'e'::('q'::[])
| NE_ct -> 'n'::('e'::[])
| CS_ct -> 'c'::('s'::[])
| CC_ct -> 'c'::('c'::[])
| MI_ct -> 'm'::('i'::[])
| PL_ct -> 'p'::('l'::[])
| VS_ct -> 'v'::('s'::[])
| VC_ct -> 'v'::('c'::[])
| HI_ct -> 'h'::('i'::[])
| LS_ct -> 'l'::('s'::[])
| GE_ct -> 'g'::('e'::[])
| LT_ct -> 'l'::('t'::[])
| GT_ct -> 'g'::('t'::[])
| LE_ct -> 'l'::('e'::[])

(** val shift_kind_beq : shift_kind -> shift_kind -> bool **)

let shift_kind_beq x y =
  match x with
  | SLSL -> (match y with
             | SLSL -> true
             | _ -> false)
  | SLSR -> (match y with
             | SLSR -> true
             | _ -> false)
  | SASR -> (match y with
             | SASR -> true
             | _ -> false)
  | SROR -> (match y with
             | SROR -> true
             | _ -> false)

(** val shift_kind_eq_dec : shift_kind -> shift_kind -> bool **)

let shift_kind_eq_dec x y =
  let b = shift_kind_beq x y in if b then true else false

(** val shift_kind_eq_axiom : shift_kind Equality.axiom **)

let shift_kind_eq_axiom =
  eq_axiom_of_scheme shift_kind_beq

(** val eqTC_shift_kind : shift_kind eqTypeC **)

let eqTC_shift_kind =
  { beq = shift_kind_beq; ceqP = shift_kind_eq_axiom }

(** val shift_kind_eqType : Equality.coq_type **)

let shift_kind_eqType =
  ceqT_eqType eqTC_shift_kind

(** val shift_kinds : shift_kind list **)

let shift_kinds =
  SLSL :: (SLSR :: (SASR :: (SROR :: [])))

(** val string_of_shift_kind : shift_kind -> char list **)

let string_of_shift_kind = function
| SLSL -> 'l'::('s'::('l'::[]))
| SLSR -> 'l'::('s'::('r'::[]))
| SASR -> 'a'::('s'::('r'::[]))
| SROR -> 'r'::('o'::('r'::[]))

(** val check_shift_amount : shift_kind -> coq_Z -> bool **)

let check_shift_amount sk z =
  match sk with
  | SLSL ->
    (&&) (Z.leb Z0 z)
      (Z.leb z (Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
  | SROR ->
    (&&) (Z.leb (Zpos Coq_xH) z)
      (Z.leb z (Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
  | _ ->
    (&&) (Z.leb (Zpos Coq_xH) z)
      (Z.leb z (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))

(** val shift_op :
    shift_kind -> wsize -> GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let shift_op = function
| SLSL -> wshl
| SLSR -> wshr
| SASR -> wsar
| SROR -> wror

(** val shift_of_sop2 : wsize -> sop2 -> shift_kind option **)

let shift_of_sop2 ws op =
  match oassert (eq_op wsize_eqType (Obj.magic ws) (Obj.magic U32)) with
  | Some _ ->
    (match op with
     | Olsr w -> (match w with
                  | U32 -> Some SLSR
                  | _ -> None)
     | Olsl o ->
       (match o with
        | Op_int -> None
        | Op_w w -> (match w with
                     | U32 -> Some SLSL
                     | _ -> None))
     | Oasr o ->
       (match o with
        | Op_int -> None
        | Op_w w -> (match w with
                     | U32 -> Some SASR
                     | _ -> None))
     | Oror w -> (match w with
                  | U32 -> Some SROR
                  | _ -> None)
     | _ -> None)
  | None -> None

(** val arm_fc_of_cfc : combine_flags_core -> flag_combination **)

let arm_fc_of_cfc cfc =
  let vnf = FCVar0 in
  let vzf = FCVar1 in
  let vcf = FCVar2 in
  let vvf = FCVar3 in
  (match cfc with
   | CFC_B -> FCNot vcf
   | CFC_E -> vzf
   | CFC_L -> FCNot (FCEq (vnf, vvf))
   | CFC_BE -> FCOr ((FCNot vcf), vzf)
   | CFC_LE -> FCOr (vzf, (FCNot (FCEq (vnf, vvf)))))

(** val arm_fcp : coq_FlagCombinationParams **)

let arm_fcp =
  arm_fc_of_cfc

(** val arm_decl : (register, __, __, rflag, condt) arch_decl **)

let arm_decl =
  { reg_size = arm_reg_size; xreg_size = arm_xreg_size; cond_eqC =
    eqTC_condt; toS_r = reg_toS; toS_rx = (empty_toS (Coq_sword U32));
    toS_x = (empty_toS (Coq_sword U64)); toS_f = rflag_toS; ad_rsp = SP;
    ad_fcp = arm_fcp }

(** val arm_linux_call_conv :
    (register, __, __, rflag, condt) calling_convention **)

let arm_linux_call_conv =
  { callee_saved =
    (map (fun x -> ARReg x)
      (R04 :: (R05 :: (R06 :: (R07 :: (R08 :: (R09 :: (R10 :: (R11 :: (SP :: []))))))))));
    call_reg_args = (R00 :: (R01 :: (R02 :: (R03 :: [])))); call_xreg_args =
    []; call_reg_ret = (R00 :: (R01 :: [])); call_xreg_ret = [] }

type expand_immediate_kind =
| EI_none
| EI_byte
| EI_pattern
| EI_shift

(** val z_to_bytes : coq_Z -> ((coq_Z * coq_Z) * coq_Z) * coq_Z **)

let z_to_bytes n =
  let (n0, b0) =
    Z.div_eucl n (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO Coq_xH)))))))))
  in
  let (n1, b1) =
    Z.div_eucl n0 (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO Coq_xH)))))))))
  in
  let (n2, b2) =
    Z.div_eucl n1 (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO Coq_xH)))))))))
  in
  let b3 =
    Z.modulo n2 (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      (Coq_xO Coq_xH)))))))))
  in
  (((b3, b2), b1), b0)

(** val is_ei_pattern : coq_Z -> bool **)

let is_ei_pattern n =
  let (p, b0) = z_to_bytes n in
  let (p0, b1) = p in
  let (b3, b2) = p0 in
  (||)
    ((&&) (eq_op coq_Z_eqType (Obj.magic b3) (Obj.magic b0))
      ((&&) (eq_op coq_Z_eqType (Obj.magic b2) (Obj.magic b0))
        (eq_op coq_Z_eqType (Obj.magic b1) (Obj.magic b0))))
    ((||)
      ((&&) (eq_op coq_Z_eqType (Obj.magic b3) (Obj.magic int_to_Z (Posz O)))
        ((&&) (eq_op coq_Z_eqType (Obj.magic b2) (Obj.magic b0))
          (eq_op coq_Z_eqType (Obj.magic b1) (Obj.magic int_to_Z (Posz O)))))
      ((&&) (eq_op coq_Z_eqType (Obj.magic b3) (Obj.magic b1))
        ((&&)
          (eq_op coq_Z_eqType (Obj.magic b2) (Obj.magic int_to_Z (Posz O)))
          (eq_op coq_Z_eqType (Obj.magic b0) (Obj.magic int_to_Z (Posz O))))))

(** val is_ei_shift : coq_Z -> bool **)

let is_ei_shift n =
  let byte_end = Z.sub (Z.log2 n) (Zpos (Coq_xI (Coq_xI Coq_xH))) in
  eq_op coq_Z_eqType
    (Obj.magic Z.rem n (Z.pow (Zpos (Coq_xO Coq_xH)) byte_end))
    (Obj.magic int_to_Z (Posz O))

(** val ei_kind : coq_Z -> expand_immediate_kind **)

let ei_kind n =
  if (&&) (Z.leb Z0 n)
       (Z.ltb n (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
         (Coq_xO Coq_xH))))))))))
  then EI_byte
  else if is_ei_pattern n
       then EI_pattern
       else if is_ei_shift n then EI_shift else EI_none

(** val is_expandable : coq_Z -> bool **)

let is_expandable n =
  match ei_kind n with
  | EI_none -> false
  | EI_shift -> false
  | _ -> true

(** val is_expandable_or_shift : coq_Z -> bool **)

let is_expandable_or_shift n =
  match ei_kind n with
  | EI_none -> false
  | _ -> true

(** val is_w12_encoding : coq_Z -> bool **)

let is_w12_encoding z =
  Z.ltb z
    (Z.pow (Zpos (Coq_xO Coq_xH)) (Zpos (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))

(** val is_w16_encoding : coq_Z -> bool **)

let is_w16_encoding z =
  Z.ltb z
    (Z.pow (Zpos (Coq_xO Coq_xH)) (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      Coq_xH))))))
