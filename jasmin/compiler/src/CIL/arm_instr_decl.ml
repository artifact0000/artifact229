open BinInt
open BinNums
open Bool
open Datatypes
open PeanoNat
open String0
open Arch_decl
open Arch_utils
open Arm_decl
open Eqtype
open Fintype
open Sem_type
open Seq
open Shift_kind
open Sopn
open Ssralg
open Ssrbool
open Ssrnat
open Type
open Utils0
open Word0
open Word_ssrZ
open Wsize
open Xseq

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module E =
 struct
  (** val no_semantics : error **)

  let no_semantics =
    ErrType
 end

type arm_options = { set_flags : bool; is_conditional : bool;
                     has_shift : shift_kind option }

(** val set_flags : arm_options -> bool **)

let set_flags a =
  a.set_flags

(** val is_conditional : arm_options -> bool **)

let is_conditional a =
  a.is_conditional

(** val has_shift : arm_options -> shift_kind option **)

let has_shift a =
  a.has_shift

(** val arm_options_beq : arm_options -> arm_options -> bool **)

let arm_options_beq ao0 ao1 =
  (&&)
    (eq_op bool_eqType (Obj.magic ao0.set_flags) (Obj.magic ao1.set_flags))
    ((&&)
      (eq_op bool_eqType (Obj.magic ao0.is_conditional)
        (Obj.magic ao1.is_conditional))
      (eq_op (option_eqType shift_kind_eqType) (Obj.magic ao0.has_shift)
        (Obj.magic ao1.has_shift)))

(** val arm_options_eq_axiom : arm_options Equality.axiom **)

let arm_options_eq_axiom __top_assumption_ =
  let _evar_0_ =
    fun _set_flags_ _is_conditional_ _has_shift_ __top_assumption_0 ->
    let _evar_0_ = fun _set_flags1_ _is_conditional1_ _has_shift1_ ->
      iffP
        (arm_options_beq { set_flags = _set_flags_; is_conditional =
          _is_conditional_; has_shift = _has_shift_ } { set_flags =
          _set_flags1_; is_conditional = _is_conditional1_; has_shift =
          _has_shift1_ })
        (if arm_options_beq { set_flags = _set_flags_; is_conditional =
              _is_conditional_; has_shift = _has_shift_ } { set_flags =
              _set_flags1_; is_conditional = _is_conditional1_; has_shift =
              _has_shift1_ }
         then ReflectT
         else ReflectF)
    in
    let { set_flags = set_flags0; is_conditional = is_conditional0;
      has_shift = has_shift0 } = __top_assumption_0
    in
    _evar_0_ set_flags0 is_conditional0 has_shift0
  in
  let { set_flags = set_flags0; is_conditional = is_conditional0; has_shift =
    has_shift0 } = __top_assumption_
  in
  _evar_0_ set_flags0 is_conditional0 has_shift0

(** val eqTC_arm_options : arm_options eqTypeC **)

let eqTC_arm_options =
  { beq = arm_options_beq; ceqP = arm_options_eq_axiom }

(** val arm_options_eqType : Equality.coq_type **)

let arm_options_eqType =
  ceqT_eqType eqTC_arm_options

(** val arm_options_dec_eq : arm_options -> arm_options -> bool **)

let arm_options_dec_eq ao0 ao1 =
  let _evar_0_ = fun _ -> true in
  let _evar_0_0 = fun _ -> false in
  (match arm_options_eq_axiom ao0 ao1 with
   | ReflectT -> _evar_0_ __
   | ReflectF -> _evar_0_0 __)

(** val default_opts : arm_options **)

let default_opts =
  { set_flags = false; is_conditional = false; has_shift = None }

(** val set_is_conditional : arm_options -> arm_options **)

let set_is_conditional ao =
  { set_flags = ao.set_flags; is_conditional = true; has_shift =
    ao.has_shift }

(** val unset_is_conditional : arm_options -> arm_options **)

let unset_is_conditional ao =
  { set_flags = ao.set_flags; is_conditional = false; has_shift =
    ao.has_shift }

type halfword =
| HWB
| HWT

type arm_mnemonic =
| ADD
| ADC
| MUL
| MLA
| MLS
| SDIV
| SUB
| RSB
| UDIV
| UMULL
| UMAAL
| UMLAL
| SMULL
| SMLAL
| SMMUL
| SMMULR
| SMUL_hw of halfword * halfword
| SMLA_hw of halfword * halfword
| SMULW_hw of halfword
| AND
| BFC
| BFI
| BIC
| EOR
| MVN
| ORR
| ASR
| LSL
| LSR
| ROR
| REV
| REV16
| REVSH
| ADR
| MOV
| MOVT
| UBFX
| UXTB
| UXTH
| SBFX
| CLZ
| CMP
| TST
| CMN
| LDR
| LDRB
| LDRH
| LDRSB
| LDRSH
| STR
| STRB
| STRH

(** val internal_halfword_beq : halfword -> halfword -> bool **)

let internal_halfword_beq x y =
  match x with
  | HWB -> (match y with
            | HWB -> true
            | HWT -> false)
  | HWT -> (match y with
            | HWB -> false
            | HWT -> true)

(** val arm_mnemonic_beq : arm_mnemonic -> arm_mnemonic -> bool **)

let arm_mnemonic_beq x y =
  match x with
  | ADD -> (match y with
            | ADD -> true
            | _ -> false)
  | ADC -> (match y with
            | ADC -> true
            | _ -> false)
  | MUL -> (match y with
            | MUL -> true
            | _ -> false)
  | MLA -> (match y with
            | MLA -> true
            | _ -> false)
  | MLS -> (match y with
            | MLS -> true
            | _ -> false)
  | SDIV -> (match y with
             | SDIV -> true
             | _ -> false)
  | SUB -> (match y with
            | SUB -> true
            | _ -> false)
  | RSB -> (match y with
            | RSB -> true
            | _ -> false)
  | UDIV -> (match y with
             | UDIV -> true
             | _ -> false)
  | UMULL -> (match y with
              | UMULL -> true
              | _ -> false)
  | UMAAL -> (match y with
              | UMAAL -> true
              | _ -> false)
  | UMLAL -> (match y with
              | UMLAL -> true
              | _ -> false)
  | SMULL -> (match y with
              | SMULL -> true
              | _ -> false)
  | SMLAL -> (match y with
              | SMLAL -> true
              | _ -> false)
  | SMMUL -> (match y with
              | SMMUL -> true
              | _ -> false)
  | SMMULR -> (match y with
               | SMMULR -> true
               | _ -> false)
  | SMUL_hw (x0, x1) ->
    (match y with
     | SMUL_hw (x2, x3) ->
       (&&) (internal_halfword_beq x0 x2) (internal_halfword_beq x1 x3)
     | _ -> false)
  | SMLA_hw (x0, x1) ->
    (match y with
     | SMLA_hw (x2, x3) ->
       (&&) (internal_halfword_beq x0 x2) (internal_halfword_beq x1 x3)
     | _ -> false)
  | SMULW_hw x0 ->
    (match y with
     | SMULW_hw x1 -> internal_halfword_beq x0 x1
     | _ -> false)
  | AND -> (match y with
            | AND -> true
            | _ -> false)
  | BFC -> (match y with
            | BFC -> true
            | _ -> false)
  | BFI -> (match y with
            | BFI -> true
            | _ -> false)
  | BIC -> (match y with
            | BIC -> true
            | _ -> false)
  | EOR -> (match y with
            | EOR -> true
            | _ -> false)
  | MVN -> (match y with
            | MVN -> true
            | _ -> false)
  | ORR -> (match y with
            | ORR -> true
            | _ -> false)
  | ASR -> (match y with
            | ASR -> true
            | _ -> false)
  | LSL -> (match y with
            | LSL -> true
            | _ -> false)
  | LSR -> (match y with
            | LSR -> true
            | _ -> false)
  | ROR -> (match y with
            | ROR -> true
            | _ -> false)
  | REV -> (match y with
            | REV -> true
            | _ -> false)
  | REV16 -> (match y with
              | REV16 -> true
              | _ -> false)
  | REVSH -> (match y with
              | REVSH -> true
              | _ -> false)
  | ADR -> (match y with
            | ADR -> true
            | _ -> false)
  | MOV -> (match y with
            | MOV -> true
            | _ -> false)
  | MOVT -> (match y with
             | MOVT -> true
             | _ -> false)
  | UBFX -> (match y with
             | UBFX -> true
             | _ -> false)
  | UXTB -> (match y with
             | UXTB -> true
             | _ -> false)
  | UXTH -> (match y with
             | UXTH -> true
             | _ -> false)
  | SBFX -> (match y with
             | SBFX -> true
             | _ -> false)
  | CLZ -> (match y with
            | CLZ -> true
            | _ -> false)
  | CMP -> (match y with
            | CMP -> true
            | _ -> false)
  | TST -> (match y with
            | TST -> true
            | _ -> false)
  | CMN -> (match y with
            | CMN -> true
            | _ -> false)
  | LDR -> (match y with
            | LDR -> true
            | _ -> false)
  | LDRB -> (match y with
             | LDRB -> true
             | _ -> false)
  | LDRH -> (match y with
             | LDRH -> true
             | _ -> false)
  | LDRSB -> (match y with
              | LDRSB -> true
              | _ -> false)
  | LDRSH -> (match y with
              | LDRSH -> true
              | _ -> false)
  | STR -> (match y with
            | STR -> true
            | _ -> false)
  | STRB -> (match y with
             | STRB -> true
             | _ -> false)
  | STRH -> (match y with
             | STRH -> true
             | _ -> false)

(** val arm_mnemonic_eq_dec : arm_mnemonic -> arm_mnemonic -> bool **)

let arm_mnemonic_eq_dec x y =
  let b = arm_mnemonic_beq x y in if b then true else false

(** val arm_mnemonic_eq_axiom : arm_mnemonic Equality.axiom **)

let arm_mnemonic_eq_axiom =
  eq_axiom_of_scheme arm_mnemonic_beq

(** val eqTC_arm_mnemonic : arm_mnemonic eqTypeC **)

let eqTC_arm_mnemonic =
  { beq = arm_mnemonic_beq; ceqP = arm_mnemonic_eq_axiom }

(** val arm_mnemonic_eqType : Equality.coq_type **)

let arm_mnemonic_eqType =
  ceqT_eqType eqTC_arm_mnemonic

(** val arm_mnemonics : arm_mnemonic list **)

let arm_mnemonics =
  ADD :: (ADC :: (MUL :: (MLA :: (MLS :: (SDIV :: (SUB :: (RSB :: (UDIV :: (UMULL :: (UMAAL :: (UMLAL :: (SMULL :: (SMLAL :: (SMMUL :: (SMMULR :: ((SMUL_hw
    (HWB, HWB)) :: ((SMUL_hw (HWB, HWT)) :: ((SMUL_hw (HWT,
    HWB)) :: ((SMUL_hw (HWT, HWT)) :: ((SMLA_hw (HWB, HWB)) :: ((SMLA_hw
    (HWB, HWT)) :: ((SMLA_hw (HWT, HWB)) :: ((SMLA_hw (HWT,
    HWT)) :: ((SMULW_hw HWB) :: ((SMULW_hw
    HWT) :: (AND :: (BFC :: (BFI :: (BIC :: (EOR :: (MVN :: (ORR :: (ASR :: (LSL :: (LSR :: (ROR :: (REV :: (REV16 :: (REVSH :: (ADR :: (MOV :: (MOVT :: (UBFX :: (UXTB :: (UXTH :: (SBFX :: (CLZ :: (CMP :: (TST :: (CMN :: (LDR :: (LDRB :: (LDRH :: (LDRSB :: (LDRSH :: (STR :: (STRB :: (STRH :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val finTC_arm_mnemonic : arm_mnemonic finTypeC **)

let finTC_arm_mnemonic =
  { _eqC = eqTC_arm_mnemonic; cenum = arm_mnemonics }

(** val arm_mnemonic_finType : Finite.coq_type **)

let arm_mnemonic_finType =
  cfinT_finType finTC_arm_mnemonic

(** val set_flags_mnemonics : arm_mnemonic list **)

let set_flags_mnemonics =
  ADD :: (ADC :: (MUL :: (SUB :: (RSB :: (AND :: (BIC :: (EOR :: (MVN :: (ORR :: (ASR :: (LSL :: (LSR :: (ROR :: (MOV :: []))))))))))))))

(** val has_shift_mnemonics : arm_mnemonic list **)

let has_shift_mnemonics =
  ADD :: (ADC :: (SUB :: (RSB :: (AND :: (BIC :: (EOR :: (MVN :: (ORR :: (CMP :: (TST :: (CMN :: [])))))))))))

(** val condition_mnemonics : arm_mnemonic list **)

let condition_mnemonics =
  CMP :: (TST :: [])

(** val always_has_shift_mnemonics : (arm_mnemonic * shift_kind) list **)

let always_has_shift_mnemonics =
  (UXTB, SROR) :: ((UXTH, SROR) :: [])

(** val wsize_uload_mn : (wsize * arm_mnemonic) list **)

let wsize_uload_mn =
  (U8, LDRB) :: ((U16, LDRH) :: ((U32, LDR) :: []))

(** val uload_mn_of_wsize : wsize -> arm_mnemonic option **)

let uload_mn_of_wsize ws =
  assoc wsize_eqType (Obj.magic wsize_uload_mn) (Obj.magic ws)

(** val wsize_of_uload_mn : arm_mnemonic -> wsize option **)

let wsize_of_uload_mn mn =
  assoc arm_mnemonic_eqType
    (map (fun x -> ((snd (Obj.magic x)), (fst x))) wsize_uload_mn)
    (Obj.magic mn)

(** val wsize_sload_mn : (wsize * arm_mnemonic) list **)

let wsize_sload_mn =
  (U8, LDRSB) :: ((U16, LDRSH) :: [])

(** val sload_mn_of_wsize : wsize -> arm_mnemonic option **)

let sload_mn_of_wsize ws =
  assoc wsize_eqType (Obj.magic wsize_sload_mn) (Obj.magic ws)

(** val wsize_of_sload_mn : arm_mnemonic -> wsize option **)

let wsize_of_sload_mn mn =
  assoc arm_mnemonic_eqType
    (map (fun x -> ((snd (Obj.magic x)), (fst x))) wsize_sload_mn)
    (Obj.magic mn)

(** val wsize_of_load_mn : arm_mnemonic -> wsize option **)

let wsize_of_load_mn mn =
  match wsize_of_uload_mn mn with
  | Some ws -> Some ws
  | None -> wsize_of_sload_mn mn

(** val wsize_store_mn : (wsize * arm_mnemonic) list **)

let wsize_store_mn =
  (U8, STRB) :: ((U16, STRH) :: ((U32, STR) :: []))

(** val store_mn_of_wsize : wsize -> arm_mnemonic option **)

let store_mn_of_wsize ws =
  assoc wsize_eqType (Obj.magic wsize_store_mn) (Obj.magic ws)

(** val wsize_of_store_mn : arm_mnemonic -> wsize option **)

let wsize_of_store_mn mn =
  assoc arm_mnemonic_eqType
    (map (fun x -> ((snd (Obj.magic x)), (fst x))) wsize_store_mn)
    (Obj.magic mn)

(** val string_of_hw : halfword -> char list **)

let string_of_hw = function
| HWB -> 'B'::[]
| HWT -> 'T'::[]

(** val string_of_arm_mnemonic : arm_mnemonic -> char list **)

let string_of_arm_mnemonic mn =
  let with_hw = fun s hw -> append s (string_of_hw hw) in
  (match mn with
   | ADD -> 'A'::('D'::('D'::[]))
   | ADC -> 'A'::('D'::('C'::[]))
   | MUL -> 'M'::('U'::('L'::[]))
   | MLA -> 'M'::('L'::('A'::[]))
   | MLS -> 'M'::('L'::('S'::[]))
   | SDIV -> 'S'::('D'::('I'::('V'::[])))
   | SUB -> 'S'::('U'::('B'::[]))
   | RSB -> 'R'::('S'::('B'::[]))
   | UDIV -> 'U'::('D'::('I'::('V'::[])))
   | UMULL -> 'U'::('M'::('U'::('L'::('L'::[]))))
   | UMAAL -> 'U'::('M'::('A'::('A'::('L'::[]))))
   | UMLAL -> 'U'::('M'::('L'::('A'::('L'::[]))))
   | SMULL -> 'S'::('M'::('U'::('L'::('L'::[]))))
   | SMLAL -> 'S'::('M'::('L'::('A'::('L'::[]))))
   | SMMUL -> 'S'::('M'::('M'::('U'::('L'::[]))))
   | SMMULR -> 'S'::('M'::('M'::('U'::('L'::('R'::[])))))
   | SMUL_hw (hw0, hw1) ->
     with_hw (with_hw ('S'::('M'::('U'::('L'::[])))) hw0) hw1
   | SMLA_hw (hw0, hw1) ->
     with_hw (with_hw ('S'::('M'::('L'::('A'::[])))) hw0) hw1
   | SMULW_hw hw -> with_hw ('S'::('M'::('U'::('L'::('W'::[]))))) hw
   | AND -> 'A'::('N'::('D'::[]))
   | BFC -> 'B'::('F'::('C'::[]))
   | BFI -> 'B'::('F'::('I'::[]))
   | BIC -> 'B'::('I'::('C'::[]))
   | EOR -> 'E'::('O'::('R'::[]))
   | MVN -> 'M'::('V'::('N'::[]))
   | ORR -> 'O'::('R'::('R'::[]))
   | ASR -> 'A'::('S'::('R'::[]))
   | LSL -> 'L'::('S'::('L'::[]))
   | LSR -> 'L'::('S'::('R'::[]))
   | ROR -> 'R'::('O'::('R'::[]))
   | REV -> 'R'::('E'::('V'::[]))
   | REV16 -> 'R'::('E'::('V'::('1'::('6'::[]))))
   | REVSH -> 'R'::('E'::('V'::('S'::('H'::[]))))
   | ADR -> 'A'::('D'::('R'::[]))
   | MOV -> 'M'::('O'::('V'::[]))
   | MOVT -> 'M'::('O'::('V'::('T'::[])))
   | UBFX -> 'U'::('B'::('F'::('X'::[])))
   | UXTB -> 'U'::('X'::('T'::('B'::[])))
   | UXTH -> 'U'::('X'::('T'::('H'::[])))
   | SBFX -> 'S'::('B'::('F'::('X'::[])))
   | CLZ -> 'C'::('L'::('Z'::[]))
   | CMP -> 'C'::('M'::('P'::[]))
   | TST -> 'T'::('S'::('T'::[]))
   | CMN -> 'C'::('M'::('N'::[]))
   | LDR -> 'L'::('D'::('R'::[]))
   | LDRB -> 'L'::('D'::('R'::('B'::[])))
   | LDRH -> 'L'::('D'::('R'::('H'::[])))
   | LDRSB -> 'L'::('D'::('R'::('S'::('B'::[]))))
   | LDRSH -> 'L'::('D'::('R'::('S'::('H'::[]))))
   | STR -> 'S'::('T'::('R'::[]))
   | STRB -> 'S'::('T'::('R'::('B'::[])))
   | STRH -> 'S'::('T'::('R'::('H'::[]))))

type arm_op =
| ARM_op of arm_mnemonic * arm_options

(** val arm_op_beq : arm_op -> arm_op -> bool **)

let arm_op_beq op0 op1 =
  let ARM_op (mn0, ao0) = op0 in
  let ARM_op (mn1, ao1) = op1 in
  (&&) (eq_op arm_mnemonic_eqType (Obj.magic mn0) (Obj.magic mn1))
    (eq_op arm_options_eqType (Obj.magic ao0) (Obj.magic ao1))

(** val arm_op_eq_axiom : arm_op Equality.axiom **)

let arm_op_eq_axiom __top_assumption_ =
  let _evar_0_ = fun mn0 ao0 __top_assumption_0 ->
    let _evar_0_ = fun mn1 ao1 ->
      iffP (arm_op_beq (ARM_op (mn0, ao0)) (ARM_op (mn1, ao1)))
        (if arm_op_beq (ARM_op (mn0, ao0)) (ARM_op (mn1, ao1))
         then ReflectT
         else ReflectF)
    in
    let ARM_op (a, a0) = __top_assumption_0 in _evar_0_ a a0
  in
  let ARM_op (a, a0) = __top_assumption_ in _evar_0_ a a0

(** val eqTC_arm_op : arm_op eqTypeC **)

let eqTC_arm_op =
  { beq = arm_op_beq; ceqP = arm_op_eq_axiom }

(** val arm_op_eqType : Equality.coq_type **)

let arm_op_eqType =
  ceqT_eqType eqTC_arm_op

(** val arm_op_dec_eq : arm_op -> arm_op -> bool **)

let arm_op_dec_eq op0 op1 =
  let _evar_0_ = fun _ -> true in
  let _evar_0_0 = fun _ -> false in
  (match arm_op_eq_axiom op0 op1 with
   | ReflectT -> _evar_0_ __
   | ReflectF -> _evar_0_0 __)

(** val ad_nz : (register, __, __, rflag, condt) Arch_decl.arg_desc list **)

let ad_nz =
  map (coq_F arm_decl) (NF :: (ZF :: []))

(** val ad_nzc : (register, __, __, rflag, condt) Arch_decl.arg_desc list **)

let ad_nzc =
  map (coq_F arm_decl) (NF :: (ZF :: (CF :: [])))

(** val ad_nzcv : (register, __, __, rflag, condt) Arch_decl.arg_desc list **)

let ad_nzcv =
  map (coq_F arm_decl) (NF :: (ZF :: (CF :: (VF :: []))))

(** val coq_NF_of_word : wsize -> GRing.ComRing.sort -> bool **)

let coq_NF_of_word =
  msb

(** val coq_ZF_of_word : wsize -> GRing.ComRing.sort -> bool **)

let coq_ZF_of_word ws w =
  eq_op (GRing.ComRing.eqType (word ws)) w
    (GRing.zero (GRing.ComRing.zmodType (word ws)))

(** val nzcv_of_aluop :
    wsize -> GRing.ComRing.sort -> coq_Z -> coq_Z -> sem_tuple **)

let nzcv_of_aluop ws res res_unsigned res_signed =
  Obj.magic ((Some (coq_NF_of_word ws res)), ((Some (coq_ZF_of_word ws res)),
    ((Some
    (negb
      (eq_op coq_Z_eqType (Obj.magic wunsigned ws res)
        (Obj.magic res_unsigned)))), (Some
    (negb
      (eq_op coq_Z_eqType (Obj.magic wsigned ws res) (Obj.magic res_signed)))))))

(** val nzcv_w_of_aluop :
    wsize -> GRing.ComRing.sort -> coq_Z -> coq_Z -> ltuple **)

let nzcv_w_of_aluop ws w wun wsi =
  merge_tuple
    (map (Obj.magic __)
      (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))))
    (map (Obj.magic __) ((Coq_sword ws) :: [])) (nzcv_of_aluop ws w wun wsi) w

(** val drop_nz :
    (register, __, __, rflag, condt) instr_desc_t -> (register, __, __,
    rflag, condt) instr_desc_t **)

let drop_nz =
  idt_drop2 arm_decl

(** val drop_nzc :
    (register, __, __, rflag, condt) instr_desc_t -> (register, __, __,
    rflag, condt) instr_desc_t **)

let drop_nzc =
  idt_drop3 arm_decl

(** val drop_nzcv :
    (register, __, __, rflag, condt) instr_desc_t -> (register, __, __,
    rflag, condt) instr_desc_t **)

let drop_nzcv =
  idt_drop4 arm_decl

(** val mk_semi_cond :
    stype list -> stype list -> sem_tuple exec sem_prod -> sem_tuple exec
    sem_prod **)

let mk_semi_cond tin tout semi =
  let f0 = fun res cond ->
    if cond
    then sem_prod_const tout res
    else sem_prod_app tout (sem_prod_tuple tout) (fun x -> Ok x)
  in
  let f1 = sem_prod_app tin semi f0 in
  add_arguments tin (Coq_sbool :: tout) f1

(** val mk_cond :
    (register, __, __, rflag, condt) instr_desc_t -> (register, __, __,
    rflag, condt) instr_desc_t **)

let mk_cond idt =
  { id_msb_flag = MSB_MERGE; id_tin =
    (cat idt.id_tin (Coq_sbool :: idt.id_tout)); id_in =
    (cat idt.id_in ((coq_E arm_decl idt.id_nargs) :: idt.id_out)); id_tout =
    idt.id_tout; id_out = idt.id_out; id_semi =
    (mk_semi_cond idt.id_tin idt.id_tout idt.id_semi); id_args_kinds =
    (map (fun x -> cat x ((CAcond :: []) :: [])) idt.id_args_kinds);
    id_nargs = (S idt.id_nargs); id_str_jas = idt.id_str_jas; id_safe =
    idt.id_safe; id_pp_asm = idt.id_pp_asm }

(** val mk_semi1_shifted :
    shift_kind -> 'a1 exec sem_prod -> 'a1 exec sem_prod **)

let mk_semi1_shifted sk semi =
  Obj.magic (fun wn shift_amount ->
    let sham = wunsigned U8 shift_amount in
    Obj.magic semi (shift_op sk arm_decl.reg_size wn sham))

(** val mk_semi2_2_shifted :
    stype -> shift_kind -> 'a1 exec sem_prod -> 'a1 exec sem_prod **)

let mk_semi2_2_shifted _ sk semi =
  Obj.magic (fun x wm shift_amount ->
    let sham = wunsigned U8 shift_amount in
    Obj.magic semi x (shift_op sk arm_decl.reg_size wm sham))

(** val mk_semi3_2_shifted :
    stype -> stype -> shift_kind -> 'a1 exec sem_prod -> 'a1 exec sem_prod **)

let mk_semi3_2_shifted _ _ sk semi =
  Obj.magic (fun x wm y shift_amount ->
    let sham = wunsigned U8 shift_amount in
    Obj.magic semi x (shift_op sk arm_decl.reg_size wm sham) y)

(** val mk_shifted :
    shift_kind -> (register, __, __, rflag, condt) instr_desc_t -> sem_tuple
    exec sem_prod -> (register, __, __, rflag, condt) instr_desc_t **)

let mk_shifted _ idt semi' =
  { id_msb_flag = MSB_MERGE; id_tin =
    (cat idt.id_tin ((Coq_sword U8) :: [])); id_in =
    (cat idt.id_in ((coq_E arm_decl idt.id_nargs) :: [])); id_tout =
    idt.id_tout; id_out = idt.id_out; id_semi = semi'; id_args_kinds =
    (map (fun x -> cat x (((CAimm arm_decl.reg_size) :: []) :: []))
      idt.id_args_kinds); id_nargs = (S idt.id_nargs); id_str_jas =
    idt.id_str_jas; id_safe = idt.id_safe; id_pp_asm = idt.id_pp_asm }

(** val pp_arm_op :
    arm_mnemonic -> arm_options -> (register, __, __, rflag, condt) asm_arg
    list -> (register, __, __, rflag, condt) pp_asm_op **)

let pp_arm_op mn _ args =
  { pp_aop_name = (string_of_arm_mnemonic mn); pp_aop_ext = PP_name;
    pp_aop_args = (map (fun a -> (arm_decl.reg_size, a)) args) }

(** val arm_ADD_semi : sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_ADD_semi wn wm =
  let x =
    nzcv_w_of_aluop arm_decl.reg_size
      (GRing.add (GRing.ComRing.zmodType (word arm_decl.reg_size)) wn wm)
      (Z.add (wunsigned arm_decl.reg_size wn)
        (wunsigned arm_decl.reg_size wm))
      (Z.add (wsigned arm_decl.reg_size wn) (wsigned arm_decl.reg_size wm))
  in
  Ok x

(** val arm_ADD_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_ADD_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = ADD in
  let x = { id_msb_flag = MSB_MERGE; id_tin =
    ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
    ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: []))))
      ((sreg arm_decl) :: [])); id_out =
    (cat ad_nzcv ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic arm_ADD_semi); id_args_kinds =
    (cat ak_reg_reg_reg (ak_reg_reg_imm arm_decl)); id_nargs = (S (S (S O)));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  let x0 =
    match opts.has_shift with
    | Some sk ->
      mk_shifted sk x (mk_semi2_2_shifted (sreg arm_decl) sk x.id_semi)
    | None -> x
  in
  if opts.set_flags then x0 else drop_nzcv x0

(** val arm_ADC_semi : sem_tuple -> sem_tuple -> bool -> sem_tuple exec **)

let arm_ADC_semi wn wm cf =
  let c = Z.b2z cf in
  let x =
    nzcv_w_of_aluop arm_decl.reg_size
      (GRing.add (GRing.ComRing.zmodType (word arm_decl.reg_size))
        (GRing.add (GRing.ComRing.zmodType (word arm_decl.reg_size)) wn wm)
        (wrepr arm_decl.reg_size c))
      (Z.add
        (Z.add (wunsigned arm_decl.reg_size wn)
          (wunsigned arm_decl.reg_size wm)) c)
      (Z.add
        (Z.add (wsigned arm_decl.reg_size wn) (wsigned arm_decl.reg_size wm))
        c)
  in
  Ok x

(** val arm_ADC_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_ADC_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = ADC in
  let x = { id_msb_flag = MSB_MERGE; id_tin =
    ((sreg arm_decl) :: ((sreg arm_decl) :: (Coq_sbool :: []))); id_in =
    ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: ((coq_F
                                                                 arm_decl CF) :: [])));
    id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: []))))
      ((sreg arm_decl) :: [])); id_out =
    (cat ad_nzcv ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic arm_ADC_semi); id_args_kinds =
    (cat ak_reg_reg_reg (ak_reg_reg_imm arm_decl)); id_nargs = (S (S (S O)));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  let x0 =
    match opts.has_shift with
    | Some sk ->
      mk_shifted sk x
        (mk_semi3_2_shifted (sreg arm_decl) Coq_sbool sk x.id_semi)
    | None -> x
  in
  if opts.set_flags then x0 else drop_nzcv x0

(** val arm_MUL_semi : sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_MUL_semi wn wm =
  let res = GRing.mul (GRing.ComRing.ringType (word arm_decl.reg_size)) wn wm
  in
  Ok
  (Obj.magic ((Some (coq_NF_of_word arm_decl.reg_size res)), ((Some
    (coq_ZF_of_word arm_decl.reg_size res)), res)))

(** val arm_MUL_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_MUL_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = MUL in
  let x = { id_msb_flag = MSB_MERGE; id_tin =
    ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
    ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: [])) ((sreg arm_decl) :: [])); id_out =
    (cat ad_nz ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic arm_MUL_semi); id_args_kinds = ak_reg_reg_reg; id_nargs = (S
    (S (S O))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe =
    []; id_pp_asm = (pp_arm_op mn opts) }
  in
  if opts.set_flags then x else drop_nz x

(** val arm_MLA_semi :
    sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_MLA_semi wn wm wa =
  Ok
    (GRing.add
      (GRing.Ring.zmodType (GRing.ComRing.ringType (word arm_decl.reg_size)))
      (GRing.mul (GRing.ComRing.ringType (word arm_decl.reg_size)) wn wm) wa)

(** val arm_MLA_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_MLA_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = MLA in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: ((sreg arm_decl) :: []))); id_in =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: ((coq_E arm_decl
                                                               (S (S (S O)))) :: [])));
  id_tout = ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []);
  id_semi = (Obj.magic arm_MLA_semi); id_args_kinds = ak_reg_reg_reg_reg;
  id_nargs = (S (S (S (S O)))); id_str_jas =
  (pp_s (string_of_arm_mnemonic0 mn)); id_safe = []; id_pp_asm =
  (pp_arm_op mn opts) }

(** val arm_MLS_semi :
    sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_MLS_semi wn wm wa =
  Ok
    (GRing.add (GRing.ComRing.zmodType (word arm_decl.reg_size)) wa
      (GRing.opp
        (GRing.Ring.zmodType
          (GRing.ComRing.ringType (word arm_decl.reg_size)))
        (GRing.mul (GRing.ComRing.ringType (word arm_decl.reg_size)) wn wm)))

(** val arm_MLS_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_MLS_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = MLS in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: ((sreg arm_decl) :: []))); id_in =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: ((coq_E arm_decl
                                                               (S (S (S O)))) :: [])));
  id_tout = ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []);
  id_semi = (Obj.magic arm_MLS_semi); id_args_kinds = ak_reg_reg_reg_reg;
  id_nargs = (S (S (S (S O)))); id_str_jas =
  (pp_s (string_of_arm_mnemonic0 mn)); id_safe = []; id_pp_asm =
  (pp_arm_op mn opts) }

(** val arm_SDIV_semi : sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_SDIV_semi wn wm =
  Ok (wdivi arm_decl.reg_size wn wm)

(** val arm_SDIV_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_SDIV_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = SDIV in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
  ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []); id_semi =
  (Obj.magic arm_SDIV_semi); id_args_kinds = ak_reg_reg_reg; id_nargs = (S (S
  (S O))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
  id_pp_asm = (pp_arm_op mn opts) }

(** val arm_SUB_semi : sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_SUB_semi wn wm =
  let wmnot = wnot arm_decl.reg_size wm in
  let x =
    nzcv_w_of_aluop arm_decl.reg_size
      (GRing.add (GRing.ComRing.zmodType (word arm_decl.reg_size))
        (GRing.add (GRing.ComRing.zmodType (word arm_decl.reg_size)) wn wmnot)
        (GRing.one (GRing.ComRing.ringType (word arm_decl.reg_size))))
      (Z.add
        (Z.add (wunsigned arm_decl.reg_size wn)
          (wunsigned arm_decl.reg_size wmnot)) (Zpos Coq_xH))
      (Z.add
        (Z.add (wsigned arm_decl.reg_size wn)
          (wsigned arm_decl.reg_size wmnot)) (Zpos Coq_xH))
  in
  Ok x

(** val arm_SUB_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_SUB_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = SUB in
  let x = { id_msb_flag = MSB_MERGE; id_tin =
    ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
    ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: []))))
      ((sreg arm_decl) :: [])); id_out =
    (cat ad_nzcv ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic arm_SUB_semi); id_args_kinds =
    (cat ak_reg_reg_reg (ak_reg_reg_imm arm_decl)); id_nargs = (S (S (S O)));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  let x0 =
    match opts.has_shift with
    | Some sk ->
      mk_shifted sk x (mk_semi2_2_shifted (sreg arm_decl) sk x.id_semi)
    | None -> x
  in
  if opts.set_flags then x0 else drop_nzcv x0

(** val arm_RSB_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_RSB_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = RSB in
  let x = { id_msb_flag = MSB_MERGE; id_tin =
    ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
    ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: []))))
      ((sreg arm_decl) :: [])); id_out =
    (cat ad_nzcv ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic (fun wn wm -> arm_SUB_semi wm wn)); id_args_kinds =
    (cat ak_reg_reg_reg (ak_reg_reg_imm arm_decl)); id_nargs = (S (S (S O)));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  let x0 =
    match opts.has_shift with
    | Some sk ->
      mk_shifted sk x (mk_semi2_2_shifted (sreg arm_decl) sk x.id_semi)
    | None -> x
  in
  if opts.set_flags then x0 else drop_nzcv x0

(** val arm_UDIV_semi : sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_UDIV_semi wn wm =
  Ok (wdiv arm_decl.reg_size wn wm)

(** val arm_UDIV_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_UDIV_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = UDIV in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
  ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []); id_semi =
  (Obj.magic arm_UDIV_semi); id_args_kinds = ak_reg_reg_reg; id_nargs = (S (S
  (S O))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
  id_pp_asm = (pp_arm_op mn opts) }

(** val arm_UMULL_semi : sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_UMULL_semi wn wm =
  Ok (Obj.magic wumul arm_decl.reg_size wn wm)

(** val arm_UMULL_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_UMULL_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = UMULL in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
  ((coq_E arm_decl (S (S O))) :: ((coq_E arm_decl (S (S (S O)))) :: []));
  id_tout = ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_out =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl O) :: [])); id_semi =
  (Obj.magic arm_UMULL_semi); id_args_kinds = ak_reg_reg_reg_reg; id_nargs =
  (S (S (S (S O)))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn));
  id_safe = []; id_pp_asm = (pp_arm_op mn opts) }

(** val arm_UMAAL_semi :
    sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_UMAAL_semi wa wb wn wm =
  let r =
    Z.add
      (Z.add (wunsigned arm_decl.reg_size wa)
        (wunsigned arm_decl.reg_size wb))
      (Z.mul (wunsigned arm_decl.reg_size wn)
        (wunsigned arm_decl.reg_size wm))
  in
  Ok
  (Obj.magic ((wrepr arm_decl.reg_size r), (high_bits arm_decl.reg_size r)))

(** val arm_UMAAL_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_UMAAL_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = UMAAL in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: ((sreg arm_decl) :: ((sreg arm_decl) :: []))));
  id_in =
  ((coq_E arm_decl O) :: ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S
                                                       O))) :: ((coq_E
                                                                  arm_decl (S
                                                                  (S (S O)))) :: []))));
  id_tout = ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_out =
  ((coq_E arm_decl O) :: ((coq_E arm_decl (S O)) :: [])); id_semi =
  (Obj.magic arm_UMAAL_semi); id_args_kinds = ak_reg_reg_reg_reg; id_nargs =
  (S (S (S (S O)))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn));
  id_safe = []; id_pp_asm = (pp_arm_op mn opts) }

(** val arm_UMLAL_semi :
    sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_UMLAL_semi dlo dhi wn wm =
  let (hi, lo) = wumul arm_decl.reg_size wn wm in
  Ok (Obj.magic wdaddu arm_decl.reg_size dhi dlo hi lo)

(** val arm_UMLAL_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_UMLAL_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = UMLAL in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: ((sreg arm_decl) :: ((sreg arm_decl) :: []))));
  id_in =
  ((coq_E arm_decl O) :: ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S
                                                       O))) :: ((coq_E
                                                                  arm_decl (S
                                                                  (S (S O)))) :: []))));
  id_tout = ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_out =
  ((coq_E arm_decl O) :: ((coq_E arm_decl (S O)) :: [])); id_semi =
  (Obj.magic arm_UMLAL_semi); id_args_kinds = ak_reg_reg_reg_reg; id_nargs =
  (S (S (S (S O)))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn));
  id_safe = []; id_pp_asm = (pp_arm_op mn opts) }

(** val arm_SMULL_semi : sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_SMULL_semi wn wm =
  Ok (Obj.magic wsmul arm_decl.reg_size wn wm)

(** val arm_SMULL_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_SMULL_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = SMULL in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
  ((coq_E arm_decl (S (S O))) :: ((coq_E arm_decl (S (S (S O)))) :: []));
  id_tout = ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_out =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl O) :: [])); id_semi =
  (Obj.magic arm_SMULL_semi); id_args_kinds = ak_reg_reg_reg_reg; id_nargs =
  (S (S (S (S O)))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn));
  id_safe = []; id_pp_asm = (pp_arm_op mn opts) }

(** val arm_SMLAL_semi :
    sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_SMLAL_semi dlo dhi wn wm =
  let (hi, lo) = wsmul arm_decl.reg_size wn wm in
  Ok (Obj.magic wdadds arm_decl.reg_size dhi dlo hi lo)

(** val arm_SMLAL_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_SMLAL_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = SMLAL in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: ((sreg arm_decl) :: ((sreg arm_decl) :: []))));
  id_in =
  ((coq_E arm_decl O) :: ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S
                                                       O))) :: ((coq_E
                                                                  arm_decl (S
                                                                  (S (S O)))) :: []))));
  id_tout = ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_out =
  ((coq_E arm_decl O) :: ((coq_E arm_decl (S O)) :: [])); id_semi =
  (Obj.magic arm_SMLAL_semi); id_args_kinds = ak_reg_reg_reg_reg; id_nargs =
  (S (S (S (S O)))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn));
  id_safe = []; id_pp_asm = (pp_arm_op mn opts) }

(** val arm_SMMUL_semi : sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_SMMUL_semi wn wm =
  Ok (wmulhs arm_decl.reg_size wn wm)

(** val arm_SMMUL_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_SMMUL_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = SMMUL in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
  ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []); id_semi =
  (Obj.magic arm_SMMUL_semi); id_args_kinds = ak_reg_reg_reg; id_nargs = (S
  (S (S O))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
  id_pp_asm = (pp_arm_op mn opts) }

(** val arm_SMMULR_semi : sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_SMMULR_semi wn wm =
  Ok
    (high_bits arm_decl.reg_size
      (Z.add
        (Z.mul (wsigned arm_decl.reg_size wn) (wsigned arm_decl.reg_size wm))
        (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        Coq_xH))))))))))))))))))))))))))))))))))

(** val arm_SMMULR_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_SMMULR_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = SMMULR in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
  ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []); id_semi =
  (Obj.magic arm_SMMULR_semi); id_args_kinds = ak_reg_reg_reg; id_nargs = (S
  (S (S O))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
  id_pp_asm = (pp_arm_op mn opts) }

(** val get_hw :
    halfword -> (register, __, __, rflag, condt) wreg -> GRing.ComRing.sort **)

let get_hw hw x =
  match split_vec arm_decl.reg_size (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S O)))))))))))))))) x with
  | [] -> GRing.zero (GRing.ComRing.zmodType (word U16))
  | lo :: l ->
    (match l with
     | [] -> GRing.zero (GRing.ComRing.zmodType (word U16))
     | hi :: l0 ->
       (match l0 with
        | [] -> (match hw with
                 | HWB -> Obj.magic lo
                 | HWT -> Obj.magic hi)
        | _ :: _ -> GRing.zero (GRing.ComRing.zmodType (word U16))))

(** val arm_smul_hw_semi :
    halfword -> halfword -> (register, __, __, rflag, condt) wreg ->
    (register, __, __, rflag, condt) wreg -> (register, __, __, rflag, condt)
    wreg exec **)

let arm_smul_hw_semi hwn hwm wn wm =
  let n = get_hw hwn wn in
  let m = get_hw hwm wm in
  let r = Z.mul (wsigned U16 n) (wsigned U16 m) in Ok (wrepr U32 r)

(** val arm_smul_hw_instr :
    arm_options -> halfword -> halfword -> (register, __, __, rflag, condt)
    instr_desc_t **)

let arm_smul_hw_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  (fun hwn hwm ->
  let mn = SMUL_hw (hwn, hwm) in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
  ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []); id_semi =
  (Obj.magic arm_smul_hw_semi hwn hwm); id_args_kinds = ak_reg_reg_reg;
  id_nargs = (S (S (S O))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn));
  id_safe = []; id_pp_asm = (pp_arm_op mn opts) })

(** val arm_smla_hw_semi :
    halfword -> halfword -> (register, __, __, rflag, condt) wreg ->
    (register, __, __, rflag, condt) wreg -> (register, __, __, rflag, condt)
    wreg -> (register, __, __, rflag, condt) wreg exec **)

let arm_smla_hw_semi hwn hwm wn wm acc =
  let n = get_hw hwn wn in
  let m = get_hw hwm wm in
  let r =
    Z.add (Z.mul (wsigned U16 n) (wsigned U16 m))
      (wsigned arm_decl.reg_size acc)
  in
  Ok (wrepr U32 r)

(** val arm_smla_hw_instr :
    arm_options -> halfword -> halfword -> (register, __, __, rflag, condt)
    instr_desc_t **)

let arm_smla_hw_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  (fun hwn hwm ->
  let mn = SMLA_hw (hwn, hwm) in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: ((sreg arm_decl) :: []))); id_in =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: ((coq_E arm_decl
                                                               (S (S (S O)))) :: [])));
  id_tout = ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []);
  id_semi = (Obj.magic arm_smla_hw_semi hwn hwm); id_args_kinds =
  ak_reg_reg_reg_reg; id_nargs = (S (S (S (S O)))); id_str_jas =
  (pp_s (string_of_arm_mnemonic0 mn)); id_safe = []; id_pp_asm =
  (pp_arm_op mn opts) })

(** val arm_smulw_hw_semi :
    halfword -> (register, __, __, rflag, condt) wreg -> (register, __, __,
    rflag, condt) wreg -> (register, __, __, rflag, condt) wreg exec **)

let arm_smulw_hw_semi hw wn wm =
  let m = get_hw hw wm in
  let res = Z.mul (wsigned arm_decl.reg_size wn) (wsigned U16 m) in
  let w = wrepr U64 res in
  Ok
  (winit U32 (fun i ->
    wbit_n U64 w
      (addn i (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))

(** val arm_smulw_hw_instr :
    arm_options -> halfword -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_smulw_hw_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  (fun hw ->
  let mn = SMULW_hw hw in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
  ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []); id_semi =
  (Obj.magic arm_smulw_hw_semi hw); id_args_kinds = ak_reg_reg_reg;
  id_nargs = (S (S (S O))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn));
  id_safe = []; id_pp_asm = (pp_arm_op mn opts) })

(** val arm_bitwise_semi :
    wsize -> (GRing.ComRing.sort -> GRing.ComRing.sort) ->
    (GRing.ComRing.sort -> GRing.ComRing.sort) -> (GRing.ComRing.sort ->
    GRing.ComRing.sort -> GRing.ComRing.sort) -> sem_tuple -> sem_tuple ->
    sem_tuple exec **)

let arm_bitwise_semi ws op0 op1 op wn wm =
  let res = op (op0 wn) (op1 wm) in
  Ok
  (Obj.magic ((Some (coq_NF_of_word ws res)), ((Some
    (coq_ZF_of_word ws res)), (None, res))))

(** val arm_AND_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_AND_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = AND in
  let x = { id_msb_flag = MSB_MERGE; id_tin =
    ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
    ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))
      ((sreg arm_decl) :: [])); id_out =
    (cat ad_nzc ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic arm_bitwise_semi arm_decl.reg_size (fun x -> x) (fun x -> x)
      (wand arm_decl.reg_size)); id_args_kinds =
    (cat ak_reg_reg_reg (ak_reg_reg_imm arm_decl)); id_nargs = (S (S (S O)));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  let x0 =
    match opts.has_shift with
    | Some sk ->
      mk_shifted sk x (mk_semi2_2_shifted (sreg arm_decl) sk x.id_semi)
    | None -> x
  in
  if opts.set_flags then x0 else drop_nzc x0

(** val arm_BFC_semi :
    (register, __, __, rflag, condt) wreg -> GRing.ComRing.sort ->
    GRing.ComRing.sort -> (register, __, __, rflag, condt) wreg exec **)

let arm_BFC_semi x lsb width =
  let lsbit = wunsigned U8 lsb in
  let nbits = wunsigned U8 width in
  if Z.ltb lsbit (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
  then if Z.leb (Zpos Coq_xH) nbits
       then if Z.leb nbits
                 (Z.sub (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                   Coq_xH)))))) lsbit)
            then let msbit = Z.sub (Z.add lsbit nbits) (Zpos Coq_xH) in
                 let mk = fun i ->
                   if (&&) (Nat.leb (Z.to_nat lsbit) i)
                        (Nat.leb i (Z.to_nat msbit))
                   then false
                   else wbit_n arm_decl.reg_size x i
                 in
                 Ok (winit arm_decl.reg_size mk)
            else Error E.no_semantics
       else Error E.no_semantics
  else Error E.no_semantics

(** val arm_BFC_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_BFC_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = BFC in
  { id_msb_flag = MSB_MERGE; id_tin = ((sreg arm_decl) :: ((Coq_sword
  U8) :: ((Coq_sword U8) :: []))); id_in =
  ((coq_E arm_decl O) :: ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S
                                                       O))) :: [])));
  id_tout = ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []);
  id_semi = (Obj.magic arm_BFC_semi); id_args_kinds = ak_reg_imm8_imm8;
  id_nargs = (S (S (S O))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn));
  id_safe = []; id_pp_asm = (pp_arm_op mn opts) }

(** val arm_BFI_semi :
    (register, __, __, rflag, condt) wreg -> (register, __, __, rflag, condt)
    wreg -> GRing.ComRing.sort -> GRing.ComRing.sort -> (register, __, __,
    rflag, condt) wreg exec **)

let arm_BFI_semi x y lsb width =
  let lsbit = wunsigned U8 lsb in
  let nbits = wunsigned U8 width in
  if Z.ltb lsbit (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
  then if Z.leb (Zpos Coq_xH) nbits
       then if Z.leb nbits
                 (Z.sub (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                   Coq_xH)))))) lsbit)
            then let msbit = Z.sub (Z.add lsbit nbits) (Zpos Coq_xH) in
                 let mk = fun i ->
                   if (&&) (Nat.leb (Z.to_nat lsbit) i)
                        (Nat.leb i (Z.to_nat msbit))
                   then wbit_n arm_decl.reg_size y (subn i (Z.to_nat lsbit))
                   else wbit_n arm_decl.reg_size x i
                 in
                 Ok (winit arm_decl.reg_size mk)
            else Error E.no_semantics
       else Error E.no_semantics
  else Error E.no_semantics

(** val arm_BFI_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_BFI_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = BFI in
  { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: ((sreg arm_decl) :: ((Coq_sword U8) :: ((Coq_sword
  U8) :: [])))); id_in =
  ((coq_E arm_decl O) :: ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S
                                                       O))) :: ((coq_E
                                                                  arm_decl (S
                                                                  (S (S O)))) :: []))));
  id_tout = ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []);
  id_semi = (Obj.magic arm_BFI_semi); id_args_kinds = ak_reg_reg_imm8_imm8;
  id_nargs = (S (S (S (S O)))); id_str_jas =
  (pp_s (string_of_arm_mnemonic0 mn)); id_safe = []; id_pp_asm =
  (pp_arm_op mn opts) }

(** val arm_BIC_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_BIC_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = BIC in
  let x = { id_msb_flag = MSB_MERGE; id_tin =
    ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
    ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))
      ((sreg arm_decl) :: [])); id_out =
    (cat ad_nzc ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic arm_bitwise_semi arm_decl.reg_size (fun x -> x)
      (wnot arm_decl.reg_size) (wand arm_decl.reg_size)); id_args_kinds =
    (cat ak_reg_reg_reg (ak_reg_reg_imm arm_decl)); id_nargs = (S (S (S O)));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  let x0 =
    match opts.has_shift with
    | Some sk ->
      mk_shifted sk x (mk_semi2_2_shifted (sreg arm_decl) sk x.id_semi)
    | None -> x
  in
  if opts.set_flags then x0 else drop_nzc x0

(** val arm_EOR_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_EOR_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = EOR in
  let x = { id_msb_flag = MSB_MERGE; id_tin =
    ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
    ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))
      ((sreg arm_decl) :: [])); id_out =
    (cat ad_nzc ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic arm_bitwise_semi arm_decl.reg_size (fun x -> x) (fun x -> x)
      (wxor arm_decl.reg_size)); id_args_kinds =
    (cat ak_reg_reg_reg (ak_reg_reg_imm arm_decl)); id_nargs = (S (S (S O)));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  let x0 =
    match opts.has_shift with
    | Some sk ->
      mk_shifted sk x (mk_semi2_2_shifted (sreg arm_decl) sk x.id_semi)
    | None -> x
  in
  if opts.set_flags then x0 else drop_nzc x0

(** val arm_MVN_semi : sem_tuple -> sem_tuple exec **)

let arm_MVN_semi wn =
  let res = wnot arm_decl.reg_size wn in
  Ok
  (Obj.magic ((Some (coq_NF_of_word arm_decl.reg_size res)), ((Some
    (coq_ZF_of_word arm_decl.reg_size res)), (None, res))))

(** val arm_MVN_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_MVN_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = MVN in
  let x = { id_msb_flag = MSB_MERGE; id_tin = ((sreg arm_decl) :: []);
    id_in = ((coq_E arm_decl (S O)) :: []); id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))
      ((sreg arm_decl) :: [])); id_out =
    (cat ad_nzc ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic arm_MVN_semi); id_args_kinds =
    (cat ak_reg_reg (ak_reg_imm arm_decl)); id_nargs = (S (S O));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  let x0 =
    match opts.has_shift with
    | Some sk -> mk_shifted sk x (mk_semi1_shifted sk x.id_semi)
    | None -> x
  in
  if opts.set_flags then x0 else drop_nzc x0

(** val arm_ORR_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_ORR_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = ORR in
  let x = { id_msb_flag = MSB_MERGE; id_tin =
    ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
    ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))
      ((sreg arm_decl) :: [])); id_out =
    (cat ad_nzc ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic arm_bitwise_semi arm_decl.reg_size (fun x -> x) (fun x -> x)
      (wor arm_decl.reg_size)); id_args_kinds =
    (cat ak_reg_reg_reg (ak_reg_reg_imm arm_decl)); id_nargs = (S (S (S O)));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  let x0 =
    match opts.has_shift with
    | Some sk ->
      mk_shifted sk x (mk_semi2_2_shifted (sreg arm_decl) sk x.id_semi)
    | None -> x
  in
  if opts.set_flags then x0 else drop_nzc x0

(** val arm_ASR_semi : sem_tuple -> GRing.ComRing.sort -> sem_tuple exec **)

let arm_ASR_semi wn wsham =
  let sham = wunsigned U8 wsham in
  let res = wsar arm_decl.reg_size wn sham in
  Ok
  (Obj.magic ((Some (coq_NF_of_word arm_decl.reg_size res)), ((Some
    (coq_ZF_of_word arm_decl.reg_size res)), ((Some
    (msb arm_decl.reg_size res)), res))))

(** val arm_ASR_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_ASR_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = ASR in
  let x = { id_msb_flag = MSB_MERGE; id_tin = ((sreg arm_decl) :: ((Coq_sword
    U8) :: [])); id_in =
    ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))
      ((sreg arm_decl) :: [])); id_out =
    (cat ad_nzc ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic arm_ASR_semi); id_args_kinds =
    (cat ak_reg_reg_reg (ak_reg_reg_imm arm_decl)); id_nargs = (S (S (S O)));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  if opts.set_flags then x else drop_nzc x

(** val arm_LSL_semi : sem_tuple -> GRing.ComRing.sort -> sem_tuple exec **)

let arm_LSL_semi wn wsham =
  let sham = wunsigned U8 wsham in
  let res = wshl arm_decl.reg_size wn sham in
  Ok
  (Obj.magic ((Some (coq_NF_of_word arm_decl.reg_size res)), ((Some
    (coq_ZF_of_word arm_decl.reg_size res)), ((Some
    (msb arm_decl.reg_size res)), res))))

(** val arm_LSL_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_LSL_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = LSL in
  let x = { id_msb_flag = MSB_MERGE; id_tin = ((sreg arm_decl) :: ((Coq_sword
    U8) :: [])); id_in =
    ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))
      ((sreg arm_decl) :: [])); id_out =
    (cat ad_nzc ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic arm_LSL_semi); id_args_kinds =
    (cat ak_reg_reg_reg (ak_reg_reg_imm arm_decl)); id_nargs = (S (S (S O)));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  if opts.set_flags then x else drop_nzc x

(** val arm_LSR_semi : sem_tuple -> GRing.ComRing.sort -> sem_tuple exec **)

let arm_LSR_semi wn wsham =
  let sham = wunsigned U8 wsham in
  let res = wshr arm_decl.reg_size wn sham in
  Ok
  (Obj.magic ((Some (coq_NF_of_word arm_decl.reg_size res)), ((Some
    (coq_ZF_of_word arm_decl.reg_size res)), ((Some
    (msb arm_decl.reg_size res)), res))))

(** val arm_LSR_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_LSR_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = LSR in
  let x = { id_msb_flag = MSB_MERGE; id_tin = ((sreg arm_decl) :: ((Coq_sword
    U8) :: [])); id_in =
    ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))
      ((sreg arm_decl) :: [])); id_out =
    (cat ad_nzc ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic arm_LSR_semi); id_args_kinds =
    (cat ak_reg_reg_reg (ak_reg_reg_imm arm_decl)); id_nargs = (S (S (S O)));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  if opts.set_flags then x else drop_nzc x

(** val arm_ROR_semi : sem_tuple -> GRing.ComRing.sort -> sem_tuple exec **)

let arm_ROR_semi wn wsham =
  let sham = wunsigned U8 wsham in
  let res = wror arm_decl.reg_size wn sham in
  Ok
  (Obj.magic ((Some (coq_NF_of_word arm_decl.reg_size res)), ((Some
    (coq_ZF_of_word arm_decl.reg_size res)), ((Some
    (msb arm_decl.reg_size res)), res))))

(** val arm_ROR_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_ROR_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = ROR in
  let x = { id_msb_flag = MSB_MERGE; id_tin = ((sreg arm_decl) :: ((Coq_sword
    U8) :: [])); id_in =
    ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))
      ((sreg arm_decl) :: [])); id_out =
    (cat ad_nzc ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic arm_ROR_semi); id_args_kinds =
    (cat ak_reg_reg_reg (ak_reg_reg_imm arm_decl)); id_nargs = (S (S (S O)));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  if opts.set_flags then x else drop_nzc x

(** val mk_rev_instr :
    arm_options -> arm_mnemonic -> sem_tuple exec sem_prod -> (register, __,
    __, rflag, condt) instr_desc_t **)

let mk_rev_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  (fun mn semi -> { id_msb_flag = MSB_MERGE; id_tin =
  ((sreg arm_decl) :: []); id_in = ((coq_E arm_decl (S O)) :: []); id_tout =
  ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []); id_semi =
  semi; id_args_kinds = ak_reg_reg; id_nargs = (S (S O)); id_str_jas =
  (pp_s (string_of_arm_mnemonic0 mn)); id_safe = []; id_pp_asm =
  (pp_arm_op mn opts) })

(** val arm_REV_semi : sem_tuple -> sem_tuple exec **)

let arm_REV_semi w =
  Ok (wbswap arm_decl.reg_size w)

(** val arm_REV16_semi : sem_tuple -> sem_tuple exec **)

let arm_REV16_semi w =
  Ok (lift1_vec U16 (wbswap U16) U32 w)

(** val arm_REVSH_semi : sem_tuple -> sem_tuple exec **)

let arm_REVSH_semi w =
  Ok (sign_extend U32 U16 (wbswap U16 (zero_extend U16 arm_decl.reg_size w)))

(** val arm_REV_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_REV_instr opts =
  mk_rev_instr opts REV (Obj.magic arm_REV_semi)

(** val arm_REV16_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_REV16_instr opts =
  mk_rev_instr opts REV16 (Obj.magic arm_REV16_semi)

(** val arm_REVSH_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_REVSH_instr opts =
  mk_rev_instr opts REVSH (Obj.magic arm_REVSH_semi)

(** val arm_ADR_semi : sem_tuple -> sem_tuple exec **)

let arm_ADR_semi wn =
  Ok wn

(** val arm_ADR_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_ADR_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = ADR in
  { id_msb_flag = MSB_MERGE; id_tin = ((sreg arm_decl) :: []); id_in =
  ((coq_Ec arm_decl (S O)) :: []); id_tout = ((sreg arm_decl) :: []);
  id_out = ((coq_E arm_decl O) :: []); id_semi = (Obj.magic arm_ADR_semi);
  id_args_kinds = ak_reg_addr; id_nargs = (S (S O)); id_str_jas =
  (pp_s (string_of_arm_mnemonic0 mn)); id_safe = []; id_pp_asm =
  (pp_arm_op mn opts) }

(** val arm_MOV_semi : sem_tuple -> sem_tuple exec **)

let arm_MOV_semi wn =
  Ok
    (Obj.magic ((Some (coq_NF_of_word arm_decl.reg_size wn)), ((Some
      (coq_ZF_of_word arm_decl.reg_size wn)), (None, wn))))

(** val arm_MOV_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_MOV_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = MOV in
  let x = { id_msb_flag = MSB_MERGE; id_tin = ((sreg arm_decl) :: []);
    id_in = ((coq_E arm_decl (S O)) :: []); id_tout =
    (cat (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))
      ((sreg arm_decl) :: [])); id_out =
    (cat ad_nzc ((coq_E arm_decl O) :: [])); id_semi =
    (Obj.magic arm_MOV_semi); id_args_kinds =
    (cat ak_reg_reg (ak_reg_imm arm_decl)); id_nargs = (S (S O));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  if opts.set_flags then x else drop_nzc x

(** val arm_MOVT_semi : sem_tuple -> GRing.ComRing.sort -> sem_tuple exec **)

let arm_MOVT_semi wn wm =
  let hi =
    wshl arm_decl.reg_size (zero_extend arm_decl.reg_size U16 wm) (Zpos
      (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
  in
  let mask = zero_extend arm_decl.reg_size U16 (wrepr U16 (Zneg Coq_xH)) in
  Ok (wor arm_decl.reg_size hi (wand arm_decl.reg_size wn mask))

(** val arm_MOVT_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_MOVT_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = MOVT in
  { id_msb_flag = MSB_MERGE; id_tin = ((sreg arm_decl) :: ((Coq_sword
  U16) :: [])); id_in =
  ((coq_E arm_decl O) :: ((coq_E arm_decl (S O)) :: [])); id_tout =
  ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []); id_semi =
  (Obj.magic arm_MOVT_semi); id_args_kinds = (((CAreg :: []) :: (((CAimm
  U16) :: []) :: [])) :: []); id_nargs = (S (S O)); id_str_jas =
  (pp_s (string_of_arm_mnemonic0 mn)); id_safe = []; id_pp_asm =
  (pp_arm_op mn opts) }

(** val bit_field_extract_semi :
    ((register, __, __, rflag, condt) wreg -> coq_Z -> (register, __, __,
    rflag, condt) wreg) -> (register, __, __, rflag, condt) wreg ->
    GRing.ComRing.sort -> GRing.ComRing.sort -> (register, __, __, rflag,
    condt) wreg exec **)

let bit_field_extract_semi shr wn widx wwidth =
  let idx = wunsigned U8 widx in
  let width = wunsigned U8 wwidth in
  Ok
  (shr
    (wshl arm_decl.reg_size wn
      (Z.sub
        (Z.sub (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
          width) idx))
    (Z.sub (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))) width))

(** val arm_UBFX_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_UBFX_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = UBFX in
  { id_msb_flag = MSB_MERGE; id_tin = ((sreg arm_decl) :: ((Coq_sword
  U8) :: ((Coq_sword U8) :: []))); id_in =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: ((coq_E arm_decl
                                                               (S (S (S O)))) :: [])));
  id_tout = ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []);
  id_semi = (Obj.magic bit_field_extract_semi (wshr arm_decl.reg_size));
  id_args_kinds = (((CAreg :: []) :: ((CAreg :: []) :: (((CAimm
  U8) :: []) :: (((CAimm U8) :: []) :: [])))) :: []); id_nargs = (S (S (S (S
  O)))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
  id_pp_asm = (pp_arm_op mn opts) }

(** val extend_bits_semi :
    coq_Z -> (register, __, __, rflag, condt) wreg -> GRing.ComRing.sort ->
    (register, __, __, rflag, condt) wreg exec **)

let extend_bits_semi len wn wroram =
  let mask =
    wrepr arm_decl.reg_size
      (Z.sub (Z.pow (Zpos (Coq_xO Coq_xH)) len) (Zpos Coq_xH))
  in
  let roram = wunsigned U8 wroram in
  Ok (wand arm_decl.reg_size mask (wror arm_decl.reg_size wn roram))

(** val arm_UXTB_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_UXTB_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = UXTB in
  { id_msb_flag = MSB_MERGE; id_tin = ((sreg arm_decl) :: ((Coq_sword
  U8) :: [])); id_in =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
  ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []); id_semi =
  (Obj.magic extend_bits_semi (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))));
  id_args_kinds = ak_reg_reg_imm8; id_nargs = (S (S (S O))); id_str_jas =
  (pp_s (string_of_arm_mnemonic0 mn)); id_safe = []; id_pp_asm =
  (pp_arm_op mn opts) }

(** val arm_UXTH_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_UXTH_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = UXTH in
  { id_msb_flag = MSB_MERGE; id_tin = ((sreg arm_decl) :: ((Coq_sword
  U8) :: [])); id_in =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: [])); id_tout =
  ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []); id_semi =
  (Obj.magic extend_bits_semi (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    Coq_xH)))))); id_args_kinds = ak_reg_reg_imm16; id_nargs = (S (S (S O)));
  id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = []; id_pp_asm =
  (pp_arm_op mn opts) }

(** val arm_SBFX_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_SBFX_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = SBFX in
  { id_msb_flag = MSB_MERGE; id_tin = ((sreg arm_decl) :: ((Coq_sword
  U8) :: ((Coq_sword U8) :: []))); id_in =
  ((coq_E arm_decl (S O)) :: ((coq_E arm_decl (S (S O))) :: ((coq_E arm_decl
                                                               (S (S (S O)))) :: [])));
  id_tout = ((sreg arm_decl) :: []); id_out = ((coq_E arm_decl O) :: []);
  id_semi = (Obj.magic bit_field_extract_semi (wsar arm_decl.reg_size));
  id_args_kinds = (((CAreg :: []) :: ((CAreg :: []) :: (((CAimm
  U8) :: []) :: (((CAimm U8) :: []) :: [])))) :: []); id_nargs = (S (S (S (S
  O)))); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
  id_pp_asm = (pp_arm_op mn opts) }

(** val arm_CMP_semi : sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_CMP_semi wn wm =
  let wmnot = wnot arm_decl.reg_size wm in
  let res =
    nzcv_of_aluop arm_decl.reg_size
      (GRing.add (GRing.ComRing.zmodType (word arm_decl.reg_size))
        (GRing.add (GRing.ComRing.zmodType (word arm_decl.reg_size)) wn wmnot)
        (GRing.one (GRing.ComRing.ringType (word arm_decl.reg_size))))
      (Z.add
        (Z.add (wunsigned arm_decl.reg_size wn)
          (wunsigned arm_decl.reg_size wmnot)) (Zpos Coq_xH))
      (Z.add
        (Z.add (wsigned arm_decl.reg_size wn)
          (wsigned arm_decl.reg_size wmnot)) (Zpos Coq_xH))
  in
  Ok res

(** val arm_CMP_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_CMP_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = CMP in
  let x = { id_msb_flag = MSB_MERGE; id_tin =
    ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
    ((coq_E arm_decl O) :: ((coq_E arm_decl (S O)) :: [])); id_tout =
    (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))); id_out =
    ad_nzcv; id_semi = (Obj.magic arm_CMP_semi); id_args_kinds =
    (cat ak_reg_reg (ak_reg_imm arm_decl)); id_nargs = (S (S O));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  (match opts.has_shift with
   | Some sk ->
     mk_shifted sk x (mk_semi2_2_shifted (sreg arm_decl) sk x.id_semi)
   | None -> x)

(** val arm_TST_semi : sem_tuple -> sem_tuple -> sem_tuple exec **)

let arm_TST_semi wn wm =
  let res = wand arm_decl.reg_size wn wm in
  Ok
  (Obj.magic ((Some (coq_NF_of_word arm_decl.reg_size res)), ((Some
    (coq_ZF_of_word arm_decl.reg_size res)), (Some false))))

(** val arm_TST_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_TST_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = TST in
  let x = { id_msb_flag = MSB_MERGE; id_tin =
    ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
    ((coq_E arm_decl O) :: ((coq_E arm_decl (S O)) :: [])); id_tout =
    (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: []))); id_out = ad_nzc;
    id_semi = (Obj.magic arm_TST_semi); id_args_kinds =
    (cat ak_reg_reg (ak_reg_imm arm_decl)); id_nargs = (S (S O));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  (match opts.has_shift with
   | Some sk ->
     mk_shifted sk x (mk_semi2_2_shifted (sreg arm_decl) sk x.id_semi)
   | None -> x)

(** val arm_CMN_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_CMN_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = CMN in
  let x = { id_msb_flag = MSB_MERGE; id_tin =
    ((sreg arm_decl) :: ((sreg arm_decl) :: [])); id_in =
    ((coq_E arm_decl O) :: ((coq_E arm_decl (S O)) :: [])); id_tout =
    (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))); id_out =
    ad_nzcv; id_semi =
    (Obj.magic (fun wn wm ->
      rtuple_drop5th Coq_sbool Coq_sbool Coq_sbool Coq_sbool (sreg arm_decl)
        (arm_ADD_semi wn wm))); id_args_kinds =
    (cat ak_reg_reg (ak_reg_imm arm_decl)); id_nargs = (S (S O));
    id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = [];
    id_pp_asm = (pp_arm_op mn opts) }
  in
  (match opts.has_shift with
   | Some sk ->
     mk_shifted sk x (mk_semi2_2_shifted (sreg arm_decl) sk x.id_semi)
   | None -> x)

(** val arm_extend_semi :
    wsize -> bool -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort exec **)

let arm_extend_semi ws sign ws' wn =
  let f = if sign then sign_extend else zero_extend in Ok (f ws' ws wn)

(** val arm_load_instr :
    arm_options -> arm_mnemonic -> (register, __, __, rflag, condt)
    instr_desc_t **)

let arm_load_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  (fun mn ->
  let ws = match wsize_of_load_mn mn with
           | Some ws' -> ws'
           | None -> U32 in
  { id_msb_flag = MSB_MERGE; id_tin = ((Coq_sword ws) :: []); id_in =
  ((coq_E arm_decl (S O)) :: []); id_tout = ((sreg arm_decl) :: []); id_out =
  ((coq_E arm_decl O) :: []); id_semi =
  (Obj.magic arm_extend_semi ws (isSome (wsize_of_sload_mn mn))
    arm_decl.reg_size); id_args_kinds = ak_reg_addr; id_nargs = (S (S O));
  id_str_jas = (pp_s (string_of_arm_mnemonic0 mn)); id_safe = []; id_pp_asm =
  (pp_arm_op mn opts) })

(** val arm_store_instr :
    arm_options -> arm_mnemonic -> (register, __, __, rflag, condt)
    instr_desc_t **)

let arm_store_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  (fun mn ->
  let ws = match wsize_of_store_mn mn with
           | Some ws' -> ws'
           | None -> U32 in
  { id_msb_flag = MSB_MERGE; id_tin = ((Coq_sword ws) :: []); id_in =
  ((coq_E arm_decl O) :: []); id_tout = ((Coq_sword ws) :: []); id_out =
  ((coq_E arm_decl (S O)) :: []); id_semi =
  (Obj.magic arm_extend_semi ws false ws); id_args_kinds = ak_reg_addr;
  id_nargs = (S (S O)); id_str_jas = (pp_s (string_of_arm_mnemonic0 mn));
  id_safe = []; id_pp_asm = (pp_arm_op mn opts) })

(** val arm_CLZ_instr :
    arm_options -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_CLZ_instr opts =
  let string_of_arm_mnemonic0 = fun mn ->
    append (string_of_arm_mnemonic mn)
      (append (if opts.set_flags then 'S'::[] else [])
        (if opts.is_conditional then 'c'::('c'::[]) else []))
  in
  let mn = CLZ in
  { id_msb_flag = MSB_MERGE; id_tin = ((sreg arm_decl) :: []); id_in =
  ((coq_E arm_decl (S O)) :: []); id_tout = ((sreg arm_decl) :: []); id_out =
  ((coq_E arm_decl O) :: []); id_semi =
  (Obj.magic (fun w -> Ok (leading_zero arm_decl.reg_size w)));
  id_args_kinds = ak_reg_reg; id_nargs = (S (S O)); id_str_jas =
  (pp_s (string_of_arm_mnemonic0 mn)); id_safe = []; id_pp_asm =
  (pp_arm_op mn opts) }

(** val mn_desc :
    arm_options -> arm_mnemonic -> (register, __, __, rflag, condt)
    instr_desc_t **)

let mn_desc opts = function
| ADD -> arm_ADD_instr opts
| ADC -> arm_ADC_instr opts
| MUL -> arm_MUL_instr opts
| MLA -> arm_MLA_instr opts
| MLS -> arm_MLS_instr opts
| SDIV -> arm_SDIV_instr opts
| SUB -> arm_SUB_instr opts
| RSB -> arm_RSB_instr opts
| UDIV -> arm_UDIV_instr opts
| UMULL -> arm_UMULL_instr opts
| UMAAL -> arm_UMAAL_instr opts
| UMLAL -> arm_UMLAL_instr opts
| SMULL -> arm_SMULL_instr opts
| SMLAL -> arm_SMLAL_instr opts
| SMMUL -> arm_SMMUL_instr opts
| SMMULR -> arm_SMMULR_instr opts
| SMUL_hw (hw0, hw1) -> arm_smul_hw_instr opts hw0 hw1
| SMLA_hw (hw0, hw1) -> arm_smla_hw_instr opts hw0 hw1
| SMULW_hw hw -> arm_smulw_hw_instr opts hw
| AND -> arm_AND_instr opts
| BFC -> arm_BFC_instr opts
| BFI -> arm_BFI_instr opts
| BIC -> arm_BIC_instr opts
| EOR -> arm_EOR_instr opts
| MVN -> arm_MVN_instr opts
| ORR -> arm_ORR_instr opts
| ASR -> arm_ASR_instr opts
| LSL -> arm_LSL_instr opts
| LSR -> arm_LSR_instr opts
| ROR -> arm_ROR_instr opts
| REV -> arm_REV_instr opts
| REV16 -> arm_REV16_instr opts
| REVSH -> arm_REVSH_instr opts
| ADR -> arm_ADR_instr opts
| MOV -> arm_MOV_instr opts
| MOVT -> arm_MOVT_instr opts
| UBFX -> arm_UBFX_instr opts
| UXTB -> arm_UXTB_instr opts
| UXTH -> arm_UXTH_instr opts
| SBFX -> arm_SBFX_instr opts
| CLZ -> arm_CLZ_instr opts
| CMP -> arm_CMP_instr opts
| TST -> arm_TST_instr opts
| CMN -> arm_CMN_instr opts
| STR -> arm_store_instr opts STR
| STRB -> arm_store_instr opts STRB
| STRH -> arm_store_instr opts STRH
| x -> arm_load_instr opts x

(** val arm_instr_desc :
    arm_op -> (register, __, __, rflag, condt) instr_desc_t **)

let arm_instr_desc = function
| ARM_op (mn, opts) ->
  let x = mn_desc opts mn in if opts.is_conditional then mk_cond x else x

(** val arm_prim_string : (char list * arm_op prim_constructor) list **)

let arm_prim_string =
  (('A'::('D'::('D'::[]))), (PrimARM (fun sf ic -> ARM_op (ADD, { set_flags =
    sf; is_conditional = ic; has_shift =
    None })))) :: ((('A'::('D'::('C'::[]))), (PrimARM (fun sf ic -> ARM_op
    (ADC, { set_flags = sf; is_conditional = ic; has_shift =
    None })))) :: ((('M'::('U'::('L'::[]))), (PrimARM (fun sf ic -> ARM_op
    (MUL, { set_flags = sf; is_conditional = ic; has_shift =
    None })))) :: ((('M'::('L'::('A'::[]))), (PrimARM (fun sf ic -> ARM_op
    (MLA, { set_flags = sf; is_conditional = ic; has_shift =
    None })))) :: ((('M'::('L'::('S'::[]))), (PrimARM (fun sf ic -> ARM_op
    (MLS, { set_flags = sf; is_conditional = ic; has_shift =
    None })))) :: ((('S'::('D'::('I'::('V'::[])))), (PrimARM (fun sf ic ->
    ARM_op (SDIV, { set_flags = sf; is_conditional = ic; has_shift =
    None })))) :: ((('S'::('U'::('B'::[]))), (PrimARM (fun sf ic -> ARM_op
    (SUB, { set_flags = sf; is_conditional = ic; has_shift =
    None })))) :: ((('R'::('S'::('B'::[]))), (PrimARM (fun sf ic -> ARM_op
    (RSB, { set_flags = sf; is_conditional = ic; has_shift =
    None })))) :: ((('U'::('D'::('I'::('V'::[])))), (PrimARM (fun sf ic ->
    ARM_op (UDIV, { set_flags = sf; is_conditional = ic; has_shift =
    None })))) :: ((('U'::('M'::('U'::('L'::('L'::[]))))), (PrimARM
    (fun sf ic -> ARM_op (UMULL, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('U'::('M'::('A'::('A'::('L'::[]))))),
    (PrimARM (fun sf ic -> ARM_op (UMAAL, { set_flags = sf; is_conditional =
    ic; has_shift = None })))) :: ((('U'::('M'::('L'::('A'::('L'::[]))))),
    (PrimARM (fun sf ic -> ARM_op (UMLAL, { set_flags = sf; is_conditional =
    ic; has_shift = None })))) :: ((('S'::('M'::('U'::('L'::('L'::[]))))),
    (PrimARM (fun sf ic -> ARM_op (SMULL, { set_flags = sf; is_conditional =
    ic; has_shift = None })))) :: ((('S'::('M'::('L'::('A'::('L'::[]))))),
    (PrimARM (fun sf ic -> ARM_op (SMLAL, { set_flags = sf; is_conditional =
    ic; has_shift = None })))) :: ((('S'::('M'::('M'::('U'::('L'::[]))))),
    (PrimARM (fun sf ic -> ARM_op (SMMUL, { set_flags = sf; is_conditional =
    ic; has_shift =
    None })))) :: ((('S'::('M'::('M'::('U'::('L'::('R'::[])))))), (PrimARM
    (fun sf ic -> ARM_op (SMMULR, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('S'::('M'::('U'::('L'::('B'::('B'::[])))))),
    (PrimARM (fun sf ic -> ARM_op ((SMUL_hw (HWB, HWB)), { set_flags = sf;
    is_conditional = ic; has_shift =
    None })))) :: ((('S'::('M'::('U'::('L'::('B'::('T'::[])))))), (PrimARM
    (fun sf ic -> ARM_op ((SMUL_hw (HWB, HWT)), { set_flags = sf;
    is_conditional = ic; has_shift =
    None })))) :: ((('S'::('M'::('U'::('L'::('T'::('B'::[])))))), (PrimARM
    (fun sf ic -> ARM_op ((SMUL_hw (HWT, HWB)), { set_flags = sf;
    is_conditional = ic; has_shift =
    None })))) :: ((('S'::('M'::('U'::('L'::('T'::('T'::[])))))), (PrimARM
    (fun sf ic -> ARM_op ((SMUL_hw (HWT, HWT)), { set_flags = sf;
    is_conditional = ic; has_shift =
    None })))) :: ((('S'::('M'::('L'::('A'::('B'::('B'::[])))))), (PrimARM
    (fun sf ic -> ARM_op ((SMLA_hw (HWB, HWB)), { set_flags = sf;
    is_conditional = ic; has_shift =
    None })))) :: ((('S'::('M'::('L'::('A'::('B'::('T'::[])))))), (PrimARM
    (fun sf ic -> ARM_op ((SMLA_hw (HWB, HWT)), { set_flags = sf;
    is_conditional = ic; has_shift =
    None })))) :: ((('S'::('M'::('L'::('A'::('T'::('B'::[])))))), (PrimARM
    (fun sf ic -> ARM_op ((SMLA_hw (HWT, HWB)), { set_flags = sf;
    is_conditional = ic; has_shift =
    None })))) :: ((('S'::('M'::('L'::('A'::('T'::('T'::[])))))), (PrimARM
    (fun sf ic -> ARM_op ((SMLA_hw (HWT, HWT)), { set_flags = sf;
    is_conditional = ic; has_shift =
    None })))) :: ((('S'::('M'::('U'::('L'::('W'::('B'::[])))))), (PrimARM
    (fun sf ic -> ARM_op ((SMULW_hw HWB), { set_flags = sf; is_conditional =
    ic; has_shift =
    None })))) :: ((('S'::('M'::('U'::('L'::('W'::('T'::[])))))), (PrimARM
    (fun sf ic -> ARM_op ((SMULW_hw HWT), { set_flags = sf; is_conditional =
    ic; has_shift = None })))) :: ((('A'::('N'::('D'::[]))), (PrimARM
    (fun sf ic -> ARM_op (AND, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('B'::('F'::('C'::[]))), (PrimARM
    (fun sf ic -> ARM_op (BFC, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('B'::('F'::('I'::[]))), (PrimARM
    (fun sf ic -> ARM_op (BFI, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('B'::('I'::('C'::[]))), (PrimARM
    (fun sf ic -> ARM_op (BIC, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('E'::('O'::('R'::[]))), (PrimARM
    (fun sf ic -> ARM_op (EOR, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('M'::('V'::('N'::[]))), (PrimARM
    (fun sf ic -> ARM_op (MVN, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('O'::('R'::('R'::[]))), (PrimARM
    (fun sf ic -> ARM_op (ORR, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('A'::('S'::('R'::[]))), (PrimARM
    (fun sf ic -> ARM_op (ASR, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('L'::('S'::('L'::[]))), (PrimARM
    (fun sf ic -> ARM_op (LSL, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('L'::('S'::('R'::[]))), (PrimARM
    (fun sf ic -> ARM_op (LSR, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('R'::('O'::('R'::[]))), (PrimARM
    (fun sf ic -> ARM_op (ROR, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('R'::('E'::('V'::[]))), (PrimARM
    (fun sf ic -> ARM_op (REV, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('R'::('E'::('V'::('1'::('6'::[]))))),
    (PrimARM (fun sf ic -> ARM_op (REV16, { set_flags = sf; is_conditional =
    ic; has_shift = None })))) :: ((('R'::('E'::('V'::('S'::('H'::[]))))),
    (PrimARM (fun sf ic -> ARM_op (REVSH, { set_flags = sf; is_conditional =
    ic; has_shift = None })))) :: ((('A'::('D'::('R'::[]))), (PrimARM
    (fun sf ic -> ARM_op (ADR, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('M'::('O'::('V'::[]))), (PrimARM
    (fun sf ic -> ARM_op (MOV, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('M'::('O'::('V'::('T'::[])))), (PrimARM
    (fun sf ic -> ARM_op (MOVT, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('U'::('B'::('F'::('X'::[])))), (PrimARM
    (fun sf ic -> ARM_op (UBFX, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('U'::('X'::('T'::('B'::[])))), (PrimARM
    (fun sf ic -> ARM_op (UXTB, { set_flags = sf; is_conditional = ic;
    has_shift = (Some SROR) })))) :: ((('U'::('X'::('T'::('H'::[])))),
    (PrimARM (fun sf ic -> ARM_op (UXTH, { set_flags = sf; is_conditional =
    ic; has_shift = (Some SROR) })))) :: ((('S'::('B'::('F'::('X'::[])))),
    (PrimARM (fun sf ic -> ARM_op (SBFX, { set_flags = sf; is_conditional =
    ic; has_shift = None })))) :: ((('C'::('L'::('Z'::[]))), (PrimARM
    (fun sf ic -> ARM_op (CLZ, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('C'::('M'::('P'::[]))), (PrimARM
    (fun sf ic -> ARM_op (CMP, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('T'::('S'::('T'::[]))), (PrimARM
    (fun sf ic -> ARM_op (TST, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('C'::('M'::('N'::[]))), (PrimARM
    (fun sf ic -> ARM_op (CMN, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('L'::('D'::('R'::[]))), (PrimARM
    (fun sf ic -> ARM_op (LDR, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('L'::('D'::('R'::('B'::[])))), (PrimARM
    (fun sf ic -> ARM_op (LDRB, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('L'::('D'::('R'::('H'::[])))), (PrimARM
    (fun sf ic -> ARM_op (LDRH, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('L'::('D'::('R'::('S'::('B'::[]))))),
    (PrimARM (fun sf ic -> ARM_op (LDRSB, { set_flags = sf; is_conditional =
    ic; has_shift = None })))) :: ((('L'::('D'::('R'::('S'::('H'::[]))))),
    (PrimARM (fun sf ic -> ARM_op (LDRSH, { set_flags = sf; is_conditional =
    ic; has_shift = None })))) :: ((('S'::('T'::('R'::[]))), (PrimARM
    (fun sf ic -> ARM_op (STR, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('S'::('T'::('R'::('B'::[])))), (PrimARM
    (fun sf ic -> ARM_op (STRB, { set_flags = sf; is_conditional = ic;
    has_shift = None })))) :: ((('S'::('T'::('R'::('H'::[])))), (PrimARM
    (fun sf ic -> ARM_op (STRH, { set_flags = sf; is_conditional = ic;
    has_shift =
    None })))) :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val arm_op_decl : (register, __, __, rflag, condt, arm_op) asm_op_decl **)

let arm_op_decl =
  { Arch_decl._eqT = eqTC_arm_op; instr_desc_op = arm_instr_desc;
    Arch_decl.prim_string = arm_prim_string }

type arm_prog = (register, __, __, rflag, condt, arm_op) asm_prog
