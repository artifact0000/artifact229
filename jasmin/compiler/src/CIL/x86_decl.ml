open Arch_decl
open Eqtype
open Fintype
open Flag_combination
open Seq
open Utils0
open Wsize

(** val x86_reg_size : wsize **)

let x86_reg_size =
  U64

(** val x86_xreg_size : wsize **)

let x86_xreg_size =
  U256

type register =
| RAX
| RCX
| RDX
| RBX
| RSP
| RBP
| RSI
| RDI
| R8
| R9
| R10
| R11
| R12
| R13
| R14
| R15

type register_ext =
| MM0
| MM1
| MM2
| MM3
| MM4
| MM5
| MM6
| MM7

type xmm_register =
| XMM0
| XMM1
| XMM2
| XMM3
| XMM4
| XMM5
| XMM6
| XMM7
| XMM8
| XMM9
| XMM10
| XMM11
| XMM12
| XMM13
| XMM14
| XMM15

type rflag =
| CF
| PF
| ZF
| SF
| OF

type condt =
| O_ct
| NO_ct
| B_ct
| NB_ct
| E_ct
| NE_ct
| BE_ct
| NBE_ct
| S_ct
| NS_ct
| P_ct
| NP_ct
| L_ct
| NL_ct
| LE_ct
| NLE_ct

(** val register_beq : register -> register -> bool **)

let register_beq x y =
  match x with
  | RAX -> (match y with
            | RAX -> true
            | _ -> false)
  | RCX -> (match y with
            | RCX -> true
            | _ -> false)
  | RDX -> (match y with
            | RDX -> true
            | _ -> false)
  | RBX -> (match y with
            | RBX -> true
            | _ -> false)
  | RSP -> (match y with
            | RSP -> true
            | _ -> false)
  | RBP -> (match y with
            | RBP -> true
            | _ -> false)
  | RSI -> (match y with
            | RSI -> true
            | _ -> false)
  | RDI -> (match y with
            | RDI -> true
            | _ -> false)
  | R8 -> (match y with
           | R8 -> true
           | _ -> false)
  | R9 -> (match y with
           | R9 -> true
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
  | R13 -> (match y with
            | R13 -> true
            | _ -> false)
  | R14 -> (match y with
            | R14 -> true
            | _ -> false)
  | R15 -> (match y with
            | R15 -> true
            | _ -> false)

(** val register_eq_dec : register -> register -> bool **)

let register_eq_dec x y =
  let b = register_beq x y in if b then true else false

(** val reg_eq_axiom : register Equality.axiom **)

let reg_eq_axiom =
  eq_axiom_of_scheme register_beq

(** val reg_eqMixin : register Equality.mixin_of **)

let reg_eqMixin =
  { Equality.op = register_beq; Equality.mixin_of__1 = reg_eq_axiom }

(** val reg_eqType : Equality.coq_type **)

let reg_eqType =
  Obj.magic reg_eqMixin

(** val register_ext_beq : register_ext -> register_ext -> bool **)

let register_ext_beq x y =
  match x with
  | MM0 -> (match y with
            | MM0 -> true
            | _ -> false)
  | MM1 -> (match y with
            | MM1 -> true
            | _ -> false)
  | MM2 -> (match y with
            | MM2 -> true
            | _ -> false)
  | MM3 -> (match y with
            | MM3 -> true
            | _ -> false)
  | MM4 -> (match y with
            | MM4 -> true
            | _ -> false)
  | MM5 -> (match y with
            | MM5 -> true
            | _ -> false)
  | MM6 -> (match y with
            | MM6 -> true
            | _ -> false)
  | MM7 -> (match y with
            | MM7 -> true
            | _ -> false)

(** val register_ext_eq_dec : register_ext -> register_ext -> bool **)

let register_ext_eq_dec x y =
  let b = register_ext_beq x y in if b then true else false

(** val regx_eq_axiom : register_ext Equality.axiom **)

let regx_eq_axiom =
  eq_axiom_of_scheme register_ext_beq

(** val regx_eqMixin : register_ext Equality.mixin_of **)

let regx_eqMixin =
  { Equality.op = register_ext_beq; Equality.mixin_of__1 = regx_eq_axiom }

(** val regx_eqType : Equality.coq_type **)

let regx_eqType =
  Obj.magic regx_eqMixin

(** val xmm_register_beq : xmm_register -> xmm_register -> bool **)

let xmm_register_beq x y =
  match x with
  | XMM0 -> (match y with
             | XMM0 -> true
             | _ -> false)
  | XMM1 -> (match y with
             | XMM1 -> true
             | _ -> false)
  | XMM2 -> (match y with
             | XMM2 -> true
             | _ -> false)
  | XMM3 -> (match y with
             | XMM3 -> true
             | _ -> false)
  | XMM4 -> (match y with
             | XMM4 -> true
             | _ -> false)
  | XMM5 -> (match y with
             | XMM5 -> true
             | _ -> false)
  | XMM6 -> (match y with
             | XMM6 -> true
             | _ -> false)
  | XMM7 -> (match y with
             | XMM7 -> true
             | _ -> false)
  | XMM8 -> (match y with
             | XMM8 -> true
             | _ -> false)
  | XMM9 -> (match y with
             | XMM9 -> true
             | _ -> false)
  | XMM10 -> (match y with
              | XMM10 -> true
              | _ -> false)
  | XMM11 -> (match y with
              | XMM11 -> true
              | _ -> false)
  | XMM12 -> (match y with
              | XMM12 -> true
              | _ -> false)
  | XMM13 -> (match y with
              | XMM13 -> true
              | _ -> false)
  | XMM14 -> (match y with
              | XMM14 -> true
              | _ -> false)
  | XMM15 -> (match y with
              | XMM15 -> true
              | _ -> false)

(** val xmm_register_eq_dec : xmm_register -> xmm_register -> bool **)

let xmm_register_eq_dec x y =
  let b = xmm_register_beq x y in if b then true else false

(** val xreg_eq_axiom : xmm_register Equality.axiom **)

let xreg_eq_axiom =
  eq_axiom_of_scheme xmm_register_beq

(** val xreg_eqMixin : xmm_register Equality.mixin_of **)

let xreg_eqMixin =
  { Equality.op = xmm_register_beq; Equality.mixin_of__1 = xreg_eq_axiom }

(** val xreg_eqType : Equality.coq_type **)

let xreg_eqType =
  Obj.magic xreg_eqMixin

(** val rflag_beq : rflag -> rflag -> bool **)

let rflag_beq x y =
  match x with
  | CF -> (match y with
           | CF -> true
           | _ -> false)
  | PF -> (match y with
           | PF -> true
           | _ -> false)
  | ZF -> (match y with
           | ZF -> true
           | _ -> false)
  | SF -> (match y with
           | SF -> true
           | _ -> false)
  | OF -> (match y with
           | OF -> true
           | _ -> false)

(** val rflag_eq_dec : rflag -> rflag -> bool **)

let rflag_eq_dec x y =
  let b = rflag_beq x y in if b then true else false

(** val rflag_eq_axiom : rflag Equality.axiom **)

let rflag_eq_axiom =
  eq_axiom_of_scheme rflag_beq

(** val rflag_eqMixin : rflag Equality.mixin_of **)

let rflag_eqMixin =
  { Equality.op = rflag_beq; Equality.mixin_of__1 = rflag_eq_axiom }

(** val rflag_eqType : Equality.coq_type **)

let rflag_eqType =
  Obj.magic rflag_eqMixin

(** val condt_beq : condt -> condt -> bool **)

let condt_beq x y =
  match x with
  | O_ct -> (match y with
             | O_ct -> true
             | _ -> false)
  | NO_ct -> (match y with
              | NO_ct -> true
              | _ -> false)
  | B_ct -> (match y with
             | B_ct -> true
             | _ -> false)
  | NB_ct -> (match y with
              | NB_ct -> true
              | _ -> false)
  | E_ct -> (match y with
             | E_ct -> true
             | _ -> false)
  | NE_ct -> (match y with
              | NE_ct -> true
              | _ -> false)
  | BE_ct -> (match y with
              | BE_ct -> true
              | _ -> false)
  | NBE_ct -> (match y with
               | NBE_ct -> true
               | _ -> false)
  | S_ct -> (match y with
             | S_ct -> true
             | _ -> false)
  | NS_ct -> (match y with
              | NS_ct -> true
              | _ -> false)
  | P_ct -> (match y with
             | P_ct -> true
             | _ -> false)
  | NP_ct -> (match y with
              | NP_ct -> true
              | _ -> false)
  | L_ct -> (match y with
             | L_ct -> true
             | _ -> false)
  | NL_ct -> (match y with
              | NL_ct -> true
              | _ -> false)
  | LE_ct -> (match y with
              | LE_ct -> true
              | _ -> false)
  | NLE_ct -> (match y with
               | NLE_ct -> true
               | _ -> false)

(** val condt_eq_dec : condt -> condt -> bool **)

let condt_eq_dec x y =
  let b = condt_beq x y in if b then true else false

(** val condt_eq_axiom : condt Equality.axiom **)

let condt_eq_axiom =
  eq_axiom_of_scheme condt_beq

(** val condt_eqMixin : condt Equality.mixin_of **)

let condt_eqMixin =
  { Equality.op = condt_beq; Equality.mixin_of__1 = condt_eq_axiom }

(** val condt_eqType : Equality.coq_type **)

let condt_eqType =
  Obj.magic condt_eqMixin

(** val registers : register list **)

let registers =
  RAX :: (RCX :: (RDX :: (RBX :: (RSP :: (RBP :: (RSI :: (RDI :: (R8 :: (R9 :: (R10 :: (R11 :: (R12 :: (R13 :: (R14 :: (R15 :: [])))))))))))))))

(** val reg_choiceMixin : Equality.sort Choice.Choice.mixin_of **)

let reg_choiceMixin =
  Choice.coq_PcanChoiceMixin Choice.nat_choiceType
    (Obj.magic FinIsCount.pickle reg_eqType registers)
    (Obj.magic FinIsCount.unpickle reg_eqType registers)

(** val reg_choiceType : Choice.Choice.coq_type **)

let reg_choiceType =
  { Choice.Choice.base = (Equality.coq_class reg_eqType);
    Choice.Choice.mixin = reg_choiceMixin }

(** val reg_countMixin : Equality.sort Choice.Countable.mixin_of **)

let reg_countMixin =
  Choice.coq_PcanCountMixin Choice.nat_countType
    (Obj.magic FinIsCount.pickle reg_eqType registers)
    (Obj.magic FinIsCount.unpickle reg_eqType registers)

(** val reg_countType : Choice.Countable.coq_type **)

let reg_countType =
  { Choice.Countable.base = (Choice.Choice.coq_class reg_choiceType);
    Choice.Countable.mixin = reg_countMixin }

(** val reg_finMixin : Finite.mixin_of **)

let reg_finMixin =
  Finite.coq_EnumMixin reg_countType (Obj.magic registers)

(** val reg_finType : Finite.coq_type **)

let reg_finType =
  { Finite.base = (Choice.Choice.coq_class reg_choiceType); Finite.mixin =
    reg_finMixin }

(** val regxs : register_ext list **)

let regxs =
  MM0 :: (MM1 :: (MM2 :: (MM3 :: (MM4 :: (MM5 :: (MM6 :: (MM7 :: [])))))))

(** val regx_choiceMixin : Equality.sort Choice.Choice.mixin_of **)

let regx_choiceMixin =
  Choice.coq_PcanChoiceMixin Choice.nat_choiceType
    (Obj.magic FinIsCount.pickle regx_eqType regxs)
    (Obj.magic FinIsCount.unpickle regx_eqType regxs)

(** val regx_choiceType : Choice.Choice.coq_type **)

let regx_choiceType =
  { Choice.Choice.base = (Equality.coq_class regx_eqType);
    Choice.Choice.mixin = regx_choiceMixin }

(** val regx_countMixin : Equality.sort Choice.Countable.mixin_of **)

let regx_countMixin =
  Choice.coq_PcanCountMixin Choice.nat_countType
    (Obj.magic FinIsCount.pickle regx_eqType regxs)
    (Obj.magic FinIsCount.unpickle regx_eqType regxs)

(** val regx_countType : Choice.Countable.coq_type **)

let regx_countType =
  { Choice.Countable.base = (Choice.Choice.coq_class regx_choiceType);
    Choice.Countable.mixin = regx_countMixin }

(** val regx_finMixin : Finite.mixin_of **)

let regx_finMixin =
  Finite.coq_EnumMixin regx_countType (Obj.magic regxs)

(** val regx_finType : Finite.coq_type **)

let regx_finType =
  { Finite.base = (Choice.Choice.coq_class regx_choiceType); Finite.mixin =
    regx_finMixin }

(** val xmm_registers : xmm_register list **)

let xmm_registers =
  XMM0 :: (XMM1 :: (XMM2 :: (XMM3 :: (XMM4 :: (XMM5 :: (XMM6 :: (XMM7 :: (XMM8 :: (XMM9 :: (XMM10 :: (XMM11 :: (XMM12 :: (XMM13 :: (XMM14 :: (XMM15 :: [])))))))))))))))

(** val xreg_choiceMixin : Equality.sort Choice.Choice.mixin_of **)

let xreg_choiceMixin =
  Choice.coq_PcanChoiceMixin Choice.nat_choiceType
    (Obj.magic FinIsCount.pickle xreg_eqType xmm_registers)
    (Obj.magic FinIsCount.unpickle xreg_eqType xmm_registers)

(** val xreg_choiceType : Choice.Choice.coq_type **)

let xreg_choiceType =
  { Choice.Choice.base = (Equality.coq_class xreg_eqType);
    Choice.Choice.mixin = xreg_choiceMixin }

(** val xreg_countMixin : Equality.sort Choice.Countable.mixin_of **)

let xreg_countMixin =
  Choice.coq_PcanCountMixin Choice.nat_countType
    (Obj.magic FinIsCount.pickle xreg_eqType xmm_registers)
    (Obj.magic FinIsCount.unpickle xreg_eqType xmm_registers)

(** val xreg_countType : Choice.Countable.coq_type **)

let xreg_countType =
  { Choice.Countable.base = (Choice.Choice.coq_class xreg_choiceType);
    Choice.Countable.mixin = xreg_countMixin }

(** val xreg_finMixin : Finite.mixin_of **)

let xreg_finMixin =
  Finite.coq_EnumMixin xreg_countType (Obj.magic xmm_registers)

(** val xreg_finType : Finite.coq_type **)

let xreg_finType =
  { Finite.base = (Choice.Choice.coq_class xreg_choiceType); Finite.mixin =
    xreg_finMixin }

(** val rflags : rflag list **)

let rflags =
  CF :: (PF :: (ZF :: (SF :: (OF :: []))))

(** val rflag_choiceMixin : Equality.sort Choice.Choice.mixin_of **)

let rflag_choiceMixin =
  Choice.coq_PcanChoiceMixin Choice.nat_choiceType
    (Obj.magic FinIsCount.pickle rflag_eqType rflags)
    (Obj.magic FinIsCount.unpickle rflag_eqType rflags)

(** val rflag_choiceType : Choice.Choice.coq_type **)

let rflag_choiceType =
  { Choice.Choice.base = (Equality.coq_class rflag_eqType);
    Choice.Choice.mixin = rflag_choiceMixin }

(** val rflag_countMixin : Equality.sort Choice.Countable.mixin_of **)

let rflag_countMixin =
  Choice.coq_PcanCountMixin Choice.nat_countType
    (Obj.magic FinIsCount.pickle rflag_eqType rflags)
    (Obj.magic FinIsCount.unpickle rflag_eqType rflags)

(** val rflag_countType : Choice.Countable.coq_type **)

let rflag_countType =
  { Choice.Countable.base = (Choice.Choice.coq_class rflag_choiceType);
    Choice.Countable.mixin = rflag_countMixin }

(** val rflag_finMixin : Finite.mixin_of **)

let rflag_finMixin =
  Finite.coq_EnumMixin rflag_countType (Obj.magic rflags)

(** val rflag_finType : Finite.coq_type **)

let rflag_finType =
  { Finite.base = (Choice.Choice.coq_class rflag_choiceType); Finite.mixin =
    rflag_finMixin }

(** val eqTC_register : register eqTypeC **)

let eqTC_register =
  { beq = register_beq; ceqP = reg_eq_axiom }

(** val finC_register : register finTypeC **)

let finC_register =
  { _eqC = eqTC_register; cenum = registers }

(** val register_to_string : register -> char list **)

let register_to_string = function
| RAX -> 'R'::('A'::('X'::[]))
| RCX -> 'R'::('C'::('X'::[]))
| RDX -> 'R'::('D'::('X'::[]))
| RBX -> 'R'::('B'::('X'::[]))
| RSP -> 'R'::('S'::('P'::[]))
| RBP -> 'R'::('B'::('P'::[]))
| RSI -> 'R'::('S'::('I'::[]))
| RDI -> 'R'::('D'::('I'::[]))
| R8 -> 'R'::('8'::[])
| R9 -> 'R'::('9'::[])
| R10 -> 'R'::('1'::('0'::[]))
| R11 -> 'R'::('1'::('1'::[]))
| R12 -> 'R'::('1'::('2'::[]))
| R13 -> 'R'::('1'::('3'::[]))
| R14 -> 'R'::('1'::('4'::[]))
| R15 -> 'R'::('1'::('5'::[]))

(** val x86_reg_toS : register coq_ToString **)

let x86_reg_toS =
  { category = ('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[]))))))));
    _finC = finC_register; to_string = register_to_string }

(** val eqTC_regx : register_ext eqTypeC **)

let eqTC_regx =
  { beq = register_ext_beq; ceqP = regx_eq_axiom }

(** val finC_regx : register_ext finTypeC **)

let finC_regx =
  { _eqC = eqTC_regx; cenum = regxs }

(** val regx_to_string : register_ext -> char list **)

let regx_to_string = function
| MM0 -> 'M'::('M'::('0'::[]))
| MM1 -> 'M'::('M'::('1'::[]))
| MM2 -> 'M'::('M'::('2'::[]))
| MM3 -> 'M'::('M'::('3'::[]))
| MM4 -> 'M'::('M'::('4'::[]))
| MM5 -> 'M'::('M'::('5'::[]))
| MM6 -> 'M'::('M'::('6'::[]))
| MM7 -> 'M'::('M'::('7'::[]))

(** val x86_regx_toS : register_ext coq_ToString **)

let x86_regx_toS =
  { category = ('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[]))))))));
    _finC = finC_regx; to_string = regx_to_string }

(** val eqTC_xmm_register : xmm_register eqTypeC **)

let eqTC_xmm_register =
  { beq = xmm_register_beq; ceqP = xreg_eq_axiom }

(** val finC_xmm_register : xmm_register finTypeC **)

let finC_xmm_register =
  { _eqC = eqTC_xmm_register; cenum = xmm_registers }

(** val xreg_to_string : xmm_register -> char list **)

let xreg_to_string = function
| XMM0 -> 'X'::('M'::('M'::('0'::[])))
| XMM1 -> 'X'::('M'::('M'::('1'::[])))
| XMM2 -> 'X'::('M'::('M'::('2'::[])))
| XMM3 -> 'X'::('M'::('M'::('3'::[])))
| XMM4 -> 'X'::('M'::('M'::('4'::[])))
| XMM5 -> 'X'::('M'::('M'::('5'::[])))
| XMM6 -> 'X'::('M'::('M'::('6'::[])))
| XMM7 -> 'X'::('M'::('M'::('7'::[])))
| XMM8 -> 'X'::('M'::('M'::('8'::[])))
| XMM9 -> 'X'::('M'::('M'::('9'::[])))
| XMM10 -> 'X'::('M'::('M'::('1'::('0'::[]))))
| XMM11 -> 'X'::('M'::('M'::('1'::('1'::[]))))
| XMM12 -> 'X'::('M'::('M'::('1'::('2'::[]))))
| XMM13 -> 'X'::('M'::('M'::('1'::('3'::[]))))
| XMM14 -> 'X'::('M'::('M'::('1'::('4'::[]))))
| XMM15 -> 'X'::('M'::('M'::('1'::('5'::[]))))

(** val x86_xreg_toS : xmm_register coq_ToString **)

let x86_xreg_toS =
  { category =
    ('y'::('m'::('m'::('_'::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[]))))))))))));
    _finC = finC_xmm_register; to_string = xreg_to_string }

(** val eqTC_rflag : rflag eqTypeC **)

let eqTC_rflag =
  { beq = rflag_beq; ceqP = rflag_eq_axiom }

(** val finC_rflag : rflag finTypeC **)

let finC_rflag =
  { _eqC = eqTC_rflag; cenum = rflags }

(** val rflag_to_string : rflag -> char list **)

let rflag_to_string = function
| CF -> 'C'::('F'::[])
| PF -> 'P'::('F'::[])
| ZF -> 'Z'::('F'::[])
| SF -> 'S'::('F'::[])
| OF -> 'O'::('F'::[])

(** val x86_rflag_toS : rflag coq_ToString **)

let x86_rflag_toS =
  { category = ('r'::('f'::('l'::('a'::('g'::[]))))); _finC = finC_rflag;
    to_string = rflag_to_string }

(** val eqC_condt : condt eqTypeC **)

let eqC_condt =
  { beq = condt_beq; ceqP = condt_eq_axiom }

(** val x86_fc_of_cfc : combine_flags_core -> flag_combination **)

let x86_fc_of_cfc cfc =
  let vof = FCVar0 in
  let vcf = FCVar1 in
  let vsf = FCVar2 in
  let vzf = FCVar3 in
  (match cfc with
   | CFC_B -> vcf
   | CFC_E -> vzf
   | CFC_L -> FCNot (FCEq (vof, vsf))
   | CFC_BE -> FCOr (vcf, vzf)
   | CFC_LE -> FCOr ((FCNot (FCEq (vof, vsf))), vzf))

(** val x86_fcp : coq_FlagCombinationParams **)

let x86_fcp =
  x86_fc_of_cfc

(** val x86_decl :
    (register, register_ext, xmm_register, rflag, condt) arch_decl **)

let x86_decl =
  { reg_size = x86_reg_size; xreg_size = x86_xreg_size; cond_eqC = eqC_condt;
    toS_r = x86_reg_toS; toS_rx = x86_regx_toS; toS_x = x86_xreg_toS; toS_f =
    x86_rflag_toS; ad_rsp = RSP; ad_fcp = x86_fcp }

(** val x86_linux_call_conv :
    (register, register_ext, xmm_register, rflag, condt) calling_convention **)

let x86_linux_call_conv =
  { callee_saved =
    (map (fun x -> ARReg x)
      (RBX :: (RBP :: (RSP :: (R12 :: (R13 :: (R14 :: (R15 :: []))))))));
    call_reg_args = (RDI :: (RSI :: (RDX :: (RCX :: (R8 :: (R9 :: []))))));
    call_xreg_args =
    (XMM0 :: (XMM1 :: (XMM2 :: (XMM3 :: (XMM4 :: (XMM5 :: (XMM6 :: (XMM7 :: []))))))));
    call_reg_ret = (RAX :: (RDX :: [])); call_xreg_ret =
    (XMM0 :: (XMM1 :: [])) }

(** val x86_windows_call_conv :
    (register, register_ext, xmm_register, rflag, condt) calling_convention **)

let x86_windows_call_conv =
  { callee_saved =
    (cat
      (map (fun x -> ARReg x)
        (RBX :: (RBP :: (RDI :: (RSI :: (RSP :: (R12 :: (R13 :: (R14 :: (R15 :: []))))))))))
      (map (fun x -> AXReg x)
        (XMM6 :: (XMM7 :: (XMM8 :: (XMM9 :: (XMM10 :: (XMM11 :: (XMM12 :: (XMM13 :: (XMM14 :: (XMM15 :: []))))))))))));
    call_reg_args = (RCX :: (RDX :: (R8 :: (R9 :: [])))); call_xreg_args =
    (XMM0 :: (XMM1 :: (XMM2 :: (XMM3 :: [])))); call_reg_ret = (RAX :: []);
    call_xreg_ret = (XMM0 :: []) }
