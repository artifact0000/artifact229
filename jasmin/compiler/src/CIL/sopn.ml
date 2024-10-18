open BinInt
open BinNums
open Bool
open Datatypes
open String0
open Eqtype
open Pseudo_operator
open Sem_type
open Seq
open Slh_ops
open Ssralg
open Ssrbool
open Ssrfun
open Ssrfun0
open Type
open Utils0
open Values
open Var0
open Warray_
open Word0
open Wsize

let __ = let rec f _ = Obj.repr f in Obj.repr f

type arg_desc =
| ADImplicit of Var.var
| ADExplicit of nat * Var.var option

type instruction_desc = { str : (unit -> char list); tin : stype list;
                          i_in : arg_desc list; tout : stype list;
                          i_out : arg_desc list;
                          semi : sem_tuple exec sem_prod;
                          i_safe : safe_cond list }

(** val str : instruction_desc -> unit -> char list **)

let str i =
  i.str

(** val tin : instruction_desc -> stype list **)

let tin i =
  i.tin

(** val i_in : instruction_desc -> arg_desc list **)

let i_in i =
  i.i_in

(** val tout : instruction_desc -> stype list **)

let tout i =
  i.tout

(** val i_out : instruction_desc -> arg_desc list **)

let i_out i =
  i.i_out

(** val semi : instruction_desc -> sem_tuple exec sem_prod **)

let semi i =
  i.semi

(** val i_safe : instruction_desc -> safe_cond list **)

let i_safe i =
  i.i_safe

type prim_x86_suffix =
| PVp of wsize
| PVv of velem * wsize
| PVsv of signedness * velem * wsize
| PVx of wsize * wsize
| PVvv of velem * wsize * velem * wsize

type 'asm_op prim_constructor =
| PrimX86 of prim_x86_suffix list * (prim_x86_suffix -> 'asm_op option)
| PrimARM of (bool -> bool -> 'asm_op)

type 'asm_op asmOp = { _eqT : 'asm_op eqTypeC;
                       asm_op_instr : ('asm_op -> instruction_desc);
                       prim_string : (char list * 'asm_op prim_constructor)
                                     list }

(** val _eqT : 'a1 asmOp -> 'a1 eqTypeC **)

let _eqT asmOp0 =
  asmOp0._eqT

(** val asm_op_instr : 'a1 asmOp -> 'a1 -> instruction_desc **)

let asm_op_instr asmOp0 =
  asmOp0.asm_op_instr

(** val prim_string : 'a1 asmOp -> (char list * 'a1 prim_constructor) list **)

let prim_string asmOp0 =
  asmOp0.prim_string

type 'asm_op asm_op_t = 'asm_op

type internal_reason =
| IRpc_load_scratch
| IRpc_load_msf
| IRpc_save_scratch

(** val internal_reason_beq : internal_reason -> internal_reason -> bool **)

let internal_reason_beq x y =
  match x with
  | IRpc_load_scratch -> (match y with
                          | IRpc_load_scratch -> true
                          | _ -> false)
  | IRpc_load_msf -> (match y with
                      | IRpc_load_msf -> true
                      | _ -> false)
  | IRpc_save_scratch -> (match y with
                          | IRpc_save_scratch -> true
                          | _ -> false)

(** val internal_reason_eq_dec :
    internal_reason -> internal_reason -> bool **)

let internal_reason_eq_dec x y =
  let b = internal_reason_beq x y in if b then true else false

(** val internal_reason_eq_axiom : internal_reason Equality.axiom **)

let internal_reason_eq_axiom =
  eq_axiom_of_scheme internal_reason_beq

(** val internal_reason_eqMixin : internal_reason Equality.mixin_of **)

let internal_reason_eqMixin =
  { Equality.op = internal_reason_beq; Equality.mixin_of__1 =
    internal_reason_eq_axiom }

(** val internal_reason_eqType : Equality.coq_type **)

let internal_reason_eqType =
  Obj.magic internal_reason_eqMixin

(** val string_of_internal_reason : internal_reason -> char list **)

let string_of_internal_reason = function
| IRpc_load_scratch ->
  'p'::('c'::('_'::('l'::('o'::('a'::('d'::('_'::('s'::('c'::('r'::('a'::('t'::('c'::('h'::[]))))))))))))))
| IRpc_load_msf ->
  'p'::('c'::('_'::('l'::('o'::('a'::('d'::('_'::('m'::('s'::('f'::[]))))))))))
| IRpc_save_scratch ->
  'p'::('c'::('_'::('s'::('a'::('v'::('e'::('_'::('s'::('c'::('r'::('a'::('t'::('c'::('h'::[]))))))))))))))

type internal_op =
| Ouse_vars of internal_reason * stype list * stype list

(** val internal_op_beq : internal_op -> internal_op -> bool **)

let internal_op_beq io0 io1 =
  let Ouse_vars (ir0, tin0, tout0) = io0 in
  let Ouse_vars (ir1, tin1, tout1) = io1 in
  (&&) (eq_op internal_reason_eqType (Obj.magic ir0) (Obj.magic ir1))
    ((&&) (eq_op (seq_eqType stype_eqType) (Obj.magic tin0) (Obj.magic tin1))
      (eq_op (seq_eqType stype_eqType) (Obj.magic tout0) (Obj.magic tout1)))

(** val internal_op_eq_axiom : internal_op Equality.axiom **)

let internal_op_eq_axiom __top_assumption_ =
  let _evar_0_ = fun _i_ _l_ _l1_ __top_assumption_0 ->
    let _evar_0_ = fun _i1_ _l2_ _l3_ ->
      iffP
        ((&&) (eq_op internal_reason_eqType _i_ _i1_)
          ((&&) (eq_op (seq_eqType stype_eqType) _l_ _l2_)
            (eq_op (seq_eqType stype_eqType) _l1_ _l3_)))
        (if (&&) (eq_op internal_reason_eqType _i_ _i1_)
              ((&&) (eq_op (seq_eqType stype_eqType) _l_ _l2_)
                (eq_op (seq_eqType stype_eqType) _l1_ _l3_))
         then ReflectT
         else ReflectF)
    in
    let Ouse_vars (i, l, l0) = __top_assumption_0 in Obj.magic _evar_0_ i l l0
  in
  let Ouse_vars (i, l, l0) = __top_assumption_ in Obj.magic _evar_0_ i l l0

(** val internal_op_eqMixin : internal_op Equality.mixin_of **)

let internal_op_eqMixin =
  { Equality.op = internal_op_beq; Equality.mixin_of__1 =
    internal_op_eq_axiom }

(** val internal_op_eqType : Equality.coq_type **)

let internal_op_eqType =
  Obj.magic internal_op_eqMixin

type 'asm_op sopn =
| Opseudo_op of pseudo_operator
| Oslh of slh_op
| Oasm of 'asm_op asm_op_t
| Ointernal of internal_op

(** val sopn_beq : 'a1 asmOp -> 'a1 sopn -> 'a1 sopn -> bool **)

let sopn_beq asmop o1 o2 =
  match o1 with
  | Opseudo_op o3 ->
    (match o2 with
     | Opseudo_op o4 ->
       eq_op pseudo_operator_eqType (Obj.magic o3) (Obj.magic o4)
     | _ -> false)
  | Oslh o3 ->
    (match o2 with
     | Oslh o4 -> eq_op slh_op_eqType (Obj.magic o3) (Obj.magic o4)
     | _ -> false)
  | Oasm o3 ->
    (match o2 with
     | Oasm o4 -> eq_op (ceqT_eqType asmop._eqT) (Obj.magic o3) (Obj.magic o4)
     | _ -> false)
  | Ointernal o3 ->
    (match o2 with
     | Ointernal o4 -> eq_op internal_op_eqType (Obj.magic o3) (Obj.magic o4)
     | _ -> false)

(** val sopn_eq_axiom : 'a1 asmOp -> 'a1 sopn Equality.axiom **)

let sopn_eq_axiom asmop __top_assumption_ =
  let _evar_0_ = fun _p_ __top_assumption_0 ->
    let _evar_0_ = fun _p1_ ->
      reflect_inj pseudo_operator_eqType (Obj.magic (fun x -> Opseudo_op x))
        _p_ _p1_ (eqP pseudo_operator_eqType _p_ _p1_)
    in
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = fun _ -> ReflectF in
    let _evar_0_2 = fun _ -> ReflectF in
    (match __top_assumption_0 with
     | Opseudo_op p -> Obj.magic _evar_0_ p
     | Oslh s -> _evar_0_0 s
     | Oasm a -> _evar_0_1 a
     | Ointernal i -> _evar_0_2 i)
  in
  let _evar_0_0 = fun _s_ __top_assumption_0 ->
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = fun _s1_ ->
      reflect_inj slh_op_eqType (Obj.magic (fun x -> Oslh x)) _s_ _s1_
        (eqP slh_op_eqType _s_ _s1_)
    in
    let _evar_0_2 = fun _ -> ReflectF in
    let _evar_0_3 = fun _ -> ReflectF in
    (match __top_assumption_0 with
     | Opseudo_op p -> _evar_0_0 p
     | Oslh s -> Obj.magic _evar_0_1 s
     | Oasm a -> _evar_0_2 a
     | Ointernal i -> _evar_0_3 i)
  in
  let _evar_0_1 = fun _a_ __top_assumption_0 ->
    let _evar_0_1 = fun _ -> ReflectF in
    let _evar_0_2 = fun _ -> ReflectF in
    let _evar_0_3 = fun _a1_ ->
      reflect_inj (ceqT_eqType asmop._eqT) (fun x -> Oasm x) _a_ _a1_
        (eqP (ceqT_eqType asmop._eqT) _a_ _a1_)
    in
    let _evar_0_4 = fun _ -> ReflectF in
    (match __top_assumption_0 with
     | Opseudo_op p -> _evar_0_1 p
     | Oslh s -> _evar_0_2 s
     | Oasm a -> _evar_0_3 a
     | Ointernal i -> _evar_0_4 i)
  in
  let _evar_0_2 = fun _i_ __top_assumption_0 ->
    let _evar_0_2 = fun _ -> ReflectF in
    let _evar_0_3 = fun _ -> ReflectF in
    let _evar_0_4 = fun _ -> ReflectF in
    let _evar_0_5 = fun _i1_ ->
      reflect_inj internal_op_eqType (Obj.magic (fun x -> Ointernal x)) _i_
        _i1_ (eqP internal_op_eqType _i_ _i1_)
    in
    (match __top_assumption_0 with
     | Opseudo_op p -> _evar_0_2 p
     | Oslh s -> _evar_0_3 s
     | Oasm a -> _evar_0_4 a
     | Ointernal i -> Obj.magic _evar_0_5 i)
  in
  (match __top_assumption_ with
   | Opseudo_op p -> Obj.magic _evar_0_ p
   | Oslh s -> Obj.magic _evar_0_0 s
   | Oasm a -> Obj.magic _evar_0_1 a
   | Ointernal i -> Obj.magic _evar_0_2 i)

(** val sopn_eqMixin : 'a1 asmOp -> 'a1 sopn Equality.mixin_of **)

let sopn_eqMixin asmop =
  { Equality.op = (sopn_beq asmop); Equality.mixin_of__1 =
    (sopn_eq_axiom asmop) }

(** val sopn_eqType : 'a1 asmOp -> Equality.coq_type **)

let sopn_eqType asmop =
  Obj.magic sopn_eqMixin asmop

(** val sopn_copy : 'a1 asmOp -> wsize -> positive -> 'a1 sopn **)

let sopn_copy _ ws p =
  Opseudo_op (Ocopy (ws, p))

(** val sopn_nop : 'a1 asmOp -> 'a1 sopn **)

let sopn_nop _ =
  Opseudo_op Onop

(** val sopn_mulu : 'a1 asmOp -> wsize -> 'a1 sopn **)

let sopn_mulu _ ws =
  Opseudo_op (Omulu ws)

(** val sopn_addcarry : 'a1 asmOp -> wsize -> 'a1 sopn **)

let sopn_addcarry _ ws =
  Opseudo_op (Oaddcarry ws)

(** val sopn_subcarry : 'a1 asmOp -> wsize -> 'a1 sopn **)

let sopn_subcarry _ ws =
  Opseudo_op (Osubcarry ws)

(** val coq_Ocopy_instr : wsize -> positive -> instruction_desc **)

let coq_Ocopy_instr ws p =
  let sz = Z.to_pos (arr_size ws p) in
  { str = (pp_sz ('c'::('o'::('p'::('y'::[])))) ws); tin = ((Coq_sarr
  sz) :: []); i_in = ((ADExplicit ((S O), None)) :: []); tout = ((Coq_sarr
  sz) :: []); i_out = ((ADExplicit (O, None)) :: []); semi =
  (Obj.magic WArray.copy ws p); i_safe = ((AllInit (ws, p, O)) :: []) }

(** val coq_Onop_instr : instruction_desc **)

let coq_Onop_instr =
  { str = (pp_s ('N'::('O'::('P'::[])))); tin = []; i_in = []; tout = [];
    i_out = []; semi = (Obj.magic (Ok ())); i_safe = [] }

(** val coq_Omulu_instr : wsize -> instruction_desc **)

let coq_Omulu_instr sz =
  { str = (pp_sz ('m'::('u'::('l'::('u'::[])))) sz); tin = ((Coq_sword
    sz) :: ((Coq_sword sz) :: [])); i_in = ((ADExplicit (O,
    None)) :: ((ADExplicit ((S O), None)) :: [])); tout = ((Coq_sword
    sz) :: ((Coq_sword sz) :: [])); i_out = ((ADExplicit ((S (S O)),
    None)) :: ((ADExplicit ((S (S (S O))), None)) :: [])); semi =
    (Obj.magic (fun x y -> Ok (wumul sz x y))); i_safe = [] }

(** val coq_Oaddcarry_instr : wsize -> instruction_desc **)

let coq_Oaddcarry_instr sz =
  { str = (pp_sz ('a'::('d'::('c'::[]))) sz); tin = ((Coq_sword
    sz) :: ((Coq_sword sz) :: (Coq_sbool :: []))); i_in = ((ADExplicit (O,
    None)) :: ((ADExplicit ((S O), None)) :: ((ADExplicit ((S (S O)),
    None)) :: []))); tout = (Coq_sbool :: ((Coq_sword sz) :: [])); i_out =
    ((ADExplicit ((S (S (S O))), None)) :: ((ADExplicit ((S (S (S (S O)))),
    None)) :: [])); semi =
    (Obj.magic (fun x y c ->
      let p = waddcarry sz x y c in Ok ((Some (fst p)), (snd p)))); i_safe =
    [] }

(** val coq_Osubcarry_instr : wsize -> instruction_desc **)

let coq_Osubcarry_instr sz =
  { str = (pp_sz ('s'::('b'::('b'::[]))) sz); tin = ((Coq_sword
    sz) :: ((Coq_sword sz) :: (Coq_sbool :: []))); i_in = ((ADExplicit (O,
    None)) :: ((ADExplicit ((S O), None)) :: ((ADExplicit ((S (S O)),
    None)) :: []))); tout = (Coq_sbool :: ((Coq_sword sz) :: [])); i_out =
    ((ADExplicit ((S (S (S O))), None)) :: ((ADExplicit ((S (S (S (S O)))),
    None)) :: [])); semi =
    (Obj.magic (fun x y c ->
      let p = wsubcarry sz x y c in Ok ((Some (fst p)), (snd p)))); i_safe =
    [] }

(** val spill_semi : stype list -> sem_tuple exec sem_prod **)

let rec spill_semi = function
| [] -> Obj.magic (Ok ())
| _ :: tys0 -> Obj.magic (fun _ -> spill_semi tys0)

(** val coq_Ospill_instr : spill_op -> stype list -> instruction_desc **)

let coq_Ospill_instr o tys =
  { str = (fun _ -> string_of_pseudo_operator (Ospill (o, tys))); tin = tys;
    i_in = (mapi (fun i _ -> ADExplicit (i, None)) tys); tout = []; i_out =
    []; semi = (spill_semi tys); i_safe = [] }

(** val coq_Oswap_instr : stype -> instruction_desc **)

let coq_Oswap_instr ty =
  { str = (fun _ -> 's'::('w'::('a'::('p'::[])))); tin = (ty :: (ty :: []));
    i_in = ((ADExplicit (O, None)) :: ((ADExplicit ((S O), None)) :: []));
    tout = (ty :: (ty :: [])); i_out = ((ADExplicit (O,
    None)) :: ((ADExplicit ((S O), None)) :: [])); semi =
    (Obj.magic swap_semi ty); i_safe = [] }

(** val pseudo_op_get_instr_desc : pseudo_operator -> instruction_desc **)

let pseudo_op_get_instr_desc = function
| Ospill (o0, tys) -> coq_Ospill_instr o0 tys
| Ocopy (ws, p) -> coq_Ocopy_instr ws p
| Onop -> coq_Onop_instr
| Omulu sz -> coq_Omulu_instr sz
| Oaddcarry sz -> coq_Oaddcarry_instr sz
| Osubcarry sz -> coq_Osubcarry_instr sz
| Oswap ty -> coq_Oswap_instr ty

(** val se_init_sem : coq_MSFsize -> GRing.ComRing.sort exec **)

let se_init_sem msfsz =
  Ok (GRing.zero (GRing.ComRing.zmodType (word (msf_size msfsz))))

(** val se_update_sem :
    coq_MSFsize -> bool -> GRing.ComRing.sort -> GRing.ComRing.sort exec **)

let se_update_sem msfsz b msf =
  Ok
    (if b
     then msf
     else GRing.opp
            (GRing.Ring.zmodType
              (GRing.ComRing.ringType (word (msf_size msfsz))))
            (GRing.one (GRing.ComRing.ringType (word (msf_size msfsz)))))

(** val se_move_sem :
    coq_MSFsize -> GRing.ComRing.sort -> GRing.ComRing.sort exec **)

let se_move_sem _ w =
  Ok w

(** val se_protect_sem :
    coq_MSFsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort exec **)

let se_protect_sem _ _ w _ =
  Ok w

(** val se_protect_ptr_sem :
    coq_MSFsize -> positive -> WArray.array -> GRing.ComRing.sort ->
    WArray.array exec **)

let se_protect_ptr_sem _ _ t _ =
  Ok t

(** val se_protect_ptr_fail_sem :
    coq_MSFsize -> positive -> WArray.array -> GRing.ComRing.sort ->
    WArray.array exec **)

let se_protect_ptr_fail_sem msfsz _ t msf =
  if eq_op (GRing.ComRing.eqType (word (msf_size msfsz))) msf
       (GRing.zero (GRing.ComRing.zmodType (word (msf_size msfsz))))
  then Ok t
  else let s = ErrType in Error s

(** val coq_SLHinit_str : char list **)

let coq_SLHinit_str =
  'i'::('n'::('i'::('t'::('_'::('m'::('s'::('f'::[])))))))

(** val coq_SLHinit_instr : coq_MSFsize -> instruction_desc **)

let coq_SLHinit_instr msfsz =
  { str = (pp_s coq_SLHinit_str); tin = []; i_in = []; tout = ((Coq_sword
    (msf_size msfsz)) :: []); i_out = ((ADExplicit (O, None)) :: []); semi =
    (Obj.magic se_init_sem msfsz); i_safe = [] }

(** val coq_SLHupdate_str : char list **)

let coq_SLHupdate_str =
  'u'::('p'::('d'::('a'::('t'::('e'::('_'::('m'::('s'::('f'::[])))))))))

(** val coq_SLHupdate_instr : coq_MSFsize -> instruction_desc **)

let coq_SLHupdate_instr msfsz =
  { str = (pp_s coq_SLHupdate_str); tin = (Coq_sbool :: ((Coq_sword
    (msf_size msfsz)) :: [])); i_in = ((ADExplicit (O, None)) :: ((ADExplicit
    ((S O), None)) :: [])); tout = ((Coq_sword (msf_size msfsz)) :: []);
    i_out = ((ADExplicit ((S (S O)), None)) :: []); semi =
    (Obj.magic se_update_sem msfsz); i_safe = [] }

(** val coq_SLHmove_str : char list **)

let coq_SLHmove_str =
  'm'::('o'::('v'::('_'::('m'::('s'::('f'::[]))))))

(** val coq_SLHmove_instr : coq_MSFsize -> instruction_desc **)

let coq_SLHmove_instr msfsz =
  { str = (pp_s coq_SLHmove_str); tin = ((Coq_sword (msf_size msfsz)) :: []);
    i_in = ((ADExplicit (O, None)) :: []); tout = ((Coq_sword
    (msf_size msfsz)) :: []); i_out = ((ADExplicit ((S O), None)) :: []);
    semi = (Obj.magic se_move_sem msfsz); i_safe = [] }

(** val coq_SLHprotect_str : char list **)

let coq_SLHprotect_str =
  'p'::('r'::('o'::('t'::('e'::('c'::('t'::[]))))))

(** val coq_SLHprotect_instr : coq_MSFsize -> wsize -> instruction_desc **)

let coq_SLHprotect_instr msfsz ws =
  { str = (pp_sz coq_SLHprotect_str ws); tin = ((Coq_sword ws) :: ((Coq_sword
    (msf_size msfsz)) :: [])); i_in = ((ADExplicit (O, None)) :: ((ADExplicit
    ((S O), None)) :: [])); tout = ((Coq_sword ws) :: []); i_out =
    ((ADExplicit ((S (S O)), None)) :: []); semi =
    (Obj.magic se_protect_sem msfsz ws); i_safe = [] }

(** val coq_SLHprotect_ptr_str : char list **)

let coq_SLHprotect_ptr_str =
  'p'::('r'::('o'::('t'::('e'::('c'::('t'::('_'::('p'::('t'::('r'::[]))))))))))

(** val coq_SLHprotect_ptr_instr :
    coq_MSFsize -> positive -> instruction_desc **)

let coq_SLHprotect_ptr_instr msfsz p =
  { str = (pp_s coq_SLHprotect_ptr_str); tin = ((Coq_sarr p) :: ((Coq_sword
    (msf_size msfsz)) :: [])); i_in = ((ADExplicit (O, None)) :: ((ADExplicit
    ((S O), None)) :: [])); tout = ((Coq_sarr p) :: []); i_out = ((ADExplicit
    ((S (S O)), None)) :: []); semi = (Obj.magic se_protect_ptr_sem msfsz p);
    i_safe = [] }

(** val coq_SLHprotect_ptr_fail_str : char list **)

let coq_SLHprotect_ptr_fail_str =
  'p'::('r'::('o'::('t'::('e'::('c'::('t'::('_'::('p'::('t'::('r'::('_'::('f'::('a'::('i'::('l'::[])))))))))))))))

(** val coq_SLHprotect_ptr_fail_instr :
    coq_MSFsize -> positive -> instruction_desc **)

let coq_SLHprotect_ptr_fail_instr msfsz p =
  { str = (pp_s coq_SLHprotect_ptr_fail_str); tin = ((Coq_sarr
    p) :: ((Coq_sword (msf_size msfsz)) :: [])); i_in = ((ADExplicit (O,
    None)) :: ((ADExplicit ((S O), None)) :: [])); tout = ((Coq_sarr
    p) :: []); i_out = ((ADExplicit ((S (S O)), None)) :: []); semi =
    (Obj.magic se_protect_ptr_fail_sem msfsz p); i_safe = [] }

(** val slh_op_instruction_desc :
    coq_MSFsize -> slh_op -> instruction_desc **)

let slh_op_instruction_desc msfsz = function
| SLHinit -> coq_SLHinit_instr msfsz
| SLHupdate -> coq_SLHupdate_instr msfsz
| SLHmove -> coq_SLHmove_instr msfsz
| SLHprotect ws -> coq_SLHprotect_instr msfsz ws
| SLHprotect_ptr p -> coq_SLHprotect_ptr_instr msfsz p
| SLHprotect_ptr_fail p -> coq_SLHprotect_ptr_fail_instr msfsz p

(** val mk_ltuple : (stype -> sem_ot) -> stype list -> sem_tuple **)

let rec mk_ltuple get = function
| [] -> Obj.magic ()
| t0 :: l ->
  (match l with
   | [] -> get t0
   | t1 :: tout1 ->
     let rest = mk_ltuple get tout1 in
     let rest0 =
       merge_tuple (__ :: []) (map (Obj.magic __) tout1) (get t1) rest
     in
     Obj.magic ((get t0), rest0))

(** val default_value : stype -> sem_ot **)

let default_value = function
| Coq_sbool -> Obj.magic None
| Coq_sint -> Obj.magic Z0
| Coq_sarr n -> Obj.magic WArray.empty n
| Coq_sword ws -> GRing.zero (GRing.ComRing.zmodType (word ws))

(** val use_vars_semi :
    stype list -> stype list -> sem_tuple exec sem_prod **)

let rec use_vars_semi tin0 tout0 =
  match tin0 with
  | [] -> Obj.magic (Ok (mk_ltuple default_value tout0))
  | _ :: tin1 -> Obj.magic (fun _ -> use_vars_semi tin1 tout0)

(** val use_vars_instr :
    internal_reason -> stype list -> stype list -> instruction_desc **)

let use_vars_instr ir tin0 tout0 =
  { str =
    (pp_s
      (append
        ('u'::('s'::('e'::('_'::('v'::('a'::('r'::('s'::('.'::[])))))))))
        (string_of_internal_reason ir))); tin = tin0; i_in =
    (map (fun n -> ADExplicit (n, None)) (iota O (size tin0))); tout = tout0;
    i_out =
    (map (fun n -> ADExplicit (n, None)) (iota (size tin0) (size tout0)));
    semi = (use_vars_semi tin0 tout0); i_safe = [] }

(** val internal_op_instr_desc : internal_op -> instruction_desc **)

let internal_op_instr_desc = function
| Ouse_vars (ir, tin0, tout0) -> use_vars_instr ir tin0 tout0

(** val get_instr_desc :
    coq_MSFsize -> 'a1 asmOp -> 'a1 sopn -> instruction_desc **)

let get_instr_desc msfsz asmop = function
| Opseudo_op o0 -> pseudo_op_get_instr_desc o0
| Oslh o0 -> slh_op_instruction_desc msfsz o0
| Oasm o0 -> asmop.asm_op_instr o0
| Ointernal o0 -> internal_op_instr_desc o0

(** val string_of_sopn : coq_MSFsize -> 'a1 asmOp -> 'a1 sopn -> char list **)

let string_of_sopn msfsz asmop o =
  (get_instr_desc msfsz asmop o).str ()

(** val sopn_tin : coq_MSFsize -> 'a1 asmOp -> 'a1 sopn -> stype list **)

let sopn_tin msfsz asmop o =
  (get_instr_desc msfsz asmop o).tin

(** val sopn_tout : coq_MSFsize -> 'a1 asmOp -> 'a1 sopn -> stype list **)

let sopn_tout msfsz asmop o =
  (get_instr_desc msfsz asmop o).tout

(** val sopn_sem :
    coq_MSFsize -> 'a1 asmOp -> 'a1 sopn -> sem_tuple exec sem_prod **)

let sopn_sem msfsz asmop o =
  (get_instr_desc msfsz asmop o).semi

(** val eqC_sopn : 'a1 asmOp -> 'a1 sopn eqTypeC **)

let eqC_sopn asmop =
  { beq = (sopn_beq asmop); ceqP = (sopn_eq_axiom asmop) }

(** val map_prim_constructor :
    ('a1 -> 'a2) -> 'a1 prim_constructor -> 'a2 prim_constructor **)

let map_prim_constructor f = function
| PrimX86 (a, k) -> PrimX86 (a, (fun x -> Ssrfun.Option.bind (olift f) (k x)))
| PrimARM x -> PrimARM (fun sf ic -> f (x sf ic))

(** val primM : 'a1 -> 'a1 prim_constructor **)

let primM f =
  PrimX86 ([], (fun _ -> Some f))

(** val primP : coq_PointerData -> (wsize -> 'a1) -> 'a1 prim_constructor **)

let primP pd f =
  PrimX86
    ((map (Obj.magic (fun x -> PVp x))
       ((Obj.magic coq_Uptr pd) :: (rem wsize_eqType (Obj.magic coq_Uptr pd)
                                     (Obj.magic wsizes)))), (fun s ->
    match s with
    | PVp sz -> Some (f sz)
    | _ -> None))

(** val sopn_prim_string :
    coq_PointerData -> 'a1 asmOp -> (char list * 'a1 sopn prim_constructor)
    list **)

let sopn_prim_string pd asmop =
  cat ((('c'::('o'::('p'::('y'::[])))),
    (primP pd (fun sz -> Opseudo_op (Ocopy (sz, Coq_xH))))) :: ((('s'::('w'::('a'::('p'::[])))),
    (primM (Opseudo_op (Oswap Coq_sbool)))) :: ((('m'::('u'::('l'::('u'::[])))),
    (primP pd (fun sz -> Opseudo_op (Omulu sz)))) :: ((('a'::('d'::('c'::[]))),
    (primP pd (fun sz -> Opseudo_op (Oaddcarry sz)))) :: ((('s'::('b'::('b'::[]))),
    (primP pd (fun sz -> Opseudo_op (Osubcarry sz)))) :: ((('i'::('n'::('i'::('t'::('_'::('m'::('s'::('f'::[])))))))),
    (primM (Oslh SLHinit))) :: ((('u'::('p'::('d'::('a'::('t'::('e'::('_'::('m'::('s'::('f'::[])))))))))),
    (primM (Oslh SLHupdate))) :: ((('m'::('o'::('v'::('_'::('m'::('s'::('f'::[]))))))),
    (primM (Oslh SLHmove))) :: ((('p'::('r'::('o'::('t'::('e'::('c'::('t'::[]))))))),
    (primP pd (fun sz -> Oslh (SLHprotect sz)))) :: ((('p'::('r'::('o'::('t'::('e'::('c'::('t'::('_'::('p'::('t'::('r'::[]))))))))))),
    (primM (Oslh (SLHprotect_ptr Coq_xH)))) :: []))))))))))
    (map (fun pat ->
      let (s, p) = pat in (s, (map_prim_constructor (fun x -> Oasm x) p)))
      asmop.prim_string)

(** val asmOp_sopn :
    coq_PointerData -> coq_MSFsize -> 'a1 asmOp -> 'a1 sopn asmOp **)

let asmOp_sopn pd msfsz asmop =
  { _eqT = (eqC_sopn asmop); asm_op_instr = (get_instr_desc msfsz asmop);
    prim_string = (sopn_prim_string pd asmop) }
