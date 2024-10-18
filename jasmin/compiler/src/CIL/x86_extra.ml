open BinNums
open Datatypes
open String0
open Arch_decl
open Arch_extra
open Compiler_util
open Eqtype
open Expr
open Fexpr
open Sem_type
open Seq
open Sopn
open Ssralg
open Type
open Utils0
open Var0
open Word0
open Wsize
open X86
open X86_decl
open X86_instr_decl

module E =
 struct
  (** val pass_name : char list **)

  let pass_name =
    'a'::('s'::('m'::('g'::('e'::('n'::[])))))

  (** val error : instr_info -> char list -> pp_error_loc **)

  let error ii msg =
    { pel_msg = (PPEstring msg); pel_fn = None; pel_fi = None; pel_ii = (Some
      ii); pel_vi = None; pel_pass = (Some pass_name); pel_internal = true }

  (** val se_update_arguments : instr_info -> pp_error_loc **)

  let se_update_arguments ii =
    pp_internal_error_s_at pass_name ii
      ('x'::('8'::('6'::('_'::('u'::('p'::('d'::('a'::('t'::('e'::('_'::('m'::('s'::('f'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(' '::('a'::('r'::('e'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::('.'::[])))))))))))))))))))))))))))))))))))))

  (** val se_protect_arguments : instr_info -> pp_error_loc **)

  let se_protect_arguments ii =
    pp_internal_error_s_at pass_name ii
      ('x'::('8'::('6'::('_'::('p'::('r'::('o'::('t'::('e'::('c'::('t'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(' '::('a'::('r'::('e'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::('.'::[]))))))))))))))))))))))))))))))))))

  (** val se_protect_ptr : instr_info -> pp_error_loc **)

  let se_protect_ptr ii =
    pp_internal_error_s_at pass_name ii
      ('F'::('o'::('u'::('n'::('d'::(' '::('p'::('r'::('o'::('t'::('e'::('c'::('t'::('_'::('p'::('t'::('r'::('.'::[]))))))))))))))))))

  (** val slh_update_after_call : instr_info -> pp_error_loc **)

  let slh_update_after_call ii =
    pp_internal_error_s_at pass_name ii
      ('f'::('o'::('u'::('n'::('d'::(' '::('u'::('p'::('d'::('a'::('t'::('e'::('_'::('a'::('f'::('t'::('e'::('r'::('_'::('c'::('a'::('l'::('l'::('.'::[]))))))))))))))))))))))))
 end

type x86_extra_op =
| Oset0 of wsize
| Oconcat128
| Ox86MOVZX32
| Ox86MULX of wsize
| Ox86MULX_hi of wsize
| Ox86SLHinit
| Ox86SLHupdate
| Ox86SLHmove
| Ox86SLHprotect of wsize
| Ox86SLHupdate_after_call

(** val x86_extra_op_beq : x86_extra_op -> x86_extra_op -> bool **)

let x86_extra_op_beq x y =
  match x with
  | Oset0 x0 -> (match y with
                 | Oset0 x1 -> wsize_beq x0 x1
                 | _ -> false)
  | Oconcat128 -> (match y with
                   | Oconcat128 -> true
                   | _ -> false)
  | Ox86MOVZX32 -> (match y with
                    | Ox86MOVZX32 -> true
                    | _ -> false)
  | Ox86MULX x0 -> (match y with
                    | Ox86MULX x1 -> wsize_beq x0 x1
                    | _ -> false)
  | Ox86MULX_hi x0 ->
    (match y with
     | Ox86MULX_hi x1 -> wsize_beq x0 x1
     | _ -> false)
  | Ox86SLHinit -> (match y with
                    | Ox86SLHinit -> true
                    | _ -> false)
  | Ox86SLHupdate -> (match y with
                      | Ox86SLHupdate -> true
                      | _ -> false)
  | Ox86SLHmove -> (match y with
                    | Ox86SLHmove -> true
                    | _ -> false)
  | Ox86SLHprotect x0 ->
    (match y with
     | Ox86SLHprotect x1 -> wsize_beq x0 x1
     | _ -> false)
  | Ox86SLHupdate_after_call ->
    (match y with
     | Ox86SLHupdate_after_call -> true
     | _ -> false)

(** val x86_extra_op_eq_dec : x86_extra_op -> x86_extra_op -> bool **)

let x86_extra_op_eq_dec x y =
  let b = x86_extra_op_beq x y in if b then true else false

(** val x86_extra_op_eq_axiom : x86_extra_op Equality.axiom **)

let x86_extra_op_eq_axiom =
  eq_axiom_of_scheme x86_extra_op_beq

(** val x86_extra_op_eqMixin : x86_extra_op Equality.mixin_of **)

let x86_extra_op_eqMixin =
  { Equality.op = x86_extra_op_beq; Equality.mixin_of__1 =
    x86_extra_op_eq_axiom }

(** val x86_extra_op_eqType : Equality.coq_type **)

let x86_extra_op_eqType =
  Obj.magic x86_extra_op_eqMixin

(** val coq_Oset0_instr :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    wsize -> instruction_desc **)

let coq_Oset0_instr atoI sz =
  if cmp_le wsize_cmp sz U64
  then { str = (pp_sz ('s'::('e'::('t'::('0'::[])))) sz); tin = []; i_in =
         []; tout = (b5w_ty sz); i_out =
         (cat (map (sopn_arg_desc x86_decl atoI) implicit_flags) ((ADExplicit
           (O, None)) :: [])); semi =
         (let vf = Some false in
          let vt = Some true in
          Obj.magic (Ok (vf, (vf, (vf, (vt, (vt,
            (GRing.zero (GRing.ComRing.zmodType (word sz)))))))))); i_safe =
         [] }
  else { str = (pp_sz ('s'::('e'::('t'::('0'::[])))) sz); tin = []; i_in =
         []; tout = (w_ty sz); i_out = ((ADExplicit (O, None)) :: []); semi =
         (Obj.magic (Ok (GRing.zero (GRing.ComRing.zmodType (word sz)))));
         i_safe = [] }

(** val coq_Oconcat128_instr : instruction_desc **)

let coq_Oconcat128_instr =
  { str =
    (pp_s
      ('c'::('o'::('n'::('c'::('a'::('t'::('_'::('2'::('u'::('1'::('2'::('8'::[])))))))))))));
    tin = ((Coq_sword U128) :: ((Coq_sword U128) :: [])); i_in = ((ADExplicit
    ((S O), None)) :: ((ADExplicit ((S (S O)), None)) :: [])); tout =
    ((Coq_sword U256) :: []); i_out = ((ADExplicit (O, None)) :: []); semi =
    (Obj.magic (fun h l -> Ok (make_vec U128 U256 (l :: (h :: [])))));
    i_safe = [] }

(** val coq_Ox86MOVZX32_instr : instruction_desc **)

let coq_Ox86MOVZX32_instr =
  { str = (pp_s ('M'::('O'::('V'::('Z'::('X'::('3'::('2'::[])))))))); tin =
    ((Coq_sword U32) :: []); i_in = ((ADExplicit ((S O), None)) :: []);
    tout = ((Coq_sword U64) :: []); i_out = ((ADExplicit (O, None)) :: []);
    semi = (Obj.magic (fun x -> Ok (zero_extend U64 U32 x))); i_safe = [] }

(** val x86_MULX :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_MULX sz v1 v2 =
  match check_size_32_64 sz with
  | Ok _ -> Ok (Obj.magic wumul sz v1 v2)
  | Error s -> Error s

(** val coq_Ox86MULX_instr :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    wsize -> instruction_desc **)

let coq_Ox86MULX_instr atoI sz =
  let name = 'M'::('U'::('L'::('X'::[]))) in
  { str = (pp_sz name sz); tin = (w2_ty sz sz); i_in = ((ADImplicit
  (to_var (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RDX)) :: ((ADExplicit
  ((S (S O)), None)) :: [])); tout = (w2_ty sz sz); i_out = ((ADExplicit (O,
  None)) :: ((ADExplicit ((S O), None)) :: [])); semi =
  (Obj.magic x86_MULX sz); i_safe = [] }

(** val x86_MULX_hi :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_MULX_hi sz v1 v2 =
  match check_size_32_64 sz with
  | Ok _ -> Ok (wmulhu sz v1 v2)
  | Error s -> Error s

(** val coq_Ox86MULX_hi_instr :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    wsize -> instruction_desc **)

let coq_Ox86MULX_hi_instr atoI sz =
  let name = 'M'::('U'::('L'::('X'::('_'::('h'::('i'::[])))))) in
  { str = (pp_sz name sz); tin = (w2_ty sz sz); i_in = ((ADImplicit
  (to_var (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RDX)) :: ((ADExplicit
  ((S O), None)) :: [])); tout = (w_ty sz); i_out = ((ADExplicit (O,
  None)) :: []); semi = (Obj.magic x86_MULX_hi sz); i_safe = [] }

(** val coq_Ox86SLHinit_str : char list **)

let coq_Ox86SLHinit_str =
  append ('O'::('x'::('8'::('6'::('_'::[]))))) coq_SLHinit_str

(** val coq_Ox86SLHinit_instr : instruction_desc **)

let coq_Ox86SLHinit_instr =
  { str = (pp_s coq_Ox86SLHinit_str); tin = []; i_in = []; tout = ((Coq_sword
    (msf_size (arch_msfsz x86_decl))) :: []); i_out = ((ADExplicit (O,
    None)) :: []); semi = (Obj.magic se_init_sem (arch_msfsz x86_decl));
    i_safe = [] }

(** val x86_se_update_sem :
    bool -> GRing.ComRing.sort -> (GRing.ComRing.sort * GRing.ComRing.sort)
    exec **)

let x86_se_update_sem b w =
  let aux = wrepr (coq_Uptr (arch_pd x86_decl)) (Zneg Coq_xH) in
  let w0 = if negb b then aux else w in Ok (aux, w0)

(** val coq_Ox86SLHupdate_str : char list **)

let coq_Ox86SLHupdate_str =
  append ('O'::('x'::('8'::('6'::('_'::[]))))) coq_SLHupdate_str

(** val coq_Ox86SLHupdate_instr : instruction_desc **)

let coq_Ox86SLHupdate_instr =
  { str = (pp_s coq_Ox86SLHupdate_str); tin = (Coq_sbool :: ((Coq_sword
    (msf_size (arch_msfsz x86_decl))) :: [])); i_in = ((ADExplicit (O,
    None)) :: ((ADExplicit ((S O), None)) :: [])); tout = ((Coq_sword
    (msf_size (arch_msfsz x86_decl))) :: ((Coq_sword
    (msf_size (arch_msfsz x86_decl))) :: [])); i_out = ((ADExplicit ((S (S
    O)), None)) :: ((ADExplicit ((S O), None)) :: [])); semi =
    (Obj.magic x86_se_update_sem); i_safe = [] }

(** val coq_Ox86SLHmove_str : char list **)

let coq_Ox86SLHmove_str =
  append ('O'::('x'::('8'::('6'::('_'::[]))))) coq_SLHmove_str

(** val coq_Ox86SLHmove_instr : instruction_desc **)

let coq_Ox86SLHmove_instr =
  { str = (pp_s coq_Ox86SLHmove_str); tin = ((Coq_sword
    (msf_size (arch_msfsz x86_decl))) :: []); i_in = ((ADExplicit ((S O),
    None)) :: []); tout = ((Coq_sword
    (msf_size (arch_msfsz x86_decl))) :: []); i_out = ((ADExplicit (O,
    None)) :: []); semi = (Obj.magic se_move_sem (arch_msfsz x86_decl));
    i_safe = [] }

(** val se_protect_small_sem :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let se_protect_small_sem =
  x86_OR

(** val se_protect_large_sem :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    (GRing.ComRing.sort * GRing.ComRing.sort) exec **)

let se_protect_large_sem ws w msf =
  if cmp_lt wsize_cmp (coq_Uptr (arch_pd x86_decl)) ws
  then let aux = wpbroadcast (msf_size (arch_msfsz x86_decl)) ws msf in
       Ok (aux, (wor ws w aux))
  else let s = ErrType in Error s

(** val coq_Ox86SLHprotect_str : char list **)

let coq_Ox86SLHprotect_str =
  append ('O'::('x'::('8'::('6'::('_'::[]))))) coq_SLHprotect_str

(** val coq_Ox86SLHprotect_instr :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    wsize -> instruction_desc **)

let coq_Ox86SLHprotect_instr atoI =
  let out =
    cat (map (sopn_arg_desc x86_decl atoI) implicit_flags) ((ADExplicit (O,
      None)) :: [])
  in
  (fun ws ->
  if cmp_le wsize_cmp ws (coq_Uptr (arch_pd x86_decl))
  then { str = (pp_sz coq_SLHprotect_str ws); tin = ((Coq_sword
         ws) :: ((Coq_sword ws) :: [])); i_in = ((ADExplicit (O,
         None)) :: ((ADExplicit ((S O), None)) :: [])); tout =
         (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: ((Coq_sword
         ws) :: [])))))); i_out = out; semi =
         (Obj.magic se_protect_small_sem ws); i_safe = [] }
  else { str = (pp_sz coq_SLHprotect_str ws); tin = ((Coq_sword
         ws) :: ((Coq_sword (msf_size (arch_msfsz x86_decl))) :: [])); i_in =
         ((ADExplicit (O, None)) :: ((ADExplicit ((S O), None)) :: []));
         tout = ((Coq_sword ws) :: ((Coq_sword ws) :: [])); i_out =
         ((ADExplicit ((S (S O)), None)) :: ((ADExplicit (O, None)) :: []));
         semi = (Obj.magic se_protect_large_sem ws); i_safe = [] })

(** val coq_Ox86SLHupdate_after_call_str : char list **)

let coq_Ox86SLHupdate_after_call_str =
  'O'::('x'::('8'::('6'::('_'::('u'::('p'::('d'::('a'::('t'::('e'::('_'::('a'::('f'::('t'::('e'::('r'::('_'::('c'::('a'::('l'::('l'::[])))))))))))))))))))))

(** val coq_Ox86SLHupdate_after_call_instr : instruction_desc **)

let coq_Ox86SLHupdate_after_call_instr =
  { str = (pp_s coq_Ox86SLHupdate_after_call_str); tin = ((Coq_sword
    (msf_size (arch_msfsz x86_decl))) :: []); i_in = ((ADExplicit (O,
    None)) :: []); tout = ((Coq_sword
    (msf_size (arch_msfsz x86_decl))) :: ((Coq_sword
    (msf_size (arch_msfsz x86_decl))) :: [])); i_out = ((ADExplicit ((S O),
    None)) :: ((ADExplicit (O, None)) :: [])); semi =
    (Obj.magic x86_se_update_sem true); i_safe = [] }

(** val get_instr_desc :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    x86_extra_op -> instruction_desc **)

let get_instr_desc atoI = function
| Oset0 ws -> coq_Oset0_instr atoI ws
| Oconcat128 -> coq_Oconcat128_instr
| Ox86MOVZX32 -> coq_Ox86MOVZX32_instr
| Ox86MULX ws -> coq_Ox86MULX_instr atoI ws
| Ox86MULX_hi ws -> coq_Ox86MULX_hi_instr atoI ws
| Ox86SLHinit -> coq_Ox86SLHinit_instr
| Ox86SLHupdate -> coq_Ox86SLHupdate_instr
| Ox86SLHmove -> coq_Ox86SLHmove_instr
| Ox86SLHprotect ws -> coq_Ox86SLHprotect_instr atoI ws
| Ox86SLHupdate_after_call -> coq_Ox86SLHupdate_after_call_instr

(** val prim_string : (char list * x86_extra_op prim_constructor) list **)

let prim_string =
  (('s'::('e'::('t'::('0'::[])))),
    (primP (arch_pd x86_decl) (fun x -> Oset0 x))) :: ((('c'::('o'::('n'::('c'::('a'::('t'::('_'::('2'::('u'::('1'::('2'::('8'::[])))))))))))),
    (primM Oconcat128)) :: ((('M'::('U'::('L'::('X'::[])))),
    (prim_32_64 (fun x -> Ox86MULX x))) :: ((('M'::('U'::('L'::('X'::('_'::('h'::('i'::[]))))))),
    (prim_32_64 (fun x -> Ox86MULX_hi x))) :: [])))

(** val re_i : wsize -> coq_Z -> rexpr **)

let re_i ws i =
  Rexpr (fconst ws i)

(** val re8_0 : rexpr **)

let re8_0 =
  re_i U8 Z0

(** val re8_1 : rexpr **)

let re8_1 =
  re_i U8 (Zpos Coq_xH)

(** val assemble_slh_init :
    lexpr list -> (((register, register_ext, xmm_register, rflag, condt,
    x86_op) asm_op_msb_t * lexpr list) * rexpr list) list cexec **)

let assemble_slh_init les =
  Ok ((((None, LFENCE), []), []) :: ((((None, (MOV U64)), les),
    ((re_i U64 Z0) :: [])) :: []))

(** val assemble_slh_update :
    instr_info -> lexpr list -> rexpr list -> (((register, register_ext,
    xmm_register, rflag, condt, x86_op) asm_op_msb_t * lexpr list) * rexpr
    list) list cexec **)

let assemble_slh_update ii les res =
  match les with
  | [] -> Error (E.se_update_arguments ii)
  | l1 :: l2 ->
    (match l1 with
     | Store (_, _, _) -> Error (E.se_update_arguments ii)
     | LLvar aux ->
       (match l2 with
        | [] -> Error (E.se_update_arguments ii)
        | ms0 :: l3 ->
          (match l3 with
           | [] ->
             (match res with
              | [] -> Error (E.se_update_arguments ii)
              | r :: l4 ->
                (match r with
                 | Load (_, _, _) -> Error (E.se_update_arguments ii)
                 | Rexpr b ->
                   (match l4 with
                    | [] -> Error (E.se_update_arguments ii)
                    | msf :: l5 ->
                      (match l5 with
                       | [] ->
                         if (&&)
                              (negb
                                ((||)
                                  (SvExtra.Sv.mem (Obj.magic aux.v_var)
                                    (free_vars b))
                                  (SvExtra.Sv.mem (Obj.magic aux.v_var)
                                    (free_vars_r msf))))
                              (eq_op stype_eqType
                                (Obj.magic Var.vtype aux.v_var)
                                (Obj.magic (Coq_sword U64)))
                         then let res' = (Rexpr (Fapp1 (Onot, b))) :: ((Rexpr
                                (Fvar aux)) :: (msf :: []))
                              in
                              Ok ((((None, (MOV U64)), ((LLvar aux) :: [])),
                              ((re_i U64 (Zneg Coq_xH)) :: [])) :: ((((None,
                              (CMOVcc U64)), (ms0 :: [])), res') :: []))
                         else let s = E.se_update_arguments ii in Error s
                       | _ :: _ -> Error (E.se_update_arguments ii)))))
           | _ :: _ -> Error (E.se_update_arguments ii))))

(** val assemble_slh_protect :
    instr_info -> wsize -> lexpr list -> rexpr list -> (((register,
    register_ext, xmm_register, rflag, condt, x86_op) asm_op_msb_t * lexpr
    list) * rexpr list) list cexec **)

let assemble_slh_protect ii ws les res =
  if cmp_le wsize_cmp ws U64
  then Ok ((((None, (OR ws)), les), res) :: [])
  else (match les with
        | [] -> Error (E.se_protect_arguments ii)
        | l1 :: l2 ->
          (match l1 with
           | Store (_, _, _) -> Error (E.se_protect_arguments ii)
           | LLvar aux ->
             (match l2 with
              | [] -> Error (E.se_protect_arguments ii)
              | y :: l3 ->
                (match l3 with
                 | [] ->
                   (match res with
                    | [] -> Error (E.se_protect_arguments ii)
                    | x :: l4 ->
                      (match l4 with
                       | [] -> Error (E.se_protect_arguments ii)
                       | msf :: l5 ->
                         (match l5 with
                          | [] ->
                            if negb
                                 ((||)
                                   (SvExtra.Sv.mem (Obj.magic aux.v_var)
                                     (free_vars_r x))
                                   (SvExtra.Sv.mem (Obj.magic aux.v_var)
                                     (free_vars_r msf)))
                            then let eaux = Rexpr (Fvar aux) in
                                 let laux = (LLvar aux) :: [] in
                                 Ok
                                 (cat ((((None, (VPINSR VE64)), laux),
                                   (eaux :: (msf :: (re8_0 :: [])))) :: ((((None,
                                   (VPINSR VE64)), laux),
                                   (eaux :: (msf :: (re8_1 :: [])))) :: []))
                                   (cat
                                     (if eq_op wsize_eqType (Obj.magic ws)
                                           (Obj.magic U256)
                                      then (((None, VINSERTI128), laux),
                                             (eaux :: (eaux :: (re8_1 :: [])))) :: []
                                      else []) ((((None, (VPOR ws)),
                                     (y :: [])), (x :: (eaux :: []))) :: [])))
                            else let s = E.se_update_arguments ii in Error s
                          | _ :: _ -> Error (E.se_protect_arguments ii))))
                 | _ :: _ -> Error (E.se_protect_arguments ii)))))

(** val assemble_slh_move :
    lexpr list -> rexpr list -> (((register, register_ext, xmm_register,
    rflag, condt, x86_op) asm_op_msb_t * lexpr list) * rexpr list) list cexec **)

let assemble_slh_move les res =
  let lmmx =
    match les with
    | [] -> false
    | l :: l0 ->
      (match l with
       | Store (_, _, _) -> false
       | LLvar x -> (match l0 with
                     | [] -> is_regx x.v_var
                     | _ :: _ -> false))
  in
  let rmmx =
    match res with
    | [] -> false
    | r :: l ->
      (match r with
       | Load (_, _, _) -> false
       | Rexpr f ->
         (match f with
          | Fvar x -> (match l with
                       | [] -> is_regx x.v_var
                       | _ :: _ -> false)
          | _ -> false))
  in
  let op0 = fun x -> if (||) lmmx rmmx then MOVX x else MOV x in
  Ok ((((None, (op0 (coq_Uptr (arch_pd x86_decl)))), les), res) :: [])

(** val assemble_extra :
    instr_info -> x86_extra_op -> lexpr list -> rexpr list -> (((register,
    register_ext, xmm_register, rflag, condt, x86_op) asm_op_msb_t * lexpr
    list) * rexpr list) list cexec **)

let assemble_extra ii o outx inx =
  match o with
  | Oset0 sz ->
    let op0 = if cmp_le wsize_cmp sz U64 then XOR sz else VPXOR sz in
    (match rev outx with
     | [] ->
       let s =
         E.error ii
           ('s'::('e'::('t'::('0'::(' '::(':'::(' '::('d'::('e'::('s'::('t'::('i'::('n'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))
       in
       Error s
     | y :: _ ->
       (match y with
        | Store (_, _, _) ->
          let s =
            E.error ii
              ('s'::('e'::('t'::('0'::(' '::(':'::(' '::('d'::('e'::('s'::('t'::('i'::('n'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))
          in
          Error s
        | LLvar x ->
          let x0 = Rexpr (Fvar x) in
          Ok ((((None, op0), outx), (x0 :: (x0 :: []))) :: [])))
  | Oconcat128 ->
    (match inx with
     | [] ->
       let s =
         E.error ii
           ('O'::('c'::('o'::('n'::('c'::('a'::('t'::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::[])))))))))))))))))))))
       in
       Error s
     | h :: l0 ->
       (match l0 with
        | [] ->
          let s =
            E.error ii
              ('O'::('c'::('o'::('n'::('c'::('a'::('t'::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::[])))))))))))))))))))))
          in
          Error s
        | l :: l1 ->
          (match l with
           | Load (_, _, _) ->
             let s =
               E.error ii
                 ('O'::('c'::('o'::('n'::('c'::('a'::('t'::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::[])))))))))))))))))))))
             in
             Error s
           | Rexpr f ->
             (match f with
              | Fconst _ ->
                let s =
                  E.error ii
                    ('O'::('c'::('o'::('n'::('c'::('a'::('t'::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::[])))))))))))))))))))))
                in
                Error s
              | Fvar _ ->
                (match l1 with
                 | [] ->
                   let x = l :: (h :: (re8_1 :: [])) in
                   Ok ((((None, VINSERTI128), outx), x) :: [])
                 | _ :: _ ->
                   let s =
                     E.error ii
                       ('O'::('c'::('o'::('n'::('c'::('a'::('t'::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::[])))))))))))))))))))))
                   in
                   Error s)
              | _ ->
                let s =
                  E.error ii
                    ('O'::('c'::('o'::('n'::('c'::('a'::('t'::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::[])))))))))))))))))))))
                in
                Error s))))
  | Ox86MOVZX32 ->
    (match outx with
     | [] ->
       let s =
         E.error ii
           ('O'::('x'::('8'::('6'::('M'::('O'::('V'::('Z'::('X'::('3'::('2'::(':'::(' '::('d'::('e'::('s'::('t'::('i'::('n'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))))))))
       in
       Error s
     | l :: l0 ->
       (match l with
        | Store (_, _, _) ->
          let s =
            E.error ii
              ('O'::('x'::('8'::('6'::('M'::('O'::('V'::('Z'::('X'::('3'::('2'::(':'::(' '::('d'::('e'::('s'::('t'::('i'::('n'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))))))))
          in
          Error s
        | LLvar _ ->
          (match l0 with
           | [] -> Ok ((((None, (MOV U32)), outx), inx) :: [])
           | _ :: _ ->
             let s =
               E.error ii
                 ('O'::('x'::('8'::('6'::('M'::('O'::('V'::('Z'::('X'::('3'::('2'::(':'::(' '::('d'::('e'::('s'::('t'::('i'::('n'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))))))))
             in
             Error s)))
  | Ox86MULX sz ->
    (match match outx with
           | [] ->
             Error
               (E.error ii
                 ('O'::('x'::('8'::('6'::('M'::('U'::('L'::('X'::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::[])))))))))))))))))))))))
           | h :: l0 ->
             (match h with
              | Store (_, _, _) ->
                Error
                  (E.error ii
                    ('O'::('x'::('8'::('6'::('M'::('U'::('L'::('X'::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::[])))))))))))))))))))))))
              | LLvar hi ->
                (match l0 with
                 | [] ->
                   Error
                     (E.error ii
                       ('O'::('x'::('8'::('6'::('M'::('U'::('L'::('X'::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::[])))))))))))))))))))))))
                 | l :: l1 ->
                   (match l with
                    | Store (_, _, _) ->
                      Error
                        (E.error ii
                          ('O'::('x'::('8'::('6'::('M'::('U'::('L'::('X'::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::[])))))))))))))))))))))))
                    | LLvar lo ->
                      (match l1 with
                       | [] ->
                         if negb
                              (eq_op Var.var_eqType (Obj.magic lo.v_var)
                                (Obj.magic hi.v_var))
                         then Ok (l :: (h :: []))
                         else let s =
                                E.error ii
                                  ('O'::('x'::('8'::('6'::('M'::('U'::('L'::('X'::(':'::(' '::('l'::('o'::(' '::('='::(' '::('h'::('i'::[])))))))))))))))))
                              in
                              Error s
                       | _ :: _ ->
                         Error
                           (E.error ii
                             ('O'::('x'::('8'::('6'::('M'::('U'::('L'::('X'::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::[]))))))))))))))))))))))))))) with
     | Ok x -> Ok ((((None, (MULX_lo_hi sz)), x), inx) :: [])
     | Error s -> Error s)
  | Ox86MULX_hi sz ->
    (match outx with
     | [] ->
       let s =
         E.error ii
           ('O'::('x'::('8'::('6'::('M'::('U'::('L'::('X'::('_'::('h'::('i'::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::[])))))))))))))))))))))))))
       in
       Error s
     | l :: l0 ->
       (match l with
        | Store (_, _, _) ->
          let s =
            E.error ii
              ('O'::('x'::('8'::('6'::('M'::('U'::('L'::('X'::('_'::('h'::('i'::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::[])))))))))))))))))))))))))
          in
          Error s
        | LLvar hi ->
          (match l0 with
           | [] ->
             let x = (LLvar hi) :: ((LLvar hi) :: []) in
             Ok ((((None, (MULX_lo_hi sz)), x), inx) :: [])
           | _ :: _ ->
             let s =
               E.error ii
                 ('O'::('x'::('8'::('6'::('M'::('U'::('L'::('X'::('_'::('h'::('i'::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::[])))))))))))))))))))))))))
             in
             Error s)))
  | Ox86SLHinit -> assemble_slh_init outx
  | Ox86SLHupdate -> assemble_slh_update ii outx inx
  | Ox86SLHmove -> assemble_slh_move outx inx
  | Ox86SLHprotect ws -> assemble_slh_protect ii ws outx inx
  | Ox86SLHupdate_after_call -> Error (E.slh_update_after_call ii)

(** val eqC_x86_extra_op : x86_extra_op eqTypeC **)

let eqC_x86_extra_op =
  { beq = x86_extra_op_beq; ceqP = x86_extra_op_eq_axiom }

(** val x86_extra_op_decl :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    x86_extra_op asmOp **)

let x86_extra_op_decl atoI =
  { _eqT = eqC_x86_extra_op; asm_op_instr = (get_instr_desc atoI);
    Sopn.prim_string = prim_string }

(** val x86_extra :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) asm_extra **)

let x86_extra atoI =
  { _asm = x86; _atoI = atoI; _extra = (x86_extra_op_decl atoI); to_asm =
    assemble_extra }

type x86_extended_op =
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  extended_op

(** val coq_Ox86 :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    x86_op -> x86_extended_op sopn **)

let coq_Ox86 _ o =
  Oasm (BaseOp (None, o))
