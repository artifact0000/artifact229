open BinNums
open Datatypes
open Arch_decl
open Arch_extra
open Arch_params
open Arm_decl
open Arm_extra
open Arm_instr_decl
open Arm_lowering
open Arm_params_common
open Arm_params_core
open Arm_stack_zeroization
open Asm_gen
open Compiler_util
open Eqtype
open Expr
open Fexpr
open Linearization
open Lowering
open Protect_calls
open Seq
open Slh_lowering
open Sopn
open Ssrbool
open Stack_alloc
open Stack_zeroization
open Type
open Utils0
open Var0
open Word_ssrZ
open Wsize

type __ = Obj.t

(** val is_load : pexpr -> bool **)

let is_load = function
| Pload (_, _, _) -> true
| _ -> false

(** val arm_mov_ofs :
    (register, __, __, rflag, condt) arch_toIdent -> lval -> assgn_tag ->
    vptr_kind -> pexpr -> coq_Z -> (register, __, __, rflag, condt, arm_op,
    arm_extra_op) extended_op instr_r option **)

let arm_mov_ofs atoI x tag vpk y ofs =
  let mk = fun oa ->
    let (op, args) = oa in
    Some (Copn ((x :: []), tag, (coq_Oarm atoI (ARM_op (op, default_opts))),
    args))
  in
  (match mk_mov vpk with
   | MK_LEA ->
     mk (ADR,
       ((if eq_op coq_Z_eqType (Obj.magic ofs) (Obj.magic Z0)
         then y
         else add (arch_pd arm_decl) y (eword_of_int arm_decl.reg_size ofs)) :: []))
   | MK_MOV ->
     (match x with
      | Lvar x_ ->
        if is_load y
        then if eq_op coq_Z_eqType (Obj.magic ofs) (Obj.magic Z0)
             then mk (LDR, (y :: []))
             else None
        else if eq_op coq_Z_eqType (Obj.magic ofs) (Obj.magic Z0)
             then mk (MOV, (y :: []))
             else if is_arith_small ofs
                  then mk (ADD,
                         (y :: ((eword_of_int arm_decl.reg_size ofs) :: [])))
                  else (match y with
                        | Pvar y_ ->
                          if (&&)
                               (negb
                                 (eq_op Var.var_eqType (Obj.magic x_.v_var)
                                   (Obj.magic y_.gv.v_var)))
                               ((&&) (is_lvar y_)
                                 ((&&)
                                   (eq_op stype_eqType
                                     (Obj.magic Var.vtype x_.v_var)
                                     (Obj.magic (Coq_sword U32)))
                                   (eq_op stype_eqType
                                     (Obj.magic Var.vtype y_.gv.v_var)
                                     (Obj.magic (Coq_sword U32)))))
                          then Some (Copn ((x :: ((Lvar y_.gv) :: [])), tag,
                                 (Oasm (ExtOp Oarm_add_large_imm)),
                                 (y :: ((eword_of_int arm_decl.reg_size ofs) :: []))))
                          else None
                        | _ -> None)
      | Lmem (_, _, _) ->
        if eq_op coq_Z_eqType (Obj.magic ofs) (Obj.magic Z0)
        then mk (STR, (y :: []))
        else None
      | _ -> None))

(** val arm_immediate :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z ->
    arm_extended_op instr_r **)

let arm_immediate atoI x z =
  Copn (((Lvar x) :: []), AT_none,
    (coq_Oarm atoI (ARM_op (MOV, default_opts))),
    ((cast_const (arch_pd arm_decl) z) :: []))

(** val arm_swap :
    (register, __, __, rflag, condt) arch_toIdent -> assgn_tag -> var_i ->
    var_i -> var_i -> var_i -> (register, __, __, rflag, condt, arm_op,
    arm_extra_op) extended_op instr_r **)

let arm_swap _ t x y z w =
  Copn (((Lvar x) :: ((Lvar y) :: [])), t, (Oasm (ExtOp (Oarm_swap
    arm_decl.reg_size))), ((coq_Plvar z) :: ((coq_Plvar w) :: [])))

(** val arm_saparams :
    (register, __, __, rflag, condt) arch_toIdent -> (register, __, __,
    rflag, condt, arm_op, arm_extra_op) extended_op stack_alloc_params **)

let arm_saparams atoI =
  { sap_mov_ofs = (arm_mov_ofs atoI); sap_immediate = (arm_immediate atoI);
    sap_swap = (arm_swap atoI) }

(** val arm_allocate_stack_frame :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i option ->
    coq_Z -> ((FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval
    list) list **)

let arm_allocate_stack_frame atoI rspi tmp sz =
  match tmp with
  | Some aux -> ARMFopn.smart_subi_tmp atoI rspi aux sz
  | None -> (ARMFopn.subi atoI rspi rspi sz) :: []

(** val arm_free_stack_frame :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i option ->
    coq_Z -> ((FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval
    list) list **)

let arm_free_stack_frame atoI rspi tmp sz =
  match tmp with
  | Some aux -> ARMFopn.smart_addi_tmp atoI rspi aux sz
  | None -> (ARMFopn.addi atoI rspi rspi sz) :: []

(** val arm_set_up_sp_register :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z -> wsize
    -> var_i -> var_i -> ((lexpr list * (register, __, __, rflag, condt,
    arm_op, arm_extra_op) extended_op sopn) * rexpr list) list **)

let arm_set_up_sp_register atoI rspi sf_sz al r tmp =
  let load_imm = ARMFopn.smart_subi atoI tmp rspi sf_sz in
  let i0 = ARMFopn.align atoI tmp tmp al in
  let i1 = ARMFopn.mov atoI r rspi in
  let i2 = ARMFopn.mov atoI rspi tmp in
  cat load_imm (i0 :: (i1 :: (i2 :: [])))

(** val arm_tmp :
    (register, __, __, rflag, condt) arch_toIdent -> Ident.Ident.ident **)

let arm_tmp atoI =
  Var.vname
    (mk_var_i
      (to_var (Coq_sword arm_decl.reg_size) arm_decl.toS_r atoI.toI_r R12)).v_var

(** val arm_tmp2 :
    (register, __, __, rflag, condt) arch_toIdent -> Ident.Ident.ident **)

let arm_tmp2 atoI =
  Var.vname
    (mk_var_i
      (to_var (Coq_sword arm_decl.reg_size) arm_decl.toS_r atoI.toI_r LR)).v_var

(** val arm_lmove :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> (lexpr
    list * arm_extended_op sopn) * rexpr list **)

let arm_lmove atoI xd xs =
  ((((LLvar xd) :: []), (coq_Oarm atoI (ARM_op (MOV, default_opts)))),
    ((Rexpr (Fvar xs)) :: []))

(** val arm_check_ws : Equality.sort -> bool **)

let arm_check_ws ws =
  eq_op wsize_eqType ws (Obj.magic arm_decl.reg_size)

(** val arm_lstore :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z -> var_i
    -> (lexpr list * arm_extended_op sopn) * rexpr list **)

let arm_lstore atoI xd ofs xs =
  let ws = arm_decl.reg_size in
  let mn = STR in
  ((((Store (ws, xd, (fconst ws ofs))) :: []),
  (coq_Oarm atoI (ARM_op (mn, default_opts)))), ((Rexpr (Fvar xs)) :: []))

(** val arm_lload :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z
    -> (lexpr list * arm_extended_op sopn) * rexpr list **)

let arm_lload atoI xd xs ofs =
  let ws = arm_decl.reg_size in
  let mn = LDR in
  ((((LLvar xd) :: []), (coq_Oarm atoI (ARM_op (mn, default_opts)))), ((Load
  (ws, xs, (fconst ws ofs))) :: []))

(** val arm_liparams :
    (register, __, __, rflag, condt) arch_toIdent -> (register, __, __,
    rflag, condt, arm_op, arm_extra_op) extended_op linearization_params **)

let arm_liparams atoI =
  { lip_tmp = (arm_tmp atoI); lip_tmp2 = (arm_tmp2 atoI);
    lip_not_saved_stack = ((arm_tmp atoI) :: []); lip_allocate_stack_frame =
    (arm_allocate_stack_frame atoI); lip_free_stack_frame =
    (arm_free_stack_frame atoI); lip_set_up_sp_register =
    (arm_set_up_sp_register atoI); lip_lmove = (arm_lmove atoI);
    lip_check_ws = (Obj.magic arm_check_ws); lip_lstore = (arm_lstore atoI);
    lip_lstores =
    (lstores_imm_dfl (arch_pd arm_decl) (asm_opI (arm_extra atoI))
      (arm_tmp2 atoI) (arm_lstore atoI) (ARMFopn.smart_addi atoI)
      is_arith_small); lip_lloads =
    (lloads_imm_dfl (arch_pd arm_decl) (asm_opI (arm_extra atoI))
      (arm_tmp2 atoI) (arm_lload atoI) (ARMFopn.smart_addi atoI)
      is_arith_small) }

(** val arm_fvars_correct :
    (register, __, __, rflag, condt) arch_toIdent -> fresh_vars -> progT ->
    (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op
    fun_decl list -> bool **)

let arm_fvars_correct atoI fv pT fds =
  fvars_correct (asm_opI (arm_extra atoI)) pT (all_fresh_vars fv) (fvars fv)
    fds

(** val arm_loparams :
    (register, __, __, rflag, condt) arch_toIdent -> ((register, __, __,
    rflag, condt, arm_op, arm_extra_op) extended_op, lowering_options)
    lowering_params **)

let arm_loparams atoI =
  { lop_lower_i = (fun _ _ -> Arm_lowering.lower_i atoI); lop_fvars_correct =
    (arm_fvars_correct atoI) }

(** val arm_shparams :
    (register, __, __, rflag, condt) arch_toIdent -> (register, __, __,
    rflag, condt, arm_op, arm_extra_op) extended_op sh_params **)

let arm_shparams _ =
  let pc_err_msg =
    'C'::('A'::('L'::('L'::('/'::('R'::('E'::('T'::(' '::('p'::('r'::('o'::('t'::('e'::('c'::('t'::('i'::('o'::('n'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::(' '::('f'::('o'::('r'::(' '::('C'::('o'::('r'::('t'::('e'::('x'::(' '::('M'::('4'::[]))))))))))))))))))))))))))))))))))))))))))))))
  in
  { shp_lower = (fun _ _ _ -> None); shp_update_after_call = (fun err _ ->
  Error (err (Some pc_err_msg))) }

(** val arm_pcparams :
    (register, __, __, rflag, condt) arch_toIdent -> (register, __, __,
    rflag, condt, arm_op, arm_extra_op) extended_op protect_calls_params **)

let arm_pcparams _ =
  let pc_err_msg =
    'C'::('A'::('L'::('L'::('/'::('R'::('E'::('T'::(' '::('p'::('r'::('o'::('t'::('e'::('c'::('t'::('i'::('o'::('n'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::(' '::('f'::('o'::('r'::(' '::('C'::('o'::('r'::('t'::('e'::('x'::(' '::('M'::('4'::[]))))))))))))))))))))))))))))))))))))))))))))))
  in
  { pcp_is_update_after_call = (fun _ -> false);
  pcp_lower_update_after_call = (fun err _ _ _ _ _ -> Error
  (err (Some pc_err_msg))); pcp_load_tag = (fun err _ -> Error
  (err (Some pc_err_msg))); pcp_cmpi = (fun err _ _ -> Error
  (err (Some pc_err_msg))); pcp_cond_ne = (Fconst Z0); pcp_cond_gt = (Fconst
  Z0); pcp_save_ra = (fun err _ _ -> Error (err (Some pc_err_msg))) }

(** val condt_of_rflag : rflag -> condt **)

let condt_of_rflag = function
| NF -> MI_ct
| ZF -> EQ_ct
| CF -> CS_ct
| VF -> VS_ct

(** val condt_not : condt -> condt **)

let condt_not = function
| EQ_ct -> NE_ct
| NE_ct -> EQ_ct
| CS_ct -> CC_ct
| CC_ct -> CS_ct
| MI_ct -> PL_ct
| PL_ct -> MI_ct
| VS_ct -> VC_ct
| VC_ct -> VS_ct
| HI_ct -> LS_ct
| LS_ct -> HI_ct
| GE_ct -> LT_ct
| LT_ct -> GE_ct
| GT_ct -> LE_ct
| LE_ct -> GT_ct

(** val condt_and : condt -> condt -> condt option **)

let condt_and c0 c1 =
  match c0 with
  | NE_ct ->
    (match c1 with
     | CS_ct -> Some HI_ct
     | GE_ct -> Some GT_ct
     | _ -> None)
  | CS_ct -> (match c1 with
              | NE_ct -> Some HI_ct
              | _ -> None)
  | GE_ct -> (match c1 with
              | NE_ct -> Some GT_ct
              | _ -> None)
  | _ -> None

(** val condt_or : condt -> condt -> condt option **)

let condt_or c0 c1 =
  match c0 with
  | EQ_ct ->
    (match c1 with
     | CC_ct -> Some LS_ct
     | LT_ct -> Some LE_ct
     | _ -> None)
  | CC_ct -> (match c1 with
              | EQ_ct -> Some LS_ct
              | _ -> None)
  | LT_ct -> (match c1 with
              | EQ_ct -> Some LE_ct
              | _ -> None)
  | _ -> None

(** val is_rflags_GE : rflag -> rflag -> bool **)

let is_rflags_GE r0 r1 =
  match r0 with
  | NF -> (match r1 with
           | VF -> true
           | _ -> false)
  | VF -> (match r1 with
           | NF -> true
           | _ -> false)
  | _ -> false

(** val assemble_cond :
    (register, __, __, rflag, condt) arch_toIdent -> instr_info -> fexpr ->
    condt cexec **)

let rec assemble_cond atoI ii e = match e with
| Fvar v ->
  (match of_var_e Coq_sbool arm_decl.toS_f atoI.toI_f ii v with
   | Ok x -> Ok (condt_of_rflag x)
   | Error s -> Error s)
| Fapp1 (s, e0) ->
  (match s with
   | Onot ->
     (match assemble_cond atoI ii e0 with
      | Ok x -> Ok (condt_not x)
      | Error s0 -> Error s0)
   | _ ->
     Error
       (Asm_gen.E.berror ii e
         ('C'::('a'::('n'::('\''::('t'::(' '::('a'::('s'::('s'::('e'::('m'::('b'::('l'::('e'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))
| Fapp2 (s, e0, e1) ->
  (match s with
   | Obeq ->
     (match e0 with
      | Fvar x0 ->
        (match e1 with
         | Fvar x1 ->
           (match of_var_e Coq_sbool arm_decl.toS_f atoI.toI_f ii x0 with
            | Ok x ->
              (match of_var_e Coq_sbool arm_decl.toS_f atoI.toI_f ii x1 with
               | Ok x2 ->
                 if is_rflags_GE x x2
                 then Ok GE_ct
                 else Error
                        (Asm_gen.E.berror ii e
                          ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('('::('E'::('Q'::(')'::('.'::[]))))))))))))))))))))))))
               | Error s0 -> Error s0)
            | Error s0 -> Error s0)
         | _ ->
           Error
             (Asm_gen.E.berror ii e
               ('C'::('a'::('n'::('\''::('t'::(' '::('a'::('s'::('s'::('e'::('m'::('b'::('l'::('e'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))
      | _ ->
        Error
          (Asm_gen.E.berror ii e
            ('C'::('a'::('n'::('\''::('t'::(' '::('a'::('s'::('s'::('e'::('m'::('b'::('l'::('e'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))
   | Oand ->
     (match assemble_cond atoI ii e0 with
      | Ok x ->
        (match assemble_cond atoI ii e1 with
         | Ok x0 ->
           (match condt_and x x0 with
            | Some ct -> Ok ct
            | None ->
              Error
                (Asm_gen.E.berror ii e
                  ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('('::('A'::('N'::('D'::(')'::[])))))))))))))))))))))))))
         | Error s0 -> Error s0)
      | Error s0 -> Error s0)
   | Oor ->
     (match assemble_cond atoI ii e0 with
      | Ok x ->
        (match assemble_cond atoI ii e1 with
         | Ok x0 ->
           (match condt_or x x0 with
            | Some ct -> Ok ct
            | None ->
              Error
                (Asm_gen.E.berror ii e
                  ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('('::('O'::('R'::(')'::[]))))))))))))))))))))))))
         | Error s0 -> Error s0)
      | Error s0 -> Error s0)
   | _ ->
     Error
       (Asm_gen.E.berror ii e
         ('C'::('a'::('n'::('\''::('t'::(' '::('a'::('s'::('s'::('e'::('m'::('b'::('l'::('e'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))
| _ ->
  Error
    (Asm_gen.E.berror ii e
      ('C'::('a'::('n'::('\''::('t'::(' '::('a'::('s'::('s'::('e'::('m'::('b'::('l'::('e'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::('.'::[]))))))))))))))))))))))))))

(** val arm_agparams :
    (register, __, __, rflag, condt) arch_toIdent -> (register, __, __,
    rflag, condt, arm_op, arm_extra_op) asm_gen_params **)

let arm_agparams =
  assemble_cond

(** val arm_szparams :
    (register, __, __, rflag, condt) arch_toIdent -> (register, __, __,
    rflag, condt, arm_op, arm_extra_op) extended_op stack_zeroization_params **)

let arm_szparams =
  stack_zeroization_cmd

(** val arm_is_move_op :
    (register, __, __, rflag, condt) arch_toIdent -> (register, __, __,
    rflag, condt, arm_op, arm_extra_op) extended_op asm_op_t -> bool **)

let arm_is_move_op _ = function
| BaseOp a ->
  let (o0, a0) = a in
  (match o0 with
   | Some _ -> false
   | None ->
     let ARM_op (a1, opts) = a0 in
     (match a1 with
      | MOV ->
        (&&) (negb opts.set_flags)
          ((&&) (negb opts.is_conditional)
            (negb (Ssrbool.isSome opts.has_shift)))
      | _ -> false))
| ExtOp _ -> false

(** val arm_params :
    (register, __, __, rflag, condt) arch_toIdent -> (register, __, __,
    rflag, condt, arm_op, arm_extra_op, lowering_options) architecture_params **)

let arm_params atoI =
  { ap_sap = (arm_saparams atoI); ap_lip = (arm_liparams atoI); ap_lop =
    (arm_loparams atoI); ap_shp = (arm_shparams atoI); ap_pcp =
    (arm_pcparams atoI); ap_agp = (arm_agparams atoI); ap_szp =
    (arm_szparams atoI); ap_is_move_op = (arm_is_move_op atoI) }
