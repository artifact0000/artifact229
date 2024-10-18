open BinInt
open BinNums
open Datatypes
open Arch_decl
open Arch_extra
open Arm_decl
open Arm_extra
open Arm_instr_decl
open Eqtype
open Expr
open Lowering
open Pseudo_operator
open Seq
open Shift_kind
open Sopn
open Ssralg
open Ssrbool
open Type
open Utils0
open Var0
open Word0
open Wsize

type __ = Obj.t

(** val fv_NF : fresh_vars -> Ident.Ident.ident **)

let fv_NF fv =
  fv (Ident.Ident.name_of_string ('_'::('_'::('n'::('_'::('_'::[]))))))
    Coq_sbool

(** val fv_ZF : fresh_vars -> Ident.Ident.ident **)

let fv_ZF fv =
  fv (Ident.Ident.name_of_string ('_'::('_'::('z'::('_'::('_'::[]))))))
    Coq_sbool

(** val fv_CF : fresh_vars -> Ident.Ident.ident **)

let fv_CF fv =
  fv (Ident.Ident.name_of_string ('_'::('_'::('c'::('_'::('_'::[]))))))
    Coq_sbool

(** val fv_VF : fresh_vars -> Ident.Ident.ident **)

let fv_VF fv =
  fv (Ident.Ident.name_of_string ('_'::('_'::('v'::('_'::('_'::[]))))))
    Coq_sbool

(** val all_fresh_vars : fresh_vars -> Ident.Ident.ident list **)

let all_fresh_vars fv =
  (fv_NF fv) :: ((fv_ZF fv) :: ((fv_CF fv) :: ((fv_VF fv) :: [])))

(** val fvNF : fresh_vars -> Var.var **)

let fvNF fv =
  { Var.vtype = Coq_sbool; Var.vname = (fv_NF fv) }

(** val fvZF : fresh_vars -> Var.var **)

let fvZF fv =
  { Var.vtype = Coq_sbool; Var.vname = (fv_ZF fv) }

(** val fvCF : fresh_vars -> Var.var **)

let fvCF fv =
  { Var.vtype = Coq_sbool; Var.vname = (fv_CF fv) }

(** val fvVF : fresh_vars -> Var.var **)

let fvVF fv =
  { Var.vtype = Coq_sbool; Var.vname = (fv_VF fv) }

(** val fresh_flags : fresh_vars -> Var.var list **)

let fresh_flags fv =
  (fvNF fv) :: ((fvZF fv) :: ((fvCF fv) :: ((fvVF fv) :: [])))

(** val fvars : fresh_vars -> SvExtra.Sv.t **)

let fvars fv =
  SvExtra.sv_of_list (fun x -> Obj.magic x) (fresh_flags fv)

(** val chk_ws_reg : wsize -> unit option **)

let chk_ws_reg ws =
  oassert (eq_op wsize_eqType (Obj.magic ws) (Obj.magic arm_decl.reg_size))

(** val flags_of_mn : fresh_vars -> arm_mnemonic -> Var.var list **)

let flags_of_mn fv mn =
  let ids =
    match mn with
    | ADD -> []
    | ADC -> []
    | MUL -> []
    | MLA -> []
    | MLS -> []
    | SDIV -> []
    | SUB -> []
    | RSB -> []
    | UDIV -> []
    | UMULL -> []
    | UMAAL -> []
    | UMLAL -> []
    | SMULL -> []
    | SMLAL -> []
    | SMMUL -> []
    | SMMULR -> []
    | SMUL_hw (_, _) -> []
    | SMLA_hw (_, _) -> []
    | SMULW_hw _ -> []
    | AND -> []
    | BFC -> []
    | BFI -> []
    | BIC -> []
    | EOR -> []
    | MVN -> []
    | ORR -> []
    | ASR -> []
    | LSL -> []
    | LSR -> []
    | ROR -> []
    | REV -> []
    | REV16 -> []
    | REVSH -> []
    | ADR -> []
    | MOV -> []
    | MOVT -> []
    | UBFX -> []
    | UXTB -> []
    | UXTH -> []
    | SBFX -> []
    | CLZ -> []
    | CMP -> fvNF :: (fvZF :: (fvCF :: (fvVF :: [])))
    | TST -> fvNF :: (fvZF :: (fvCF :: []))
    | _ -> []
  in
  map (fun x -> x fv) ids

(** val lflags_of_mn : fresh_vars -> arm_mnemonic -> lval list **)

let lflags_of_mn fv mn =
  to_lvals (flags_of_mn fv mn)

(** val lower_TST : pexpr -> pexpr -> pexpr list option **)

let lower_TST e0 e1 =
  match e0 with
  | Papp2 (s, e00, e01) ->
    (match s with
     | Oland _ ->
       (match e1 with
        | Papp1 (s0, p) ->
          (match s0 with
           | Oword_of_int _ ->
             (match p with
              | Pconst z ->
                (match z with
                 | Z0 -> Some (e00 :: (e01 :: []))
                 | _ -> None)
              | _ -> None)
           | _ -> None)
        | _ -> None)
     | _ -> None)
  | _ -> None

(** val lower_condition_Papp2 :
    fresh_vars -> sop2 -> pexpr -> pexpr -> ((arm_mnemonic * pexpr) * pexpr
    list) option **)

let lower_condition_Papp2 fv op e0 e1 =
  match cf_of_condition op with
  | Some p ->
    let (cf, ws) = p in
    (match chk_ws_reg ws with
     | Some _ ->
       let cmp = ((CMP, (pexpr_of_cf cf (fresh_flags fv))),
         (e0 :: (e1 :: [])))
       in
       (match op with
        | Oeq o ->
          (match o with
           | Op_int -> None
           | Op_w _ ->
             let eZF = Pvar (mk_lvar (mk_var_i (fvZF fv))) in
             Some
             (match lower_TST e0 e1 with
              | Some es -> ((TST, eZF), es)
              | None -> cmp))
        | Oneq o -> (match o with
                     | Op_int -> None
                     | Op_w _ -> Some cmp)
        | Olt c -> (match c with
                    | Cmp_int -> None
                    | Cmp_w (_, _) -> Some cmp)
        | Ole c -> (match c with
                    | Cmp_int -> None
                    | Cmp_w (_, _) -> Some cmp)
        | Ogt c -> (match c with
                    | Cmp_int -> None
                    | Cmp_w (_, _) -> Some cmp)
        | Oge c -> (match c with
                    | Cmp_int -> None
                    | Cmp_w (_, _) -> Some cmp)
        | _ -> None)
     | None -> None)
  | None -> None

(** val lower_condition_pexpr :
    (register, __, __, rflag, condt) arch_toIdent -> fresh_vars -> pexpr ->
    (((lval list * (register, __, __, rflag, condt, arm_op, arm_extra_op)
    extended_op sopn) * pexpr list) * pexpr) option **)

let lower_condition_pexpr atoI fv e =
  match is_Papp2 e with
  | Some p ->
    let (p0, e1) = p in
    let (op, e0) = p0 in
    (match lower_condition_Papp2 fv op e0 e1 with
     | Some p1 ->
       let (p2, es) = p1 in
       let (mn, e') = p2 in
       Some ((((lflags_of_mn fv mn),
       (coq_Oarm atoI (ARM_op (mn, default_opts)))), es), e')
     | None -> None)
  | None -> None

(** val lower_condition :
    (register, __, __, rflag, condt) arch_toIdent -> fresh_vars -> pexpr ->
    (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op
    instr_r list * pexpr **)

let lower_condition atoI fv e =
  match lower_condition_pexpr atoI fv e with
  | Some p ->
    let (p0, c) = p in
    let (p1, es) = p0 in
    let (lvs, op) = p1 in (((Copn (lvs, AT_none, op, es)) :: []), c)
  | None -> ([], e)

(** val get_arg_shift :
    wsize -> pexpr list -> ((pexpr * shift_kind) * pexpr) option **)

let get_arg_shift ws = function
| [] -> None
| p :: l ->
  (match p with
   | Papp2 (op, v, n) ->
     (match v with
      | Pvar _ ->
        (match n with
         | Papp1 (s, p0) ->
           (match s with
            | Oword_of_int w ->
              (match w with
               | U8 ->
                 (match p0 with
                  | Pconst z ->
                    (match l with
                     | [] ->
                       (match shift_of_sop2 ws op with
                        | Some sh ->
                          (match oassert (check_shift_amount sh z) with
                           | Some _ -> Some ((v, sh), n)
                           | None -> None)
                        | None -> None)
                     | _ :: _ -> None)
                  | _ -> None)
               | _ -> None)
            | _ -> None)
         | _ -> None)
      | _ -> None)
   | _ -> None)

(** val arg_shift :
    arm_mnemonic -> wsize -> pexpr list -> arm_op * pexpr list **)

let arg_shift mn ws e =
  if in_mem (Obj.magic mn)
       (mem (seq_predType arm_mnemonic_eqType)
         (Obj.magic has_shift_mnemonics))
  then (match get_arg_shift ws e with
        | Some p ->
          let (p0, esham) = p in
          let (ebase, sh) = p0 in
          let osh = Some sh in
          let es = ebase :: (esham :: []) in
          let opts = { set_flags = false; is_conditional = false; has_shift =
            osh }
          in
          ((ARM_op (mn, opts)), es)
        | None ->
          let osh = None in
          let opts = { set_flags = false; is_conditional = false; has_shift =
            osh }
          in
          ((ARM_op (mn, opts)), e))
  else let osh = None in
       let opts = { set_flags = false; is_conditional = false; has_shift =
         osh }
       in
       ((ARM_op (mn, opts)), e)

(** val lower_Pvar : wsize -> gvar -> (arm_op * pexpr list) option **)

let lower_Pvar ws v =
  match chk_ws_reg ws with
  | Some _ ->
    let mn = if is_var_in_memory v.gv.v_var then LDR else MOV in
    Some ((ARM_op (mn, default_opts)), ((Pvar v) :: []))
  | None -> None

(** val lower_load : wsize -> pexpr -> (arm_op * pexpr list) option **)

let lower_load ws e =
  match chk_ws_reg ws with
  | Some _ -> Some ((ARM_op (LDR, default_opts)), (e :: []))
  | None -> None

(** val is_load : pexpr -> bool **)

let is_load = function
| Pvar g ->
  let { gv = x; gs = gs0 } = g in
  (match gs0 with
   | Slocal -> is_var_in_memory x.v_var
   | Sglob -> true)
| Pget (_, _, _, _) -> true
| Pload (_, _, _) -> true
| _ -> false

(** val coq_Z_mod_lnot : coq_Z -> wsize -> coq_Z **)

let coq_Z_mod_lnot z ws =
  let m = wbase ws in Z.modulo (Z.lnot (Z.modulo z m)) m

(** val mov_imm_mnemonic : pexpr -> (arm_mnemonic * pexpr) option **)

let mov_imm_mnemonic e =
  match is_const e with
  | Some z ->
    if (||) (is_expandable_or_shift z) (is_w16_encoding z)
    then Some (MOV, e)
    else let nz = coq_Z_mod_lnot z arm_decl.reg_size in
         (match oassert (is_expandable_or_shift nz) with
          | Some _ -> Some (MVN, (Pconst nz))
          | None -> None)
  | None -> Some (MOV, e)

(** val lower_Papp1 :
    wsize -> sop1 -> pexpr -> (arm_op * pexpr list) option **)

let lower_Papp1 ws op e =
  match chk_ws_reg ws with
  | Some _ ->
    (match op with
     | Oword_of_int ws' ->
       (match oassert (cmp_le wsize_cmp U32 ws') with
        | Some _ ->
          (match mov_imm_mnemonic e with
           | Some p ->
             let (mn, e') = p in
             Some ((ARM_op (mn, default_opts)), ((Papp1 ((Oword_of_int U32),
             e')) :: []))
           | None -> None)
        | None -> None)
     | Osignext (w, ws') ->
       (match w with
        | U32 ->
          (match oassert (is_load e) with
           | Some _ ->
             (match sload_mn_of_wsize ws' with
              | Some mn -> Some ((ARM_op (mn, default_opts)), (e :: []))
              | None -> None)
           | None -> None)
        | _ -> None)
     | Ozeroext (w, ws') ->
       (match w with
        | U32 ->
          (match oassert (is_load e) with
           | Some _ ->
             (match uload_mn_of_wsize ws' with
              | Some mn -> Some ((ARM_op (mn, default_opts)), (e :: []))
              | None -> None)
           | None -> None)
        | _ -> None)
     | Olnot w ->
       (match w with
        | U32 -> Some (arg_shift MVN U32 (e :: []))
        | _ -> None)
     | Oneg o ->
       (match o with
        | Op_int -> None
        | Op_w w ->
          (match w with
           | U32 ->
             Some ((ARM_op (RSB, default_opts)),
               (e :: ((wconst U32 (wrepr U32 Z0)) :: [])))
           | _ -> None))
     | _ -> None)
  | None -> None

(** val is_mul : pexpr -> (pexpr * pexpr) option **)

let is_mul = function
| Papp2 (s, x, y) ->
  (match s with
   | Omul o ->
     (match o with
      | Op_int -> None
      | Op_w w -> (match w with
                   | U32 -> Some (x, y)
                   | _ -> None))
   | _ -> None)
| _ -> None

(** val is_rsb : wsize -> pexpr -> pexpr -> bool **)

let is_rsb ws e0 e1 =
  match get_arg_shift ws (e0 :: []) with
  | Some _ ->
    (match get_arg_shift ws (e1 :: []) with
     | Some _ -> false
     | None -> true)
  | None ->
    (match get_arg_shift ws (e1 :: []) with
     | Some _ -> false
     | None -> (match is_wconst ws e0 with
                | Some _ -> true
                | None -> false))

(** val lower_Papp2_op :
    wsize -> sop2 -> pexpr -> pexpr -> ((arm_mnemonic * pexpr) * pexpr list)
    option **)

let lower_Papp2_op ws op e0 e1 =
  match chk_ws_reg ws with
  | Some _ ->
    (match op with
     | Oadd o ->
       (match o with
        | Op_int -> None
        | Op_w _ ->
          (match is_mul e0 with
           | Some p -> let (x, y) = p in Some ((MLA, x), (y :: (e1 :: [])))
           | None ->
             (match is_mul e1 with
              | Some p -> let (x, y) = p in Some ((MLA, x), (y :: (e0 :: [])))
              | None -> Some ((ADD, e0), (e1 :: [])))))
     | Omul o ->
       (match o with
        | Op_int -> None
        | Op_w _ -> Some ((MUL, e0), (e1 :: [])))
     | Osub o ->
       (match o with
        | Op_int -> None
        | Op_w _ ->
          (match is_mul e1 with
           | Some p -> let (x, y) = p in Some ((MLS, x), (y :: (e0 :: [])))
           | None ->
             if is_rsb ws e0 e1
             then Some ((RSB, e1), (e0 :: []))
             else Some ((SUB, e0), (e1 :: []))))
     | Odiv c ->
       (match c with
        | Cmp_int -> None
        | Cmp_w (s, w) ->
          (match s with
           | Signed ->
             (match w with
              | U32 -> Some ((SDIV, e0), (e1 :: []))
              | _ -> None)
           | Unsigned ->
             (match w with
              | U32 -> Some ((UDIV, e0), (e1 :: []))
              | _ -> None)))
     | Oland _ -> Some ((AND, e0), (e1 :: []))
     | Olor _ -> Some ((ORR, e0), (e1 :: []))
     | Olxor _ -> Some ((EOR, e0), (e1 :: []))
     | Olsr w ->
       (match w with
        | U32 ->
          if is_zero (Obj.magic U8) e1
          then Some ((MOV, e0), [])
          else Some ((LSR, e0), (e1 :: []))
        | _ -> None)
     | Olsl o ->
       (match o with
        | Op_int -> None
        | Op_w w ->
          (match w with
           | U32 -> Some ((LSL, e0), (e1 :: []))
           | _ -> None))
     | Oasr o ->
       (match o with
        | Op_int -> None
        | Op_w w ->
          (match w with
           | U32 ->
             if is_zero (Obj.magic U8) e1
             then Some ((MOV, e0), [])
             else Some ((ASR, e0), (e1 :: []))
           | _ -> None))
     | Oror w ->
       (match w with
        | U32 ->
          if is_zero (Obj.magic U8) e1
          then Some ((MOV, e0), [])
          else Some ((ROR, e0), (e1 :: []))
        | _ -> None)
     | Orol w ->
       (match w with
        | U32 ->
          (match is_wconst U8 e1 with
           | Some c ->
             if eq_op (GRing.ComRing.eqType (word U8)) c
                  (GRing.zero (GRing.ComRing.zmodType (word U8)))
             then Some ((MOV, e0), [])
             else Some ((ROR, e0),
                    ((wconst U8
                       (GRing.add
                         (GRing.Ring.zmodType
                           (GRing.ComRing.ringType (word U8)))
                         (GRing.natmul
                           (GRing.Ring.zmodType
                             (GRing.ComRing.ringType (word U8)))
                           (GRing.one (GRing.ComRing.ringType (word U8))) (S
                           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                           (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                           O)))))))))))))))))))))))))))))))))
                         (GRing.opp (GRing.ComRing.zmodType (word U8)) c))) :: []))
           | None -> None)
        | _ -> None)
     | _ -> None)
  | None -> None

(** val lower_Papp2 :
    wsize -> sop2 -> pexpr -> pexpr -> (arm_op * pexpr list) option **)

let lower_Papp2 ws op e0 e1 =
  match lower_Papp2_op ws op e0 e1 with
  | Some p ->
    let (p0, e1') = p in
    let (mn, e0') = p0 in
    let (aop, es) = arg_shift mn ws e1' in Some (aop, (e0' :: es))
  | None -> None

(** val lower_pexpr_aux : wsize -> pexpr -> (arm_op * pexpr list) option **)

let lower_pexpr_aux ws e = match e with
| Pvar v -> lower_Pvar ws v
| Pget (_, _, _, _) -> lower_load ws e
| Pload (_, _, _) -> lower_load ws e
| Papp1 (op, e0) -> lower_Papp1 ws op e0
| Papp2 (op, a, b) -> lower_Papp2 ws op a b
| _ -> None

(** val no_pre :
    (register, __, __, rflag, condt) arch_toIdent -> (arm_op * pexpr list)
    option -> (((register, __, __, rflag, condt, arm_op, arm_extra_op)
    extended_op instr_r list * arm_op) * pexpr list) option **)

let no_pre _ = function
| Some p -> let (aop, es) = p in Some (([], aop), es)
| None -> None

(** val lower_pexpr :
    (register, __, __, rflag, condt) arch_toIdent -> fresh_vars -> wsize ->
    pexpr -> (((register, __, __, rflag, condt, arm_op, arm_extra_op)
    extended_op instr_r list * arm_op) * pexpr list) option **)

let lower_pexpr atoI fv ws e = match e with
| Pif (s, c, e0, e1) ->
  (match s with
   | Coq_sword ws' ->
     (match oassert (eq_op wsize_eqType (Obj.magic ws) (Obj.magic ws')) with
      | Some _ ->
        (match lower_pexpr_aux ws e0 with
         | Some p ->
           let (a, es) = p in
           let ARM_op (mn, opts) = a in
           let (pre, c') = lower_condition atoI fv c in
           Some ((pre, (ARM_op (mn, (set_is_conditional opts)))),
           (cat es (c' :: (e1 :: []))))
         | None -> None)
      | None -> None)
   | _ -> no_pre atoI (lower_pexpr_aux ws e))
| _ -> no_pre atoI (lower_pexpr_aux ws e)

(** val lower_store : wsize -> pexpr -> (arm_op * pexpr list) option **)

let lower_store ws e =
  match store_mn_of_wsize ws with
  | Some mn ->
    (match e with
     | Pconst _ -> None
     | Pbool _ -> None
     | Parr_init _ -> None
     | Pvar _ ->
       let p = (default_opts, (e :: [])) in
       let (opts, es) = p in Some ((ARM_op (mn, opts)), es)
     | Pif (_, c, e0, e1) ->
       let p = ((set_is_conditional default_opts), (e0 :: (c :: (e1 :: []))))
       in
       let (opts, es) = p in Some ((ARM_op (mn, opts)), es)
     | _ -> None)
  | None -> None

(** val lower_cassgn_word :
    (register, __, __, rflag, condt) arch_toIdent -> fresh_vars -> lval ->
    wsize -> pexpr -> ((register, __, __, rflag, condt, arm_op, arm_extra_op)
    extended_op instr_r list * ((lval list * (register, __, __, rflag, condt,
    arm_op, arm_extra_op) extended_op sopn) * pexpr list)) option **)

let lower_cassgn_word atoI fv lv ws e =
  match if is_lval_in_memory lv
        then no_pre atoI (lower_store ws e)
        else lower_pexpr atoI fv ws e with
  | Some p ->
    let (p0, es) = p in
    let (pre, aop) = p0 in Some (pre, (((lv :: []), (coq_Oarm atoI aop)), es))
  | None -> None

(** val lower_cassgn_bool :
    (register, __, __, rflag, condt) arch_toIdent -> fresh_vars -> lval ->
    assgn_tag -> pexpr -> (register, __, __, rflag, condt, arm_op,
    arm_extra_op) extended_op instr_r list option **)

let lower_cassgn_bool atoI fv lv tag e =
  match lower_condition_pexpr atoI fv e with
  | Some p ->
    let (p0, c) = p in
    let (p1, es) = p0 in
    let (lvs, op) = p1 in
    Some ((Copn (lvs, tag, op, es)) :: ((Cassgn (lv, AT_inline, Coq_sbool,
    c)) :: []))
  | None -> None

(** val lower_add_carry :
    (register, __, __, rflag, condt) arch_toIdent -> lval list -> pexpr list
    -> ((lval list * (register, __, __, rflag, condt, arm_op, arm_extra_op)
    extended_op sopn) * pexpr list) option **)

let lower_add_carry _ lvs es =
  match lvs with
  | [] -> None
  | cf :: l ->
    (match l with
     | [] -> None
     | r :: l0 ->
       (match l0 with
        | [] ->
          (match es with
           | [] -> None
           | x :: l1 ->
             (match l1 with
              | [] -> None
              | y :: l2 ->
                (match l2 with
                 | [] -> None
                 | b :: l3 ->
                   (match l3 with
                    | [] ->
                      (match b with
                       | Pconst _ -> None
                       | Pbool b0 ->
                         if b0
                         then None
                         else let p = (ADD, (x :: (y :: []))) in
                              let (mn, es') = p in
                              let opts = { set_flags = true; is_conditional =
                                false; has_shift = None }
                              in
                              let lnoneb = Lnone (dummy_var_info, Coq_sbool)
                              in
                              let lvs' =
                                lnoneb :: (lnoneb :: (cf :: (lnoneb :: (r :: []))))
                              in
                              Some ((lvs', (Oasm (BaseOp (None, (ARM_op (mn,
                              opts)))))), es')
                       | Pvar _ ->
                         let p = (ADC, es) in
                         let (mn, es') = p in
                         let opts = { set_flags = true; is_conditional =
                           false; has_shift = None }
                         in
                         let lnoneb = Lnone (dummy_var_info, Coq_sbool) in
                         let lvs' =
                           lnoneb :: (lnoneb :: (cf :: (lnoneb :: (r :: []))))
                         in
                         Some ((lvs', (Oasm (BaseOp (None, (ARM_op (mn,
                         opts)))))), es')
                       | _ -> None)
                    | _ :: _ -> None))))
        | _ :: _ -> None))

(** val lower_mulu :
    (register, __, __, rflag, condt) arch_toIdent -> lval list -> pexpr list
    -> ((lval list * (register, __, __, rflag, condt, arm_op, arm_extra_op)
    extended_op sopn) * pexpr list) option **)

let lower_mulu _ lvs es =
  Some ((lvs, (Oasm (BaseOp (None, (ARM_op (UMULL, default_opts)))))), es)

(** val with_shift : arm_options -> shift_kind -> arm_options **)

let with_shift opts sh =
  { set_flags = opts.set_flags; is_conditional = opts.is_conditional;
    has_shift = (Some sh) }

(** val lower_base_op :
    (register, __, __, rflag, condt) arch_toIdent -> lval list -> arm_op ->
    pexpr list -> ((lval list * (register, __, __, rflag, condt, arm_op,
    arm_extra_op) extended_op sopn) * pexpr list) option **)

let lower_base_op _ lvs aop es =
  let ARM_op (mn, opts) = aop in
  if negb
       (eq_op (option_eqType shift_kind_eqType) (Obj.magic opts.has_shift)
         (Obj.magic None))
  then (match oassert
                (in_mem (Obj.magic mn)
                  (mem (seq_predType arm_mnemonic_eqType)
                    (Obj.magic has_shift_mnemonics))) with
        | Some _ ->
          Some ((lvs, (Oasm (BaseOp (None, (ARM_op (mn, opts)))))), es)
        | None -> None)
  else if eq_op arm_mnemonic_eqType (Obj.magic MVN) (Obj.magic mn)
       then (match es with
             | [] -> None
             | x :: rest ->
               (match get_arg_shift U32 (x :: []) with
                | Some p ->
                  let (p0, esham) = p in
                  let (ebase, sh) = p0 in
                  Some ((lvs, (Oasm (BaseOp (None, (ARM_op (mn,
                  (with_shift opts sh))))))), (ebase :: (esham :: rest)))
                | None ->
                  Some ((lvs, (Oasm (BaseOp (None, (ARM_op (mn, opts)))))),
                    es)))
       else if in_mem (Obj.magic mn)
                 (mem (seq_predType arm_mnemonic_eqType)
                   (Obj.magic
                     (ADD :: (SUB :: (RSB :: (AND :: (BIC :: (EOR :: (ORR :: (CMP :: (TST :: [])))))))))))
            then (match es with
                  | [] -> None
                  | x :: l ->
                    (match l with
                     | [] -> None
                     | y :: rest ->
                       (match get_arg_shift U32 (y :: []) with
                        | Some p ->
                          let (p0, esham) = p in
                          let (ebase, sh) = p0 in
                          Some ((lvs, (Oasm (BaseOp (None, (ARM_op (mn,
                          (with_shift opts sh))))))),
                          (x :: (ebase :: (esham :: rest))))
                        | None ->
                          Some ((lvs, (Oasm (BaseOp (None, (ARM_op (mn,
                            opts)))))), es))))
            else if eq_op arm_mnemonic_eqType (Obj.magic ADC) (Obj.magic mn)
                 then (match es with
                       | [] -> None
                       | x :: l ->
                         (match l with
                          | [] -> None
                          | y :: l0 ->
                            (match l0 with
                             | [] -> None
                             | z :: rest ->
                               (match get_arg_shift U32 (y :: []) with
                                | Some p ->
                                  let (p0, esham) = p in
                                  let (ebase, sh) = p0 in
                                  Some ((lvs, (Oasm (BaseOp (None, (ARM_op
                                  (mn, (with_shift opts sh))))))),
                                  (x :: (ebase :: (z :: (esham :: rest)))))
                                | None ->
                                  Some ((lvs, (Oasm (BaseOp (None, (ARM_op
                                    (mn, opts)))))), es)))))
                 else None

(** val lower_swap :
    (register, __, __, rflag, condt) arch_toIdent -> stype -> lval list ->
    pexpr list -> ((lval list * (register, __, __, rflag, condt, arm_op,
    arm_extra_op) extended_op sopn) * pexpr list) option **)

let lower_swap _ ty lvs es =
  match ty with
  | Coq_sarr _ -> Some ((lvs, (Opseudo_op (Oswap ty))), es)
  | Coq_sword sz ->
    if cmp_le wsize_cmp sz U32
    then Some ((lvs, (Oasm (ExtOp (Oarm_swap sz)))), es)
    else None
  | _ -> None

(** val lower_pseudo_operator :
    (register, __, __, rflag, condt) arch_toIdent -> lval list ->
    pseudo_operator -> pexpr list -> ((lval list * (register, __, __, rflag,
    condt, arm_op, arm_extra_op) extended_op sopn) * pexpr list) option **)

let lower_pseudo_operator atoI lvs op es =
  match op with
  | Omulu w -> (match w with
                | U32 -> lower_mulu atoI lvs es
                | _ -> None)
  | Oaddcarry w ->
    (match w with
     | U32 -> lower_add_carry atoI lvs es
     | _ -> None)
  | Oswap ty -> lower_swap atoI ty lvs es
  | _ -> None

(** val lower_copn :
    (register, __, __, rflag, condt) arch_toIdent -> lval list -> (register,
    __, __, rflag, condt, arm_op, arm_extra_op) extended_op sopn -> pexpr
    list -> ((lval list * (register, __, __, rflag, condt, arm_op,
    arm_extra_op) extended_op sopn) * pexpr list) option **)

let lower_copn atoI lvs op es =
  match op with
  | Opseudo_op pop -> lower_pseudo_operator atoI lvs pop es
  | Oasm a ->
    (match a with
     | BaseOp a0 ->
       let (o, aop) = a0 in
       (match o with
        | Some _ -> None
        | None -> lower_base_op atoI lvs aop es)
     | ExtOp _ -> None)
  | _ -> None

type lowering_options = unit

(** val lower_i :
    (register, __, __, rflag, condt) arch_toIdent -> fresh_vars -> (register,
    __, __, rflag, condt, arm_op, arm_extra_op) extended_op instr ->
    (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op instr
    list **)

let rec lower_i atoI fv i = match i with
| MkI (ii, ir) ->
  (match ir with
   | Cassgn (lv, tag, ty, e) ->
     let oirs =
       match ty with
       | Coq_sbool -> lower_cassgn_bool atoI fv lv tag e
       | Coq_sword ws ->
         (match lower_cassgn_word atoI fv lv ws e with
          | Some p ->
            let (pre, p0) = p in
            let (p1, es) = p0 in
            let (lvs, op) = p1 in
            Some (cat pre ((Copn (lvs, tag, op, es)) :: []))
          | None -> None)
       | _ -> None
     in
     let irs = match oirs with
               | Some irs -> irs
               | None -> ir :: [] in
     map (fun x -> MkI (ii, x)) irs
   | Copn (lvs, tag, op, es) ->
     let ir' =
       match lower_copn atoI lvs op es with
       | Some p ->
         let (p0, es') = p in
         let (lvs', op') = p0 in Copn (lvs', tag, op', es')
       | None -> ir
     in
     (MkI (ii, ir')) :: []
   | Cif (e, c1, c2) ->
     let (pre, e') = lower_condition atoI fv e in
     let c1' = conc_map (lower_i atoI fv) c1 in
     let c2' = conc_map (lower_i atoI fv) c2 in
     map (fun x -> MkI (ii, x)) (cat pre ((Cif (e', c1', c2')) :: []))
   | Cfor (v, r, c) ->
     let c' = conc_map (lower_i atoI fv) c in
     (MkI (ii, (Cfor (v, r, c')))) :: []
   | Cwhile (a, c0, e, c1) ->
     let (pre, e') = lower_condition atoI fv e in
     let c0' = conc_map (lower_i atoI fv) c0 in
     let c1' = conc_map (lower_i atoI fv) c1 in
     (MkI (ii, (Cwhile (a, (cat c0' (map (fun x -> MkI (ii, x)) pre)), e',
     c1')))) :: []
   | _ -> i :: [])
