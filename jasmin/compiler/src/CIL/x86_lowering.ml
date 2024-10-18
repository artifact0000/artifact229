open BinInt
open BinNums
open Datatypes
open Arch_decl
open Arch_extra
open Compiler_util
open Eqtype
open Expr
open Lea
open Lowering
open Pseudo_operator
open Seq
open Sopn
open Ssralg
open Ssrfun
open Type
open Utils0
open Var0
open Word0
open Word_ssrZ
open Wsize
open X86_decl
open X86_extra
open X86_instr_decl

(** val is_regx_e : pexpr -> bool **)

let is_regx_e = function
| Pvar x -> is_regx x.gv.v_var
| _ -> false

(** val is_regx_l : lval -> bool **)

let is_regx_l = function
| Lvar x0 -> is_regx x0.v_var
| _ -> false

(** val mov_ws :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    wsize -> lval -> pexpr -> assgn_tag -> x86_extended_op instr_r **)

let mov_ws atoI ws x y tag =
  if (&&) ((||) (is_regx_e y) (is_regx_l x)) (cmp_le wsize_cmp U32 ws)
  then Copn ((x :: []), tag, (coq_Ox86 atoI (MOVX ws)), (y :: []))
  else Copn ((x :: []), tag, (coq_Ox86 atoI (MOV ws)), (y :: []))

type lowering_options = { use_lea : bool; use_set0 : bool }

(** val vword : wsize -> Ident.Ident.ident -> Var.var **)

let vword vt vn =
  { Var.vtype = (Coq_sword vt); Var.vname = vn }

(** val fv_of : fresh_vars -> Var.var **)

let fv_of fv =
  let n = '_'::('_'::('o'::('f'::('_'::('_'::[]))))) in
  { Var.vtype = Coq_sbool; Var.vname =
  (fv (Ident.Ident.name_of_string n) Coq_sbool) }

(** val fv_cf : fresh_vars -> Var.var **)

let fv_cf fv =
  let n = '_'::('_'::('c'::('f'::('_'::('_'::[]))))) in
  { Var.vtype = Coq_sbool; Var.vname =
  (fv (Ident.Ident.name_of_string n) Coq_sbool) }

(** val fv_sf : fresh_vars -> Var.var **)

let fv_sf fv =
  let n = '_'::('_'::('s'::('f'::('_'::('_'::[]))))) in
  { Var.vtype = Coq_sbool; Var.vname =
  (fv (Ident.Ident.name_of_string n) Coq_sbool) }

(** val fv_zf : fresh_vars -> Var.var **)

let fv_zf fv =
  let n = '_'::('_'::('z'::('f'::('_'::('_'::[]))))) in
  { Var.vtype = Coq_sbool; Var.vname =
  (fv (Ident.Ident.name_of_string n) Coq_sbool) }

(** val fvars : fresh_vars -> SvExtra.Sv.t **)

let fvars fv =
  let fresh_word = fun sz ->
    vword sz
      (fv
        (Ident.Ident.name_of_string
          ('_'::('_'::('w'::('t'::('m'::('p'::('_'::('_'::[])))))))))
        (Coq_sword sz))
  in
  foldl (fun s sz -> SvExtra.Sv.add (Obj.magic fresh_word sz) s)
    (SvExtra.Sv.add (Obj.magic fv_of fv)
      (SvExtra.Sv.add (Obj.magic fv_cf fv)
        (SvExtra.Sv.add (Obj.magic fv_sf fv)
          (SvExtra.Sv.singleton (Obj.magic fv_zf fv))))) wsizes

(** val disj_fvars : fresh_vars -> SvExtra.Sv.t -> bool **)

let disj_fvars fv v =
  SvExtra.disjoint v (fvars fv)

(** val fvars_correct :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    fresh_vars -> progT -> (register, register_ext, xmm_register, rflag,
    condt, x86_op, x86_extra_op) extended_op fun_decl list -> bool **)

let fvars_correct atoI fv pT p =
  (&&) (disj_fvars fv (vars_p (asm_opI (x86_extra atoI)) pT p))
    ((&&)
      (negb (eq_op Var.var_eqType (Obj.magic fv_of fv) (Obj.magic fv_cf fv)))
      ((&&)
        (negb
          (eq_op Var.var_eqType (Obj.magic fv_of fv) (Obj.magic fv_sf fv)))
        ((&&)
          (negb
            (eq_op Var.var_eqType (Obj.magic fv_of fv) (Obj.magic fv_zf fv)))
          ((&&)
            (negb
              (eq_op Var.var_eqType (Obj.magic fv_cf fv) (Obj.magic fv_sf fv)))
            ((&&)
              (negb
                (eq_op Var.var_eqType (Obj.magic fv_cf fv)
                  (Obj.magic fv_zf fv)))
              (negb
                (eq_op Var.var_eqType (Obj.magic fv_sf fv)
                  (Obj.magic fv_zf fv))))))))

(** val var_info_of_lval : lval -> var_info **)

let var_info_of_lval = function
| Lnone (i, _) -> i
| Lvar x0 -> x0.v_info
| Lmem (_, x0, _) -> x0.v_info
| Laset (_, _, x0, _) -> x0.v_info
| Lasub (_, _, _, x0, _) -> x0.v_info

(** val stype_of_lval : lval -> stype **)

let stype_of_lval = function
| Lnone (_, t0) -> t0
| Lvar v -> Var.vtype v.v_var
| Lmem (_, v, _) -> Var.vtype v.v_var
| Laset (_, _, v, _) -> Var.vtype v.v_var
| Lasub (_, _, _, v, _) -> Var.vtype v.v_var

(** val wsize_of_stype : stype -> wsize **)

let wsize_of_stype = function
| Coq_sword sz -> sz
| _ -> U64

(** val wsize_of_lval : lval -> wsize **)

let wsize_of_lval = function
| Lnone (_, ty) -> wsize_of_stype ty
| Lvar h ->
  let { v_var = v_var0; v_info = _ } = h in
  let { Var.vtype = ty; Var.vname = _ } = v_var0 in wsize_of_stype ty
| Lmem (sz, _, _) -> sz
| Laset (_, sz, _, _) -> sz
| Lasub (_, _, _, _, _) -> U64

(** val lower_cond_classify :
    fresh_vars -> var_info -> pexpr -> ((((lval
    list * wsize) * pexpr) * pexpr) * pexpr) option **)

let lower_cond_classify fv vi e =
  let fr = fun n -> { v_var = n; v_info = vi } in
  let vof = fr (fv_of fv) in
  let vcf = fr (fv_cf fv) in
  let vsf = fr (fv_sf fv) in
  let vzf = fr (fv_zf fv) in
  let vflags = map (fun v -> v.v_var) (vof :: (vcf :: (vsf :: (vzf :: []))))
  in
  let lof = Lvar vof in
  let lcf = Lvar vcf in
  let lsf = Lvar vsf in
  let lzf = Lvar vzf in
  let lflags = lof :: (lcf :: (lsf :: ((coq_Lnone_b vi) :: (lzf :: [])))) in
  (match is_Papp2 e with
   | Some p ->
     let (p0, e1) = p in
     let (op, e0) = p0 in
     (match cf_of_condition op with
      | Some p1 ->
        let (cf, ws) = p1 in
        Some ((((lflags, ws), (pexpr_of_cf cf vflags)), e0), e1)
      | None -> None)
   | None -> None)

(** val lower_condition :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    fresh_vars -> var_info -> pexpr -> (register, register_ext, xmm_register,
    rflag, condt, x86_op, x86_extra_op) extended_op instr_r list * pexpr **)

let lower_condition atoI fv vi pe =
  match lower_cond_classify fv vi pe with
  | Some p ->
    let (p0, y) = p in
    let (p1, x) = p0 in
    let (p2, r) = p1 in
    let (l, sz) = p2 in
    if cmp_le wsize_cmp sz U64
    then (((Copn (l, AT_none, (coq_Ox86 atoI (CMP sz)),
           (x :: (y :: [])))) :: []), r)
    else ([], pe)
  | None -> ([], pe)

type add_inc_dec =
| AddInc of pexpr
| AddDec of pexpr
| AddNone

(** val add_inc_dec_classify : wsize -> pexpr -> pexpr -> add_inc_dec **)

let add_inc_dec_classify sz a b =
  match a with
  | Pconst _ ->
    (match b with
     | Papp1 (s, p) ->
       (match s with
        | Oword_of_int w ->
          (match p with
           | Pconst z0 ->
             (match z0 with
              | Z0 -> AddNone
              | Zpos p0 ->
                (match p0 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddInc a
                   else AddNone
                 | _ -> AddNone)
              | Zneg p0 ->
                (match p0 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddDec a
                   else AddNone
                 | _ -> AddNone))
           | _ -> AddNone)
        | _ -> AddNone)
     | _ -> AddNone)
  | Pbool _ ->
    (match b with
     | Papp1 (s, p) ->
       (match s with
        | Oword_of_int w ->
          (match p with
           | Pconst z ->
             (match z with
              | Z0 -> AddNone
              | Zpos p0 ->
                (match p0 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddInc a
                   else AddNone
                 | _ -> AddNone)
              | Zneg p0 ->
                (match p0 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddDec a
                   else AddNone
                 | _ -> AddNone))
           | _ -> AddNone)
        | _ -> AddNone)
     | _ -> AddNone)
  | Pvar _ ->
    (match b with
     | Papp1 (s, p) ->
       (match s with
        | Oword_of_int w ->
          (match p with
           | Pconst z ->
             (match z with
              | Z0 -> AddNone
              | Zpos p0 ->
                (match p0 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddInc a
                   else AddNone
                 | _ -> AddNone)
              | Zneg p0 ->
                (match p0 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddDec a
                   else AddNone
                 | _ -> AddNone))
           | _ -> AddNone)
        | _ -> AddNone)
     | _ -> AddNone)
  | Psub (_, _, _, _, _) ->
    (match b with
     | Papp1 (s, p1) ->
       (match s with
        | Oword_of_int w ->
          (match p1 with
           | Pconst z ->
             (match z with
              | Z0 -> AddNone
              | Zpos p2 ->
                (match p2 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddInc a
                   else AddNone
                 | _ -> AddNone)
              | Zneg p2 ->
                (match p2 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddDec a
                   else AddNone
                 | _ -> AddNone))
           | _ -> AddNone)
        | _ -> AddNone)
     | _ -> AddNone)
  | Papp1 (s, p) ->
    (match s with
     | Oword_of_int w ->
       (match p with
        | Pconst z ->
          (match z with
           | Z0 ->
             (match b with
              | Papp1 (s0, p0) ->
                (match s0 with
                 | Oword_of_int w0 ->
                   (match p0 with
                    | Pconst z0 ->
                      (match z0 with
                       | Z0 -> AddNone
                       | Zpos p1 ->
                         (match p1 with
                          | Coq_xH ->
                            if eq_op wsize_eqType (Obj.magic w0)
                                 (Obj.magic sz)
                            then AddInc a
                            else AddNone
                          | _ -> AddNone)
                       | Zneg p1 ->
                         (match p1 with
                          | Coq_xH ->
                            if eq_op wsize_eqType (Obj.magic w0)
                                 (Obj.magic sz)
                            then AddDec a
                            else AddNone
                          | _ -> AddNone))
                    | _ -> AddNone)
                 | _ -> AddNone)
              | _ -> AddNone)
           | Zpos p0 ->
             (match p0 with
              | Coq_xH ->
                if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                then AddInc b
                else AddNone
              | _ ->
                (match b with
                 | Papp1 (s0, p2) ->
                   (match s0 with
                    | Oword_of_int w0 ->
                      (match p2 with
                       | Pconst z0 ->
                         (match z0 with
                          | Z0 -> AddNone
                          | Zpos p3 ->
                            (match p3 with
                             | Coq_xH ->
                               if eq_op wsize_eqType (Obj.magic w0)
                                    (Obj.magic sz)
                               then AddInc a
                               else AddNone
                             | _ -> AddNone)
                          | Zneg p3 ->
                            (match p3 with
                             | Coq_xH ->
                               if eq_op wsize_eqType (Obj.magic w0)
                                    (Obj.magic sz)
                               then AddDec a
                               else AddNone
                             | _ -> AddNone))
                       | _ -> AddNone)
                    | _ -> AddNone)
                 | _ -> AddNone))
           | Zneg p0 ->
             (match p0 with
              | Coq_xH ->
                (match b with
                 | Papp1 (s0, p1) ->
                   (match s0 with
                    | Oword_of_int w0 ->
                      (match p1 with
                       | Pconst z0 ->
                         (match z0 with
                          | Zpos p2 ->
                            (match p2 with
                             | Coq_xH ->
                               if eq_op wsize_eqType (Obj.magic w0)
                                    (Obj.magic sz)
                               then AddInc a
                               else AddNone
                             | _ ->
                               if eq_op wsize_eqType (Obj.magic w)
                                    (Obj.magic sz)
                               then AddDec b
                               else AddNone)
                          | _ ->
                            if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                            then AddDec b
                            else AddNone)
                       | _ ->
                         if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                         then AddDec b
                         else AddNone)
                    | _ ->
                      if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                      then AddDec b
                      else AddNone)
                 | _ ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddDec b
                   else AddNone)
              | _ ->
                (match b with
                 | Papp1 (s0, p2) ->
                   (match s0 with
                    | Oword_of_int w0 ->
                      (match p2 with
                       | Pconst z0 ->
                         (match z0 with
                          | Z0 -> AddNone
                          | Zpos p3 ->
                            (match p3 with
                             | Coq_xH ->
                               if eq_op wsize_eqType (Obj.magic w0)
                                    (Obj.magic sz)
                               then AddInc a
                               else AddNone
                             | _ -> AddNone)
                          | Zneg p3 ->
                            (match p3 with
                             | Coq_xH ->
                               if eq_op wsize_eqType (Obj.magic w0)
                                    (Obj.magic sz)
                               then AddDec a
                               else AddNone
                             | _ -> AddNone))
                       | _ -> AddNone)
                    | _ -> AddNone)
                 | _ -> AddNone)))
        | Pbool _ ->
          (match b with
           | Papp1 (s0, p0) ->
             (match s0 with
              | Oword_of_int w0 ->
                (match p0 with
                 | Pconst z ->
                   (match z with
                    | Z0 -> AddNone
                    | Zpos p1 ->
                      (match p1 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddInc a
                         else AddNone
                       | _ -> AddNone)
                    | Zneg p1 ->
                      (match p1 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddDec a
                         else AddNone
                       | _ -> AddNone))
                 | _ -> AddNone)
              | _ -> AddNone)
           | _ -> AddNone)
        | Pvar _ ->
          (match b with
           | Papp1 (s0, p0) ->
             (match s0 with
              | Oword_of_int w0 ->
                (match p0 with
                 | Pconst z ->
                   (match z with
                    | Z0 -> AddNone
                    | Zpos p1 ->
                      (match p1 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddInc a
                         else AddNone
                       | _ -> AddNone)
                    | Zneg p1 ->
                      (match p1 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddDec a
                         else AddNone
                       | _ -> AddNone))
                 | _ -> AddNone)
              | _ -> AddNone)
           | _ -> AddNone)
        | Psub (_, _, _, _, _) ->
          (match b with
           | Papp1 (s0, p2) ->
             (match s0 with
              | Oword_of_int w0 ->
                (match p2 with
                 | Pconst z ->
                   (match z with
                    | Z0 -> AddNone
                    | Zpos p3 ->
                      (match p3 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddInc a
                         else AddNone
                       | _ -> AddNone)
                    | Zneg p3 ->
                      (match p3 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddDec a
                         else AddNone
                       | _ -> AddNone))
                 | _ -> AddNone)
              | _ -> AddNone)
           | _ -> AddNone)
        | Papp1 (_, _) ->
          (match b with
           | Papp1 (s1, p1) ->
             (match s1 with
              | Oword_of_int w0 ->
                (match p1 with
                 | Pconst z ->
                   (match z with
                    | Z0 -> AddNone
                    | Zpos p2 ->
                      (match p2 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddInc a
                         else AddNone
                       | _ -> AddNone)
                    | Zneg p2 ->
                      (match p2 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddDec a
                         else AddNone
                       | _ -> AddNone))
                 | _ -> AddNone)
              | _ -> AddNone)
           | _ -> AddNone)
        | Papp2 (_, _, _) ->
          (match b with
           | Papp1 (s1, p2) ->
             (match s1 with
              | Oword_of_int w0 ->
                (match p2 with
                 | Pconst z ->
                   (match z with
                    | Z0 -> AddNone
                    | Zpos p3 ->
                      (match p3 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddInc a
                         else AddNone
                       | _ -> AddNone)
                    | Zneg p3 ->
                      (match p3 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddDec a
                         else AddNone
                       | _ -> AddNone))
                 | _ -> AddNone)
              | _ -> AddNone)
           | _ -> AddNone)
        | PappN (_, _) ->
          (match b with
           | Papp1 (s0, p0) ->
             (match s0 with
              | Oword_of_int w0 ->
                (match p0 with
                 | Pconst z ->
                   (match z with
                    | Z0 -> AddNone
                    | Zpos p1 ->
                      (match p1 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddInc a
                         else AddNone
                       | _ -> AddNone)
                    | Zneg p1 ->
                      (match p1 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddDec a
                         else AddNone
                       | _ -> AddNone))
                 | _ -> AddNone)
              | _ -> AddNone)
           | _ -> AddNone)
        | Pif (_, _, _, _) ->
          (match b with
           | Papp1 (s1, p3) ->
             (match s1 with
              | Oword_of_int w0 ->
                (match p3 with
                 | Pconst z ->
                   (match z with
                    | Z0 -> AddNone
                    | Zpos p4 ->
                      (match p4 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddInc a
                         else AddNone
                       | _ -> AddNone)
                    | Zneg p4 ->
                      (match p4 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddDec a
                         else AddNone
                       | _ -> AddNone))
                 | _ -> AddNone)
              | _ -> AddNone)
           | _ -> AddNone)
        | _ ->
          (match b with
           | Papp1 (s0, p1) ->
             (match s0 with
              | Oword_of_int w0 ->
                (match p1 with
                 | Pconst z ->
                   (match z with
                    | Z0 -> AddNone
                    | Zpos p2 ->
                      (match p2 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddInc a
                         else AddNone
                       | _ -> AddNone)
                    | Zneg p2 ->
                      (match p2 with
                       | Coq_xH ->
                         if eq_op wsize_eqType (Obj.magic w0) (Obj.magic sz)
                         then AddDec a
                         else AddNone
                       | _ -> AddNone))
                 | _ -> AddNone)
              | _ -> AddNone)
           | _ -> AddNone))
     | _ ->
       (match b with
        | Papp1 (s0, p0) ->
          (match s0 with
           | Oword_of_int w ->
             (match p0 with
              | Pconst z ->
                (match z with
                 | Z0 -> AddNone
                 | Zpos p1 ->
                   (match p1 with
                    | Coq_xH ->
                      if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                      then AddInc a
                      else AddNone
                    | _ -> AddNone)
                 | Zneg p1 ->
                   (match p1 with
                    | Coq_xH ->
                      if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                      then AddDec a
                      else AddNone
                    | _ -> AddNone))
              | _ -> AddNone)
           | _ -> AddNone)
        | _ -> AddNone))
  | Papp2 (_, _, _) ->
    (match b with
     | Papp1 (s0, p1) ->
       (match s0 with
        | Oword_of_int w ->
          (match p1 with
           | Pconst z ->
             (match z with
              | Z0 -> AddNone
              | Zpos p2 ->
                (match p2 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddInc a
                   else AddNone
                 | _ -> AddNone)
              | Zneg p2 ->
                (match p2 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddDec a
                   else AddNone
                 | _ -> AddNone))
           | _ -> AddNone)
        | _ -> AddNone)
     | _ -> AddNone)
  | PappN (_, _) ->
    (match b with
     | Papp1 (s, p) ->
       (match s with
        | Oword_of_int w ->
          (match p with
           | Pconst z ->
             (match z with
              | Z0 -> AddNone
              | Zpos p0 ->
                (match p0 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddInc a
                   else AddNone
                 | _ -> AddNone)
              | Zneg p0 ->
                (match p0 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddDec a
                   else AddNone
                 | _ -> AddNone))
           | _ -> AddNone)
        | _ -> AddNone)
     | _ -> AddNone)
  | Pif (_, _, _, _) ->
    (match b with
     | Papp1 (s0, p2) ->
       (match s0 with
        | Oword_of_int w ->
          (match p2 with
           | Pconst z ->
             (match z with
              | Z0 -> AddNone
              | Zpos p3 ->
                (match p3 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddInc a
                   else AddNone
                 | _ -> AddNone)
              | Zneg p3 ->
                (match p3 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddDec a
                   else AddNone
                 | _ -> AddNone))
           | _ -> AddNone)
        | _ -> AddNone)
     | _ -> AddNone)
  | _ ->
    (match b with
     | Papp1 (s, p0) ->
       (match s with
        | Oword_of_int w ->
          (match p0 with
           | Pconst z ->
             (match z with
              | Z0 -> AddNone
              | Zpos p1 ->
                (match p1 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddInc a
                   else AddNone
                 | _ -> AddNone)
              | Zneg p1 ->
                (match p1 with
                 | Coq_xH ->
                   if eq_op wsize_eqType (Obj.magic w) (Obj.magic sz)
                   then AddDec a
                   else AddNone
                 | _ -> AddNone))
           | _ -> AddNone)
        | _ -> AddNone)
     | _ -> AddNone)

type sub_inc_dec =
| SubInc
| SubDec
| SubNone

(** val sub_inc_dec_classify : Equality.sort -> pexpr -> sub_inc_dec **)

let sub_inc_dec_classify sz = function
| Papp1 (s, p) ->
  (match s with
   | Oword_of_int w ->
     (match p with
      | Pconst z ->
        (match z with
         | Z0 -> SubNone
         | Zpos p0 ->
           (match p0 with
            | Coq_xH ->
              if eq_op wsize_eqType (Obj.magic w) sz then SubDec else SubNone
            | _ -> SubNone)
         | Zneg p0 ->
           (match p0 with
            | Coq_xH ->
              if eq_op wsize_eqType (Obj.magic w) sz then SubInc else SubNone
            | _ -> SubNone))
      | _ -> SubNone)
   | _ -> SubNone)
| _ -> SubNone

type divmod_pos =
| DM_Fst
| DM_Snd

type lower_cassgn_t =
| LowerMov of bool
| LowerCopn of (register, register_ext, xmm_register, rflag, condt, x86_op,
               x86_extra_op) extended_op sopn * pexpr list
| LowerInc of (register, register_ext, xmm_register, rflag, condt, x86_op,
              x86_extra_op) extended_op sopn * pexpr
| LowerLea of wsize * lea
| LowerFopn of wsize
   * (register, register_ext, xmm_register, rflag, condt, x86_op,
     x86_extra_op) extended_op sopn * pexpr list * wsize option
| LowerDiscardFlags of nat
   * (register, register_ext, xmm_register, rflag, condt, x86_op,
     x86_extra_op) extended_op sopn * pexpr list
| LowerCond
| LowerIf of stype * pexpr * pexpr * pexpr
| LowerDivMod of divmod_pos * signedness * wsize
   * (register, register_ext, xmm_register, rflag, condt, x86_op,
     x86_extra_op) extended_op sopn * pexpr * pexpr
| LowerConcat of pexpr * pexpr
| LowerAssgn

(** val is_lea : wsize -> lval -> pexpr -> lea option **)

let is_lea sz x e =
  match oassert
          ((&&) (cmp_le wsize_cmp U16 sz)
            ((&&) (cmp_le wsize_cmp sz U64) (negb (is_lval_in_memory x)))) with
  | Some _ ->
    (match mk_lea sz e with
     | Some l ->
       let { lea_disp = d; lea_base = b; lea_scale = sc; lea_offset = o } = l
       in
       let check = fun o0 ->
         match o0 with
         | Some x0 -> negb (is_var_in_memory x0.v_var)
         | None -> true
       in
       (match oassert ((&&) (check_scale sc) ((&&) (check b) (check o))) with
        | Some _ ->
          Some { lea_disp = d; lea_base = b; lea_scale = sc; lea_offset = o }
        | None -> None)
     | None -> None)
  | None -> None

(** val is_lnot : pexpr -> pexpr option **)

let is_lnot = function
| Papp1 (s, a0) -> (match s with
                    | Olnot _ -> Some a0
                    | _ -> None)
| _ -> None

(** val is_andn : pexpr -> pexpr -> (pexpr * pexpr) option **)

let is_andn a b =
  match is_lnot a with
  | Some a0 -> Some (a0, b)
  | None -> (match is_lnot b with
             | Some b0 -> Some (b0, a)
             | None -> None)

(** val mulr : wsize -> pexpr -> pexpr -> x86_op * pexpr list **)

let mulr sz a b =
  match is_wconst sz a with
  | Some _ -> ((IMULri sz), (b :: (a :: [])))
  | None ->
    (match is_wconst sz b with
     | Some _ -> ((IMULri sz), (a :: (b :: [])))
     | None -> ((IMULr sz), (a :: (b :: []))))

(** val check_shift_amount : wsize -> pexpr -> pexpr option **)

let check_shift_amount sz e =
  match is_wconst U8 e with
  | Some n ->
    if eq_op (GRing.ComRing.eqType (word U8)) n
         (wand U8 n (x86_shift_mask sz))
    then Some e
    else None
  | None ->
    (match e with
     | Papp2 (s, a, b) ->
       (match s with
        | Oland _ ->
          (match is_wconst U8 b with
           | Some n ->
             if eq_op (GRing.ComRing.eqType (word U8)) n (x86_shift_mask sz)
             then Some a
             else None
           | None -> None)
        | _ -> None)
     | _ -> None)

(** val check_signed_range : wsize option -> wsize -> coq_Z -> bool **)

let check_signed_range m sz' n =
  match m with
  | Some ws ->
    let z = wsigned sz' (wrepr sz' n) in
    let h = wmin_signed ws in if Z.leb h z then Z.ltb z (Z.opp h) else false
  | None -> false

(** val lower_cassgn_classify :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    Equality.sort -> pexpr -> lval -> lower_cassgn_t **)

let lower_cassgn_classify atoI ty e x =
  let chk = fun b r -> if b then r else LowerAssgn in
  let kb = fun b sz ->
    chk ((&&) b (eq_op stype_eqType (Obj.magic (Coq_sword sz)) ty))
  in
  let k8 = fun sz -> kb (cmp_le wsize_cmp sz U64) sz in
  let k16 = fun sz ->
    kb ((&&) (cmp_le wsize_cmp U16 sz) (cmp_le wsize_cmp sz U64)) sz
  in
  let k32 = fun sz ->
    kb ((&&) (cmp_le wsize_cmp U32 sz) (cmp_le wsize_cmp sz U64)) sz
  in
  (match e with
   | Pvar g ->
     let { gv = v; gs = _ } = g in
     let { v_var = v_var0; v_info = _ } = v in
     let { Var.vtype = vtype0; Var.vname = _ } = v_var0 in
     (match vtype0 with
      | Coq_sword sz ->
        if cmp_le wsize_cmp sz U64
        then LowerMov
               (if is_var_in_memory v.v_var
                then is_lval_in_memory x
                else false)
        else (match Obj.magic ty with
              | Coq_sword szo ->
                if cmp_le wsize_cmp U128 szo
                then LowerCopn ((coq_Ox86 atoI (VMOVDQU szo)), (e :: []))
                else if cmp_le wsize_cmp U32 szo
                     then LowerCopn ((coq_Ox86 atoI (MOVV szo)), (e :: []))
                     else LowerAssgn
              | _ -> LowerAssgn)
      | _ -> LowerAssgn)
   | Pget (_, sz, g, _) ->
     let { gv = v; gs = _ } = g in
     if cmp_le wsize_cmp sz U64
     then LowerMov
            (if is_var_in_memory v.v_var then is_lval_in_memory x else false)
     else (match Obj.magic ty with
           | Coq_sword szo ->
             if cmp_le wsize_cmp U128 szo
             then LowerCopn ((coq_Ox86 atoI (VMOVDQU szo)), (e :: []))
             else if cmp_le wsize_cmp U32 szo
                  then LowerCopn ((coq_Ox86 atoI (MOVV szo)), (e :: []))
                  else LowerAssgn
           | _ -> LowerAssgn)
   | Pload (sz, _, _) ->
     if cmp_le wsize_cmp sz U64
     then LowerMov (is_lval_in_memory x)
     else kb true sz (LowerCopn ((coq_Ox86 atoI (VMOVDQU sz)), (e :: [])))
   | Papp1 (s, a) ->
     (match s with
      | Oword_of_int sz ->
        (match a with
         | Pconst z ->
           (match Obj.magic ty with
            | Coq_sword sz' ->
              chk (cmp_le wsize_cmp sz' U64) (LowerMov
                (negb
                  (check_signed_range (Some (cmp_min wsize_cmp U32 sz')) sz z)))
            | _ -> LowerAssgn)
         | _ -> LowerAssgn)
      | Osignext (szo, szi) ->
        (match szi with
         | U8 ->
           k16 szo (LowerCopn ((coq_Ox86 atoI (MOVSX (szo, szi))), (a :: [])))
         | U16 ->
           k16 szo (LowerCopn ((coq_Ox86 atoI (MOVSX (szo, szi))), (a :: [])))
         | U32 ->
           k32 szo (LowerCopn ((coq_Ox86 atoI (MOVSX (szo, szi))), (a :: [])))
         | _ ->
           chk false (LowerCopn ((coq_Ox86 atoI (MOVSX (szo, szi))),
             (a :: []))))
      | Ozeroext (szo, szi) ->
        (match szi with
         | U8 ->
           k16 szo (LowerCopn ((coq_Ox86 atoI (MOVZX (szo, szi))), (a :: [])))
         | U16 ->
           k32 szo (LowerCopn ((coq_Ox86 atoI (MOVZX (szo, szi))), (a :: [])))
         | U32 ->
           (match szo with
            | U64 ->
              kb true szo (LowerCopn ((Oasm (ExtOp Ox86MOVZX32)), (a :: [])))
            | U128 ->
              kb true szo (LowerCopn ((coq_Ox86 atoI (MOVD szi)), (a :: [])))
            | U256 ->
              kb true szo (LowerCopn ((Oasm (BaseOp ((Some szo), (VMOV
                szi)))), (a :: [])))
            | _ -> LowerAssgn)
         | U64 ->
           (match szo with
            | U128 ->
              kb true szo (LowerCopn ((coq_Ox86 atoI (MOVD szi)), (a :: [])))
            | U256 ->
              kb true szo (LowerCopn ((Oasm (BaseOp ((Some szo), (VMOV
                szi)))), (a :: [])))
            | _ -> LowerAssgn)
         | _ -> LowerAssgn)
      | Olnot sz -> k8 sz (LowerCopn ((coq_Ox86 atoI (NOT sz)), (a :: [])))
      | Oneg o ->
        (match o with
         | Op_int -> LowerAssgn
         | Op_w sz ->
           k8 sz (LowerFopn (sz, (coq_Ox86 atoI (NEG sz)), (a :: []), None)))
      | _ -> LowerAssgn)
   | Papp2 (op, a, b) ->
     (match op with
      | Obeq -> LowerAssgn
      | Oand -> LowerAssgn
      | Oor -> LowerAssgn
      | Oadd o ->
        (match o with
         | Op_int -> LowerAssgn
         | Op_w sz ->
           k8 sz
             (match is_lea sz x e with
              | Some l -> LowerLea (sz, l)
              | None ->
                (match add_inc_dec_classify sz a b with
                 | AddInc y -> LowerInc ((coq_Ox86 atoI (INC sz)), y)
                 | AddDec y -> LowerInc ((coq_Ox86 atoI (DEC sz)), y)
                 | AddNone ->
                   LowerFopn (sz, (coq_Ox86 atoI (ADD sz)), (a :: (b :: [])),
                     (Some U32)))))
      | Omul o ->
        (match o with
         | Op_int -> LowerAssgn
         | Op_w sz ->
           k16 sz
             (match is_lea sz x e with
              | Some l -> LowerLea (sz, l)
              | None ->
                let (op0, args) = mulr sz a b in
                LowerFopn (sz, (coq_Ox86 atoI op0), args, (Some U32))))
      | Osub o ->
        (match o with
         | Op_int -> LowerAssgn
         | Op_w sz ->
           k8 sz
             (match is_lea sz x e with
              | Some l -> LowerLea (sz, l)
              | None ->
                (match sub_inc_dec_classify (Obj.magic sz) b with
                 | SubInc -> LowerInc ((coq_Ox86 atoI (INC sz)), a)
                 | SubDec -> LowerInc ((coq_Ox86 atoI (DEC sz)), a)
                 | SubNone ->
                   LowerFopn (sz, (coq_Ox86 atoI (SUB sz)), (a :: (b :: [])),
                     (Some U32)))))
      | Odiv c ->
        (match c with
         | Cmp_int -> LowerAssgn
         | Cmp_w (u, sz) ->
           let opn =
             match u with
             | Signed -> coq_Ox86 atoI (IDIV sz)
             | Unsigned -> coq_Ox86 atoI (DIV sz)
           in
           k16 sz (LowerDivMod (DM_Fst, u, sz, opn, a, b)))
      | Omod c ->
        (match c with
         | Cmp_int -> LowerAssgn
         | Cmp_w (u, sz) ->
           let opn =
             match u with
             | Signed -> coq_Ox86 atoI (IDIV sz)
             | Unsigned -> coq_Ox86 atoI (DIV sz)
           in
           k16 sz (LowerDivMod (DM_Snd, u, sz, opn, a, b)))
      | Oland sz ->
        (match is_andn a b with
         | Some p ->
           let (a0, b0) = p in
           if cmp_le wsize_cmp sz U64
           then k32 sz (LowerFopn (sz, (coq_Ox86 atoI (ANDN sz)),
                  (a0 :: (b0 :: [])), None))
           else kb true sz (LowerCopn ((coq_Ox86 atoI (VPANDN sz)),
                  (a0 :: (b0 :: []))))
         | None ->
           if cmp_le wsize_cmp sz U64
           then k8 sz (LowerFopn (sz, (coq_Ox86 atoI (AND sz)),
                  (a :: (b :: [])), (Some U32)))
           else kb true sz (LowerCopn ((coq_Ox86 atoI (VPAND sz)),
                  (a :: (b :: [])))))
      | Olor sz ->
        if cmp_le wsize_cmp sz U64
        then k8 sz (LowerFopn (sz, (coq_Ox86 atoI (OR sz)), (a :: (b :: [])),
               (Some U32)))
        else kb true sz (LowerCopn ((coq_Ox86 atoI (VPOR sz)),
               (a :: (b :: []))))
      | Olxor sz ->
        if cmp_le wsize_cmp sz U64
        then k8 sz (LowerFopn (sz, (coq_Ox86 atoI (XOR sz)),
               (a :: (b :: [])), (Some U32)))
        else kb true sz (LowerCopn ((coq_Ox86 atoI (VPXOR sz)),
               (a :: (b :: []))))
      | Olsr sz ->
        (match check_shift_amount sz b with
         | Some b0 ->
           k8 sz (LowerFopn (sz, (coq_Ox86 atoI (SHR sz)), (a :: (b0 :: [])),
             (Some U8)))
         | None -> LowerAssgn)
      | Olsl o ->
        (match o with
         | Op_int -> LowerAssgn
         | Op_w sz ->
           (match check_shift_amount sz b with
            | Some b0 ->
              k8 sz (LowerFopn (sz, (coq_Ox86 atoI (SHL sz)),
                (a :: (b0 :: [])), (Some U8)))
            | None -> LowerAssgn))
      | Oasr o ->
        (match o with
         | Op_int -> LowerAssgn
         | Op_w sz ->
           (match check_shift_amount sz b with
            | Some b0 ->
              k8 sz (LowerFopn (sz, (coq_Ox86 atoI (SAR sz)),
                (a :: (b0 :: [])), (Some U8)))
            | None -> LowerAssgn))
      | Oror sz ->
        (match check_shift_amount sz b with
         | Some b0 ->
           k8 sz (LowerDiscardFlags ((S (S O)), (coq_Ox86 atoI (ROR sz)),
             (a :: (b0 :: []))))
         | None -> LowerAssgn)
      | Orol sz ->
        (match check_shift_amount sz b with
         | Some b0 ->
           k8 sz (LowerDiscardFlags ((S (S O)), (coq_Ox86 atoI (ROL sz)),
             (a :: (b0 :: []))))
         | None -> LowerAssgn)
      | Ovadd (ve, sz) ->
        kb (cmp_le wsize_cmp U128 sz) sz (LowerCopn
          ((coq_Ox86 atoI (VPADD (ve, sz))), (a :: (b :: []))))
      | Ovsub (ve, sz) ->
        kb (cmp_le wsize_cmp U128 sz) sz (LowerCopn
          ((coq_Ox86 atoI (VPSUB (ve, sz))), (a :: (b :: []))))
      | Ovmul (ve, sz) ->
        kb
          ((&&)
            ((&&) (cmp_le wsize_cmp U16 (wsize_of_velem ve))
              (cmp_le wsize_cmp (wsize_of_velem ve) U32))
            (cmp_le wsize_cmp U128 sz)) sz (LowerCopn
          ((coq_Ox86 atoI (VPMULL (ve, sz))), (a :: (b :: []))))
      | Ovlsr (ve, sz) ->
        kb
          ((&&) (cmp_le wsize_cmp U16 (wsize_of_velem ve))
            (cmp_le wsize_cmp U128 sz)) sz (LowerCopn
          ((coq_Ox86 atoI (VPSRL (ve, sz))), (a :: (b :: []))))
      | Ovlsl (ve, sz) ->
        kb
          ((&&) (cmp_le wsize_cmp U16 (wsize_of_velem ve))
            (cmp_le wsize_cmp U128 sz)) sz (LowerCopn
          ((coq_Ox86 atoI (VPSLL (ve, sz))), (a :: (b :: []))))
      | Ovasr (ve, sz) ->
        kb
          ((&&) (cmp_le wsize_cmp U16 (wsize_of_velem ve))
            (cmp_le wsize_cmp U128 sz)) sz (LowerCopn
          ((coq_Ox86 atoI (VPSRA (ve, sz))), (a :: (b :: []))))
      | _ -> LowerCond)
   | PappN (o, l0) ->
     (match o with
      | Opack (w, p) ->
        (match w with
         | U256 ->
           (match p with
            | PE128 ->
              (match l0 with
               | [] -> LowerAssgn
               | p0 :: l1 ->
                 (match p0 with
                  | Papp1 (s, h) ->
                    (match s with
                     | Oint_of_word w0 ->
                       (match w0 with
                        | U128 ->
                          (match l1 with
                           | [] -> LowerAssgn
                           | p1 :: l2 ->
                             (match p1 with
                              | Papp1 (s0, l) ->
                                (match s0 with
                                 | Oint_of_word w1 ->
                                   (match w1 with
                                    | U128 ->
                                      (match l with
                                       | Pvar _ ->
                                         (match l2 with
                                          | [] ->
                                            if eq_op stype_eqType ty
                                                 (Obj.magic (Coq_sword U256))
                                            then LowerConcat (h, l)
                                            else LowerAssgn
                                          | _ :: _ -> LowerAssgn)
                                       | _ -> LowerAssgn)
                                    | _ -> LowerAssgn)
                                 | _ -> LowerAssgn)
                              | _ -> LowerAssgn))
                        | _ -> LowerAssgn)
                     | _ -> LowerAssgn)
                  | _ -> LowerAssgn))
            | _ -> LowerAssgn)
         | _ -> LowerAssgn)
      | Ocombine_flags _ -> LowerAssgn)
   | Pif (t0, e0, e1, e2) ->
     (match stype_of_lval x with
      | Coq_sword _ -> k16 (wsize_of_lval x) (LowerIf (t0, e0, e1, e2))
      | _ -> LowerAssgn)
   | _ -> LowerAssgn)

type opn_5flags_cases_t =
| Opn5f_large_immed of pexpr * pexpr * pexpr list
| Opn5f_other

(** val opn_5flags_cases :
    pexpr list -> wsize option -> wsize -> opn_5flags_cases_t **)

let opn_5flags_cases a m sz =
  match a with
  | [] -> Opn5f_other
  | x :: l ->
    (match l with
     | [] -> Opn5f_other
     | y :: z ->
       (match is_wconst_of_size (Obj.magic U64) y with
        | Some n ->
          if check_signed_range m sz n
          then Opn5f_other
          else Opn5f_large_immed (x, y, z)
        | None -> Opn5f_other))

(** val opn_no_imm :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op sopn -> (register, register_ext, xmm_register,
    rflag, condt, x86_op, x86_extra_op) extended_op sopn **)

let opn_no_imm _ op = match op with
| Oasm a ->
  (match a with
   | BaseOp a0 ->
     let (ws, y) = a0 in
     (match y with
      | IMULri sz -> Oasm (BaseOp (ws, (IMULr sz)))
      | _ -> op)
   | ExtOp _ -> op)
| _ -> op

(** val opn_5flags :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    fresh_vars -> wsize option -> wsize -> var_info -> lval -> lval ->
    assgn_tag -> (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op sopn -> pexpr list -> (register, register_ext,
    xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op instr_r list **)

let opn_5flags atoI fv =
  let fresh_word = fun sz ->
    vword sz
      (fv
        (Ident.Ident.name_of_string
          ('_'::('_'::('w'::('t'::('m'::('p'::('_'::('_'::[])))))))))
        (Coq_sword sz))
  in
  (fun immed_bound sopn_wsize vi cf x tg o a ->
  let f = coq_Lnone_b vi in
  let fopn = fun o0 a0 -> (Copn
    ((f :: (cf :: (f :: (f :: (f :: (x :: [])))))), tg, o0, a0)) :: []
  in
  (match opn_5flags_cases a immed_bound sopn_wsize with
   | Opn5f_large_immed (x0, y, z) ->
     let c = { v_var = (fresh_word U64); v_info = vi } in
     (Copn (((Lvar c) :: []), tg, (coq_Ox86 atoI (MOV U64)),
     (y :: []))) :: (fopn (opn_no_imm atoI o) (x0 :: ((coq_Plvar c) :: z)))
   | Opn5f_other -> fopn o a))

(** val reduce_wconst : wsize -> pexpr -> pexpr **)

let reduce_wconst sz e = match e with
| Papp1 (s, p) ->
  (match s with
   | Oword_of_int sz' ->
     (match p with
      | Pconst z ->
        Papp1 ((Oword_of_int (cmp_min wsize_cmp sz sz')), (Pconst z))
      | _ -> e)
   | _ -> e)
| _ -> e

(** val lower_cassgn :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    lowering_options -> (instr_info -> warning_msg -> instr_info) ->
    fresh_vars -> instr_info -> lval -> assgn_tag -> stype -> pexpr ->
    (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op instr list **)

let lower_cassgn atoI options warning fv =
  let fresh_word = fun sz ->
    vword sz
      (fv
        (Ident.Ident.name_of_string
          ('_'::('_'::('w'::('t'::('m'::('p'::('_'::('_'::[])))))))))
        (Coq_sword sz))
  in
  (fun ii x tg ty e ->
  let vi = var_info_of_lval x in
  let f = coq_Lnone_b vi in
  let copn = fun o a -> (MkI (ii, (Copn ((x :: []), tg, o, a)))) :: [] in
  let inc = fun o a -> (MkI (ii, (Copn
    ((f :: (f :: (f :: (f :: (x :: []))))), tg, o, (a :: []))))) :: []
  in
  (match lower_cassgn_classify atoI (Obj.magic ty) e x with
   | LowerMov b ->
     let szty = wsize_of_stype ty in
     let e0 = reduce_wconst szty e in
     if b
     then let c = { v_var = (fresh_word szty); v_info = vi } in
          (MkI (ii, (Copn (((Lvar c) :: []), tg, (coq_Ox86 atoI (MOV szty)),
          (e0 :: []))))) :: ((MkI (ii, (Copn ((x :: []), tg,
          (coq_Ox86 atoI (MOV szty)), ((coq_Plvar c) :: []))))) :: [])
     else if (&&)
               ((&&) (is_zero (Obj.magic szty) e0)
                 (negb (is_lval_in_memory x))) options.use_set0
          then if cmp_le wsize_cmp szty U64
               then (MkI (ii, (Copn
                      ((f :: (f :: (f :: (f :: (f :: (x :: [])))))), tg,
                      (Oasm (ExtOp (Oset0 szty))), [])))) :: []
               else (MkI (ii, (Copn ((x :: []), tg, (Oasm (ExtOp (Oset0
                      szty))), [])))) :: []
          else (MkI (ii, (mov_ws atoI szty x e0 tg))) :: []
   | LowerCopn (o, e0) -> copn o e0
   | LowerInc (o, e0) -> inc o e0
   | LowerLea (sz, l) ->
     let { lea_disp = d; lea_base = b; lea_scale = sc; lea_offset = o } = l in
     let de =
       wconst (coq_Uptr (arch_pd x86_decl))
         (wrepr (coq_Uptr (arch_pd x86_decl)) d)
     in
     let sce =
       wconst (coq_Uptr (arch_pd x86_decl))
         (wrepr (coq_Uptr (arch_pd x86_decl)) sc)
     in
     let b0 =
       Ssrfun.Option.apply coq_Plvar
         (wconst sz (GRing.zero (GRing.ComRing.zmodType (word sz)))) b
     in
     let o0 =
       Ssrfun.Option.apply coq_Plvar
         (wconst sz (GRing.zero (GRing.ComRing.zmodType (word sz)))) o
     in
     let lea0 = fun _ ->
       let ii0 = warning ii Use_lea in
       let add0 = fun x0 x1 -> Papp2 ((Oadd (Op_w sz)), x0, x1) in
       let mul = fun x0 x1 -> Papp2 ((Omul (Op_w sz)), x0, x1) in
       let e0 = add0 de (add0 b0 (mul sce o0)) in
       (MkI (ii0, (Copn ((x :: []), tg, (coq_Ox86 atoI (LEA sz)),
       (e0 :: []))))) :: []
     in
     if options.use_lea
     then lea0 ()
     else if eq_op coq_Z_eqType (Obj.magic d) (GRing.zero coq_Z_zmodType)
          then if eq_op coq_Z_eqType (Obj.magic sc) (GRing.one coq_Z_ringType)
               then (MkI (ii, (Copn
                      ((f :: (f :: (f :: (f :: (f :: (x :: [])))))), tg,
                      (coq_Ox86 atoI (ADD sz)), (b0 :: (o0 :: [])))))) :: []
               else if is_zero (Obj.magic sz) b0
                    then let (op, args) = mulr sz o0 sce in
                         map (fun x0 -> MkI (ii, x0))
                           (opn_5flags atoI fv (Some U32) sz vi f x tg
                             (coq_Ox86 atoI op) args)
                    else lea0 ()
          else if is_zero (Obj.magic sz) o0
               then if eq_op coq_Z_eqType (Obj.magic d)
                         (Obj.magic (Zpos Coq_xH))
                    then inc (coq_Ox86 atoI (INC sz)) b0
                    else if check_signed_range (Some U32) sz d
                         then (MkI (ii, (Copn
                                ((f :: (f :: (f :: (f :: (f :: (x :: [])))))),
                                tg, (coq_Ox86 atoI (ADD sz)),
                                (b0 :: (de :: [])))))) :: []
                         else if eq_op coq_Z_eqType (Obj.magic d)
                                   (Obj.magic Z.div (wbase U32) (Zpos (Coq_xO
                                     Coq_xH)))
                              then (MkI (ii, (Copn
                                     ((f :: (f :: (f :: (f :: (f :: (x :: [])))))),
                                     tg, (coq_Ox86 atoI (SUB sz)),
                                     (b0 :: ((wconst sz (wrepr sz (Z.opp d))) :: [])))))) :: []
                              else let c = { v_var = (fresh_word U64);
                                     v_info = vi }
                                   in
                                   (MkI (ii, (Copn (((Lvar c) :: []), tg,
                                   (coq_Ox86 atoI (MOV U64)),
                                   (de :: []))))) :: ((MkI (ii, (Copn
                                   ((f :: (f :: (f :: (f :: (f :: (x :: [])))))),
                                   tg, (coq_Ox86 atoI (ADD sz)),
                                   (b0 :: ((coq_Plvar c) :: [])))))) :: [])
               else lea0 ()
   | LowerFopn (sz, o, es, m) ->
     map (fun x0 -> MkI (ii, x0)) (opn_5flags atoI fv m sz vi f x tg o es)
   | LowerDiscardFlags (n, op, es) ->
     let lvs = nseq n (coq_Lnone_b vi) in
     (MkI (ii, (Copn ((cat lvs (x :: [])), tg, op, es)))) :: []
   | LowerCond ->
     let (i, e') = lower_condition atoI fv vi e in
     map (fun x0 -> MkI (ii, x0))
       (cat i ((Cassgn (x, AT_inline, ty, e')) :: []))
   | LowerIf (_, e0, e1, e2) ->
     let (l, e3) = lower_condition atoI fv vi e0 in
     let sz = wsize_of_lval x in
     map (fun x0 -> MkI (ii, x0))
       (cat l ((Copn ((x :: []), tg, (coq_Ox86 atoI (CMOVcc sz)),
         (e3 :: (e1 :: (e2 :: []))))) :: []))
   | LowerDivMod (p, s, sz, op, a, b) ->
     let c = { v_var = (fresh_word sz); v_info = vi } in
     let lv =
       match p with
       | DM_Fst ->
         f :: (f :: (f :: (f :: (f :: (x :: ((Lnone (vi, (Coq_sword
           sz))) :: []))))))
       | DM_Snd ->
         f :: (f :: (f :: (f :: (f :: ((Lnone (vi, (Coq_sword
           sz))) :: (x :: []))))))
     in
     let i1 =
       match s with
       | Signed ->
         Copn (((Lvar c) :: []), tg, (coq_Ox86 atoI (CQO sz)), (a :: []))
       | Unsigned ->
         Copn ((f :: (f :: (f :: (f :: (f :: ((Lvar c) :: [])))))), tg, (Oasm
           (ExtOp (Oset0 sz))), [])
     in
     (MkI (ii, i1)) :: ((MkI (ii, (Copn (lv, tg, op,
     ((coq_Plvar c) :: (a :: (b :: []))))))) :: [])
   | LowerConcat (h, l) ->
     (MkI (ii, (Copn ((x :: []), tg, (Oasm (ExtOp Oconcat128)),
       (h :: (l :: [])))))) :: []
   | LowerAssgn -> (MkI (ii, (Cassgn (x, tg, ty, e)))) :: []))

(** val lower_addcarry_classify :
    bool -> lval list -> pexpr list -> ((((var_info * (wsize ->
    x86_op)) * pexpr list) * lval) * lval) option **)

let lower_addcarry_classify sub xs es =
  match xs with
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
                 | p :: l3 ->
                   (match p with
                    | Pbool b ->
                      if b
                      then None
                      else (match l3 with
                            | [] ->
                              let vi = var_info_of_lval r in
                              Some ((((vi, (fun x0 ->
                              if sub then SUB x0 else ADD x0)),
                              (x :: (y :: []))), cf), r)
                            | _ :: _ -> None)
                    | Pvar g ->
                      let { gv = cfi; gs = gs0 } = g in
                      (match gs0 with
                       | Slocal ->
                         (match l3 with
                          | [] ->
                            let vi = cfi.v_info in
                            Some ((((vi, (fun x0 ->
                            if sub then SBB x0 else ADC x0)), es), cf), r)
                          | _ :: _ -> None)
                       | Sglob -> None)
                    | _ -> None))))
        | _ :: _ -> None))

(** val lower_addcarry :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    fresh_vars -> wsize -> bool -> lval list -> assgn_tag -> pexpr list ->
    (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op instr_r list **)

let lower_addcarry atoI fv sz sub xs tg es =
  let op =
    if sub
    then sopn_subcarry (asm_opI (x86_extra atoI))
    else sopn_addcarry (asm_opI (x86_extra atoI))
  in
  if cmp_le wsize_cmp sz U64
  then (match lower_addcarry_classify sub xs es with
        | Some p ->
          let (p0, r) = p in
          let (p1, cf) = p0 in
          let (p2, es0) = p1 in
          let (vi, o) = p2 in
          opn_5flags atoI fv (Some U32) sz vi cf r tg (coq_Ox86 atoI (o sz))
            es0
        | None -> (Copn (xs, tg, (op sz), es)) :: [])
  else (Copn (xs, tg, (op sz), es)) :: []

(** val lower_mulu :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    fresh_vars -> wsize -> lval list -> assgn_tag -> pexpr list -> (register,
    register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
    extended_op instr_r list **)

let lower_mulu atoI fv =
  let fresh_word = fun sz ->
    vword sz
      (fv
        (Ident.Ident.name_of_string
          ('_'::('_'::('w'::('t'::('m'::('p'::('_'::('_'::[])))))))))
        (Coq_sword sz))
  in
  (fun sz xs tg es ->
  match check_size_16_64 sz with
  | Ok _ ->
    (match xs with
     | [] ->
       (Copn (xs, tg, (sopn_mulu (asm_opI (x86_extra atoI)) sz), es)) :: []
     | r1 :: l ->
       (match l with
        | [] ->
          (Copn (xs, tg, (sopn_mulu (asm_opI (x86_extra atoI)) sz), es)) :: []
        | r2 :: l0 ->
          (match l0 with
           | [] ->
             (match es with
              | [] ->
                (Copn (xs, tg, (sopn_mulu (asm_opI (x86_extra atoI)) sz),
                  es)) :: []
              | x :: l1 ->
                (match l1 with
                 | [] ->
                   (Copn (xs, tg, (sopn_mulu (asm_opI (x86_extra atoI)) sz),
                     es)) :: []
                 | y :: l2 ->
                   (match l2 with
                    | [] ->
                      let vi = var_info_of_lval r2 in
                      let f = coq_Lnone_b vi in
                      (match is_wconst sz x with
                       | Some _ ->
                         let c = { v_var = (fresh_word sz); v_info = vi } in
                         (Copn (((Lvar c) :: []), tg,
                         (coq_Ox86 atoI (MOV sz)), (x :: []))) :: ((Copn
                         ((f :: (f :: (f :: (f :: (f :: (r1 :: (r2 :: []))))))),
                         tg, (coq_Ox86 atoI (MUL sz)),
                         (y :: ((coq_Plvar c) :: [])))) :: [])
                       | None ->
                         (match is_wconst sz y with
                          | Some _ ->
                            let c = { v_var = (fresh_word sz); v_info = vi }
                            in
                            (Copn (((Lvar c) :: []), tg,
                            (coq_Ox86 atoI (MOV sz)), (y :: []))) :: ((Copn
                            ((f :: (f :: (f :: (f :: (f :: (r1 :: (r2 :: []))))))),
                            tg, (coq_Ox86 atoI (MUL sz)),
                            (x :: ((coq_Plvar c) :: [])))) :: [])
                          | None ->
                            (Copn
                              ((f :: (f :: (f :: (f :: (f :: (r1 :: (r2 :: []))))))),
                              tg, (coq_Ox86 atoI (MUL sz)), es)) :: []))
                    | _ :: _ ->
                      (Copn (xs, tg,
                        (sopn_mulu (asm_opI (x86_extra atoI)) sz), es)) :: [])))
           | _ :: _ ->
             (Copn (xs, tg, (sopn_mulu (asm_opI (x86_extra atoI)) sz),
               es)) :: [])))
  | Error _ ->
    (Copn (xs, tg, (sopn_mulu (asm_opI (x86_extra atoI)) sz), es)) :: [])

(** val lower_swap :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    stype -> lval list -> assgn_tag -> pexpr list -> (register, register_ext,
    xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op instr_r list **)

let lower_swap atoI ty xs tg es =
  match is_word_type ty with
  | Some sz ->
    if cmp_le wsize_cmp sz U64
    then (Copn (xs, tg, (coq_Ox86 atoI (XCHG sz)), es)) :: []
    else (Copn (xs, tg, (Opseudo_op (Oswap ty)), es)) :: []
  | None -> (Copn (xs, tg, (Opseudo_op (Oswap ty)), es)) :: []

(** val lower_pseudo_operator :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    fresh_vars -> lval list -> assgn_tag -> pseudo_operator -> pexpr list ->
    (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op instr_r list **)

let lower_pseudo_operator atoI fv xs tg op es =
  match op with
  | Omulu sz -> lower_mulu atoI fv sz xs tg es
  | Oaddcarry sz -> lower_addcarry atoI fv sz false xs tg es
  | Osubcarry sz -> lower_addcarry atoI fv sz true xs tg es
  | Oswap ty -> lower_swap atoI ty xs tg es
  | _ -> (Copn (xs, tg, (Opseudo_op op), es)) :: []

(** val lower_copn :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    fresh_vars -> lval list -> assgn_tag -> (register, register_ext,
    xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op sopn ->
    pexpr list -> (register, register_ext, xmm_register, rflag, condt,
    x86_op, x86_extra_op) extended_op instr_r list **)

let lower_copn atoI fv xs tg op es =
  match op with
  | Opseudo_op pop -> lower_pseudo_operator atoI fv xs tg pop es
  | _ -> (Copn (xs, tg, op, es)) :: []

(** val lower_i :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    lowering_options -> (instr_info -> warning_msg -> instr_info) ->
    fresh_vars -> (register, register_ext, xmm_register, rflag, condt,
    x86_op, x86_extra_op) extended_op instr -> (register, register_ext,
    xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op instr list **)

let rec lower_i atoI options warning fv = function
| MkI (ii, ir) ->
  (match ir with
   | Cassgn (l, tg, ty, e) ->
     lower_cassgn atoI options warning fv ii l tg ty e
   | Copn (l, t0, o, e) ->
     map (fun x -> MkI (ii, x)) (lower_copn atoI fv l t0 o e)
   | Csyscall (_, _, _) -> map (fun x -> MkI (ii, x)) (ir :: [])
   | Cif (e, c1, c2) ->
     let (pre, e0) = lower_condition atoI fv dummy_var_info e in
     map (fun x -> MkI (ii, x))
       (rcons pre (Cif (e0, (conc_map (lower_i atoI options warning fv) c1),
         (conc_map (lower_i atoI options warning fv) c2))))
   | Cfor (v, r, c) ->
     (MkI (ii, (Cfor (v, r,
       (conc_map (lower_i atoI options warning fv) c))))) :: []
   | Cwhile (a, c, e, c') ->
     let (pre, e0) = lower_condition atoI fv dummy_var_info e in
     map (fun x -> MkI (ii, x)) ((Cwhile (a,
       (cat (conc_map (lower_i atoI options warning fv) c)
         (map (fun x -> MkI (dummy_instr_info, x)) pre)), e0,
       (conc_map (lower_i atoI options warning fv) c'))) :: [])
   | Ccall (_, _, _) -> map (fun x -> MkI (ii, x)) (ir :: []))
