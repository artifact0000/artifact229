open Datatypes
open Compiler_util
open Eqtype
open Expr
open Pseudo_operator
open Seq
open Sopn
open Type
open Utils0
open Var0
open Wsize

module E =
 struct
  (** val pass : char list **)

  let pass =
    'l'::('o'::('w'::('e'::('r'::(' '::('s'::('p'::('i'::('l'::('l'::('i'::('n'::('g'::(' '::('i'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('i'::('o'::('n'::('s'::[]))))))))))))))))))))))))))

  (** val ii_loop_iterator : instr_info -> pp_error_loc **)

  let ii_loop_iterator =
    ii_loop_iterator pass

  (** val error : instr_info -> pp_error -> pp_error_loc **)

  let error ii pp =
    { pel_msg = pp; pel_fn = None; pel_fi = None; pel_ii = (Some ii);
      pel_vi = None; pel_pass = (Some pass); pel_internal = false }
 end

(** val is_spill_op :
    'a1 asmOp -> 'a1 sopn -> (spill_op * stype list) option **)

let is_spill_op _ = function
| Opseudo_op p ->
  (match p with
   | Ospill (o0, tys) -> Some (o0, tys)
   | _ -> None)
| _ -> None

(** val to_spill_e : SvExtra.Sv.t -> pexpr -> SvExtra.Sv.t **)

let to_spill_e s = function
| Pvar x -> SvExtra.Sv.add (Obj.magic x.gv.v_var) s
| _ -> s

(** val to_spill_i :
    'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr -> SvExtra.Sv.t **)

let rec to_spill_i asmop s = function
| MkI (_, ir) ->
  (match ir with
   | Copn (_, _, o, es) ->
     (match is_spill_op asmop o with
      | Some p ->
        let (s0, _) = p in
        (match s0 with
         | Spill -> foldl to_spill_e s es
         | Unspill -> s)
      | None -> s)
   | Cif (_, c1, c2) ->
     foldl (to_spill_i asmop) (foldl (to_spill_i asmop) s c1) c2
   | Cfor (_, _, c) -> foldl (to_spill_i asmop) s c
   | Cwhile (_, c1, _, c2) ->
     foldl (to_spill_i asmop) (foldl (to_spill_i asmop) s c1) c2
   | _ -> s)

type spill_env = SvExtra.Sv.t

(** val update_lv : spill_env -> lval -> spill_env **)

let update_lv env = function
| Lvar x -> SvExtra.Sv.remove (Obj.magic x.v_var) env
| Laset (_, _, x, _) -> SvExtra.Sv.remove (Obj.magic x.v_var) env
| Lasub (_, _, _, x, _) -> SvExtra.Sv.remove (Obj.magic x.v_var) env
| _ -> env

(** val update_lvs : spill_env -> lval list -> spill_env **)

let update_lvs =
  foldl update_lv

(** val get_Pvar : instr_info -> pexpr -> var_i cexec **)

let get_Pvar ii e = match e with
| Pvar g ->
  let { gv = x; gs = gs0 } = g in
  (match gs0 with
   | Slocal -> Ok x
   | Sglob ->
     Error
       (E.error ii
         (pp_hov ((PPEexpr e) :: ((PPEstring
           ('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('a'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))) :: [])))))
| _ ->
  Error
    (E.error ii
      (pp_hov ((PPEexpr e) :: ((PPEstring
        ('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('a'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))) :: []))))

(** val get_Pvars : instr_info -> pexpr list -> var_i list cexec **)

let get_Pvars ii es =
  mapM (get_Pvar ii) es

(** val check_ty :
    instr_info -> var_i list -> stype list -> (pp_error_loc, unit) result **)

let check_ty ii xs tys =
  if all2 (fun x ty ->
       eq_op stype_eqType (Obj.magic Var.vtype x.v_var) (Obj.magic ty)) xs tys
  then Ok ()
  else Error
         (pp_internal_error_s_at E.pass ii
           ('b'::('a'::('d'::(' '::('t'::('y'::('p'::('e'::(' '::('f'::('o'::('r'::(' '::('s'::('p'::('i'::('l'::('l'::('/'::('u'::('n'::('s'::('p'::('i'::('l'::('l'::[])))))))))))))))))))))))))))

(** val spill_x :
    'a1 asmOp -> (instr_info -> Var.var -> Var.var cexec) -> instr_info ->
    assgn_tag -> spill_env -> var_i -> (pp_error_loc, SvExtra.Sv.t * 'a1
    instr) result **)

let spill_x _ get_spill0 ii t0 env x =
  match get_spill0 ii x.v_var with
  | Ok x0 ->
    let sx = { v_var = x0; v_info = x.v_info } in
    Ok ((SvExtra.Sv.add (Obj.magic x.v_var) env), (MkI (ii, (Cassgn ((Lvar
    sx), t0, (Var.vtype x.v_var), (coq_Plvar x))))))
  | Error s -> Error s

(** val spill_es :
    'a1 asmOp -> (instr_info -> Var.var -> Var.var cexec) -> instr_info ->
    assgn_tag -> spill_env -> stype list -> pexpr list -> (pp_error_loc,
    spill_env * 'a1 instr list) result **)

let spill_es asmop get_spill0 ii t0 env tys es =
  match get_Pvars ii es with
  | Ok x ->
    (match check_ty ii x tys with
     | Ok _ -> fmapM (spill_x asmop get_spill0 ii t0) env x
     | Error s -> Error s)
  | Error s -> Error s

(** val unspill_x :
    'a1 asmOp -> (instr_info -> Var.var -> Var.var cexec) -> instr_info ->
    assgn_tag -> spill_env -> var_i -> (pp_error_loc, 'a1 instr) result **)

let unspill_x _ get_spill0 ii t0 env x =
  if SvExtra.Sv.mem (Obj.magic x.v_var) env
  then (match get_spill0 ii x.v_var with
        | Ok x0 ->
          let sx = { v_var = x0; v_info = x.v_info } in
          Ok (MkI (ii, (Cassgn ((Lvar x), t0, (Var.vtype x.v_var),
          (coq_Plvar sx)))))
        | Error s -> Error s)
  else Error
         (E.error ii
           (pp_hov ((PPEstring
             ('T'::('h'::('e'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[]))))))))))))) :: ((PPEvar
             x.v_var) :: ((PPEstring
             ('n'::('e'::('e'::('d'::('s'::(' '::('t'::('o'::(' '::('b'::('e'::(' '::('s'::('p'::('i'::('l'::('l'::(' '::('b'::('e'::('f'::('o'::('r'::('e'::(' '::('('::('m'::('a'::('y'::('b'::('e'::(' '::('t'::('h'::('e'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('h'::('a'::('s'::(' '::('b'::('e'::('e'::('n'::(' '::('w'::('r'::('o'::('t'::('e'::(' '::('s'::('i'::('n'::('c'::('e'::(' '::('t'::('h'::('e'::(' '::('l'::('a'::('s'::('t'::(' '::('s'::('p'::('i'::('l'::('l'::(')'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: [])))))

(** val unspill_es :
    'a1 asmOp -> (instr_info -> Var.var -> Var.var cexec) -> instr_info ->
    assgn_tag -> spill_env -> stype list -> pexpr list -> (pp_error_loc, 'a1
    instr list) result **)

let unspill_es asmop get_spill0 ii t0 env tys es =
  match get_Pvars ii es with
  | Ok x ->
    (match check_ty ii x tys with
     | Ok _ -> mapM (unspill_x asmop get_spill0 ii t0 env) x
     | Error s -> Error s)
  | Error s -> Error s

(** val spill_c :
    'a1 asmOp -> (spill_env -> 'a1 instr -> (spill_env * 'a1 instr list)
    cexec) -> spill_env -> 'a1 instr list -> (spill_env * 'a1 instr list)
    cexec **)

let rec spill_c asmop spill_i0 env = function
| [] -> Ok (env, [])
| i :: c0 ->
  (match spill_i0 env i with
   | Ok x ->
     (match spill_c asmop spill_i0 (fst x) c0 with
      | Ok x0 -> Ok ((fst x0), (cat (snd x) (snd x0)))
      | Error s -> Error s)
   | Error s -> Error s)

(** val merge_env : spill_env -> spill_env -> SvExtra.Sv.t **)

let merge_env =
  SvExtra.Sv.inter

(** val loop :
    'a1 asmOp -> (spill_env -> 'a1 instr list -> (spill_env * 'a1 instr list)
    cexec) -> instr_info -> 'a1 instr list -> nat -> spill_env ->
    (spill_env * 'a1 instr list) cexec **)

let rec loop asmop spill_c0 ii c1 n env =
  match n with
  | O -> Error (E.ii_loop_iterator ii)
  | S n0 ->
    (match spill_c0 env c1 with
     | Ok x ->
       if SvExtra.Sv.subset env (fst x)
       then Ok (env, (snd x))
       else loop asmop spill_c0 ii c1 n0 (merge_env env (fst x))
     | Error s -> Error s)

(** val wloop :
    'a1 asmOp -> (spill_env -> 'a1 instr list -> (spill_env * 'a1 instr list)
    cexec) -> instr_info -> 'a1 instr list -> 'a1 instr list -> nat ->
    SvExtra.Sv.t -> (SvExtra.Sv.t * ('a1 instr list * 'a1 instr list)) cexec **)

let rec wloop asmop spill_c0 ii c1 c2 n env =
  match n with
  | O -> Error (E.ii_loop_iterator ii)
  | S n0 ->
    (match spill_c0 env c1 with
     | Ok x ->
       (match spill_c0 (fst x) c2 with
        | Ok x0 ->
          if SvExtra.Sv.subset env (fst x0)
          then Ok ((fst x), ((snd x), (snd x0)))
          else wloop asmop spill_c0 ii c1 c2 n0 (merge_env env (fst x0))
        | Error s -> Error s)
     | Error s -> Error s)

(** val spill_i :
    'a1 asmOp -> (instr_info -> Var.var -> Var.var cexec) -> spill_env -> 'a1
    instr -> (spill_env * 'a1 instr list) cexec **)

let rec spill_i asmop get_spill0 env i = match i with
| MkI (ii, ir) ->
  (match ir with
   | Cassgn (lv, _, _, _) -> Ok ((update_lv env lv), (i :: []))
   | Copn (lvs, t0, o, es) ->
     (match is_spill_op asmop o with
      | Some p ->
        let (s, tys) = p in
        (match s with
         | Spill -> spill_es asmop get_spill0 ii t0 env tys es
         | Unspill ->
           (match unspill_es asmop get_spill0 ii t0 env tys es with
            | Ok x -> Ok (env, x)
            | Error s0 -> Error s0))
      | None -> Ok ((update_lvs env lvs), (i :: [])))
   | Csyscall (lvs, _, _) -> Ok ((update_lvs env lvs), (i :: []))
   | Cif (e, c1, c2) ->
     (match spill_c asmop (spill_i asmop get_spill0) env c1 with
      | Ok x ->
        (match spill_c asmop (spill_i asmop get_spill0) env c2 with
         | Ok x0 ->
           Ok ((merge_env (fst x) (fst x0)), ((MkI (ii, (Cif (e, (snd x),
             (snd x0))))) :: []))
         | Error s -> Error s)
      | Error s -> Error s)
   | Cfor (x, r, c) ->
     (match loop asmop (spill_c asmop (spill_i asmop get_spill0)) ii c
              Loop.nb (SvExtra.Sv.remove (Obj.magic x.v_var) env) with
      | Ok x0 -> Ok ((fst x0), ((MkI (ii, (Cfor (x, r, (snd x0))))) :: []))
      | Error s -> Error s)
   | Cwhile (a, c1, e, c2) ->
     (match wloop asmop (spill_c asmop (spill_i asmop get_spill0)) ii c1 c2
              Loop.nb env with
      | Ok x ->
        Ok ((fst x), ((MkI (ii, (Cwhile (a, (fst (snd x)), e,
          (snd (snd x)))))) :: []))
      | Error s -> Error s)
   | Ccall (lvs, _, _) -> Ok ((update_lvs env lvs), (i :: [])))

(** val init_map :
    (v_kind -> instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident)
    -> SvExtra.Sv.t -> Var.var Mvar.t **)

let init_map fresh_var_ident s =
  SvExtra.Sv.fold (fun x m ->
    let n = Var.vname (Obj.magic x) in
    let k =
      match Ident.Ident.id_kind n with
      | Reg p ->
        let (_, r) = p in
        if Ident.Ident.spill_to_mmx n then Reg (Extra, r) else Stack r
      | _ -> Stack Direct
    in
    let ty = Var.vtype (Obj.magic x) in
    let n0 = Ident.Ident.id_name n in
    Mvar.set m x { Var.vtype = ty; Var.vname =
      (fresh_var_ident k dummy_instr_info n0 ty) }) s Mvar.empty

(** val get_spill :
    Var.var Mvar.t -> instr_info -> Var.var -> (pp_error_loc, Var.var) result **)

let get_spill m ii x =
  match Mvar.get m (Obj.magic x) with
  | Some sx -> Ok sx
  | None ->
    Error
      (E.error ii
        (pp_hov ((PPEstring
          ('T'::('h'::('e'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[]))))))))))))) :: ((PPEvar
          x) :: ((PPEstring
          ('n'::('e'::('e'::('d'::('s'::(' '::('t'::('o'::(' '::('b'::('e'::(' '::('s'::('p'::('i'::('l'::('l'::[])))))))))))))))))) :: [])))))

(** val check_map : Var.var Mvar.t -> SvExtra.Sv.t -> bool * SvExtra.Sv.t **)

let check_map m x =
  Mvar.fold (fun _ sx bX ->
    (((&&) (fst bX) (negb (SvExtra.Sv.mem (Obj.magic sx) (snd bX)))),
    (SvExtra.Sv.add (Obj.magic sx) (snd bX)))) m (true, x)

(** val spill_fd :
    'a1 asmOp -> (v_kind -> instr_info -> Ident.Ident.name -> stype ->
    Ident.Ident.ident) -> funname -> ('a1, 'a2) _fundef -> ('a1, 'a2) _fundef
    cexec **)

let spill_fd asmop fresh_var_ident _ fd =
  let { f_info = ii; f_tyin = tyi; f_params = params; f_body = c; f_tyout =
    tyo; f_res = res; f_extra = ef } = fd
  in
  let s = foldl (to_spill_i asmop) SvExtra.Sv.empty c in
  if SvExtra.Sv.is_empty s
  then Ok fd
  else let m = init_map fresh_var_ident s in
       let x =
         SvExtra.Sv.union (vars_l params)
           (SvExtra.Sv.union (vars_l res) (vars_c asmop c))
       in
       let b = check_map m x in
       if fst b
       then (match spill_c asmop (spill_i asmop (get_spill m))
                     SvExtra.Sv.empty c with
             | Ok x0 ->
               Ok { f_info = ii; f_tyin = tyi; f_params = params; f_body =
                 (snd x0); f_tyout = tyo; f_res = res; f_extra = ef }
             | Error s0 -> Error s0)
       else let s0 =
              pp_internal_error E.pass (PPEstring
                ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('m'::('a'::('p'::[]))))))))))))
            in
            Error s0

(** val spill_prog :
    'a1 asmOp -> (v_kind -> instr_info -> Ident.Ident.name -> stype ->
    Ident.Ident.ident) -> progT -> 'a1 prog -> 'a1 prog cexec **)

let spill_prog asmop fresh_var_ident _ p =
  match map_cfprog_name_gen (fun x -> x.f_info)
          (spill_fd asmop fresh_var_ident) p.p_funcs with
  | Ok x -> Ok { p_funcs = x; p_globs = p.p_globs; p_extra = p.p_extra }
  | Error s -> Error s
