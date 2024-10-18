open Datatypes
open Compiler_util
open Eqtype
open Expr
open Global
open Seq
open Sopn
open Ssralg
open Type
open Utils0
open Var0
open Word0
open Wsize

module E =
 struct
  (** val pass : char list **)

  let pass =
    'r'::('e'::('m'::('o'::('v'::('e'::(' '::('g'::('l'::('o'::('b'::('a'::('l'::('s'::[])))))))))))))

  (** val rm_glob_error : instr_info -> Var.var -> pp_error_loc **)

  let rm_glob_error ii x =
    { pel_msg =
      (pp_box ((PPEstring
        ('C'::('a'::('n'::('n'::('o'::('t'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::(' '::('g'::('l'::('o'::('b'::('a'::('l'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))))))))) :: ((PPEvar
        x) :: []))); pel_fn = None; pel_fi = None; pel_ii = (Some ii);
      pel_vi = None; pel_pass = (Some pass); pel_internal = false }

  (** val rm_glob_error_dup : instr_info -> Var.var -> pp_error_loc **)

  let rm_glob_error_dup ii x =
    { pel_msg =
      (pp_box ((PPEstring
        ('D'::('u'::('p'::('l'::('i'::('c'::('a'::('t'::('e'::(' '::('d'::('e'::('f'::('i'::('n'::('i'::('t'::('i'::('o'::('n'::(' '::('o'::('f'::(' '::('g'::('l'::('o'::('b'::('a'::('l'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))))))))))))))))))) :: ((PPEvar
        x) :: []))); pel_fn = None; pel_fi = None; pel_ii = (Some ii);
      pel_vi = None; pel_pass = (Some pass); pel_internal = false }

  (** val loop_iterator : pp_error_loc **)

  let loop_iterator =
    loop_iterator pass

  (** val rm_glob_ierror : char list -> pp_error_loc **)

  let rm_glob_ierror =
    pp_internal_error_s pass
 end

(** val check_data : glob_value -> wsize -> GRing.ComRing.sort -> bool **)

let check_data d ws w =
  match d with
  | Gword (ws', w') ->
    (&&) (eq_op wsize_eqType (Obj.magic ws) (Obj.magic ws'))
      (eq_op (GRing.ComRing.eqType (word ws)) w (zero_extend ws ws' w'))
  | Garr (_, _) -> false

(** val find_glob :
    instr_info -> var_i -> glob_decl list -> wsize -> GRing.ComRing.sort ->
    (pp_error_loc, Var.var) result **)

let find_glob ii xi gd ws w =
  let test = fun gv0 ->
    if (&&)
         (eq_op stype_eqType (Obj.magic (Coq_sword ws))
           (Obj.magic Var.vtype (fst gv0))) (check_data (snd gv0) ws w)
    then Some (fst gv0)
    else None
  in
  (match find_map test gd with
   | Some g -> Ok g
   | None -> Error (E.rm_glob_error ii xi.v_var))

(** val add_glob :
    (glob_decl list -> Var.var -> Ident.Ident.ident) -> instr_info -> Var.var
    -> glob_decl list -> wsize -> GRing.ComRing.sort -> (pp_error_loc,
    glob_decl list) result **)

let add_glob fresh_id ii x gd ws w =
  let test = fun gv0 ->
    (&&)
      (eq_op stype_eqType (Obj.magic (Coq_sword ws))
        (Obj.magic Var.vtype (fst gv0))) (check_data (snd gv0) ws w)
  in
  if has test gd
  then Ok gd
  else let gx = { Var.vtype = (Var.vtype x); Var.vname = (fresh_id gd x) } in
       if has (fun g' ->
            eq_op Var.var_eqType (fst (Obj.magic g')) (Obj.magic gx)) gd
       then Error (E.rm_glob_error_dup ii gx)
       else Ok ((gx, (Gword (ws, w))) :: gd)

(** val extend_glob_i :
    'a1 asmOp -> (glob_decl list -> Var.var -> Ident.Ident.ident) -> 'a1
    instr -> glob_decl list -> (pp_error_loc, glob_decl list) result **)

let rec extend_glob_i asmop fresh_id i gd =
  let MkI (ii, i0) = i in
  (match i0 with
   | Cassgn (lv, _, _, e) ->
     (match lv with
      | Lvar xi ->
        let x = xi.v_var in
        if is_glob_var x
        then (match e with
              | Papp1 (s, p) ->
                (match s with
                 | Oword_of_int ws ->
                   (match p with
                    | Pconst z -> add_glob fresh_id ii x gd ws (wrepr ws z)
                    | _ -> Error (E.rm_glob_error ii xi.v_var))
                 | _ -> Error (E.rm_glob_error ii xi.v_var))
              | _ -> Error (E.rm_glob_error ii xi.v_var))
        else Ok gd
      | _ -> Ok gd)
   | Cif (_, c1, c2) ->
     (match foldM (extend_glob_i asmop fresh_id) gd c1 with
      | Ok x -> foldM (extend_glob_i asmop fresh_id) x c2
      | Error s -> Error s)
   | Cfor (_, _, c) -> foldM (extend_glob_i asmop fresh_id) gd c
   | Cwhile (_, c1, _, c2) ->
     (match foldM (extend_glob_i asmop fresh_id) gd c1 with
      | Ok x -> foldM (extend_glob_i asmop fresh_id) x c2
      | Error s -> Error s)
   | _ -> Ok gd)

(** val extend_glob_prog :
    'a1 asmOp -> (glob_decl list -> Var.var -> Ident.Ident.ident) -> 'a1
    uprog -> (pp_error_loc, glob_decl list) result **)

let extend_glob_prog asmop fresh_id p =
  foldM (fun f gd -> foldM (extend_glob_i asmop fresh_id) gd (snd f).f_body)
    p.p_globs p.p_funcs

(** val get_var_ :
    instr_info -> Var.var Mvar.t -> gvar -> (pp_error_loc, gvar) result **)

let get_var_ ii env xi =
  if is_lvar xi
  then let vi = xi.gv in
       let x = vi.v_var in
       if is_glob_var x
       then (match Mvar.get env (Obj.magic x) with
             | Some g -> Ok (mk_gvar { v_var = g; v_info = vi.v_info })
             | None -> Error (E.rm_glob_error ii vi.v_var))
       else Ok xi
  else Ok xi

(** val remove_glob_e :
    instr_info -> Var.var Mvar.t -> pexpr -> (pp_error_loc, pexpr) result **)

let rec remove_glob_e ii env e = match e with
| Pvar xi ->
  (match get_var_ ii env xi with
   | Ok x -> Ok (Pvar x)
   | Error s -> Error s)
| Pget (aa, ws, xi, e0) ->
  (match remove_glob_e ii env e0 with
   | Ok x ->
     (match get_var_ ii env xi with
      | Ok x0 -> Ok (Pget (aa, ws, x0, x))
      | Error s -> Error s)
   | Error s -> Error s)
| Psub (aa, ws, len, xi, e0) ->
  (match remove_glob_e ii env e0 with
   | Ok x ->
     (match get_var_ ii env xi with
      | Ok x0 -> Ok (Psub (aa, ws, len, x0, x))
      | Error s -> Error s)
   | Error s -> Error s)
| Pload (ws, xi, e0) ->
  let x = xi.v_var in
  if is_glob_var x
  then Error (E.rm_glob_error ii xi.v_var)
  else (match remove_glob_e ii env e0 with
        | Ok x0 -> Ok (Pload (ws, xi, x0))
        | Error s -> Error s)
| Papp1 (o, e0) ->
  (match remove_glob_e ii env e0 with
   | Ok x -> Ok (Papp1 (o, x))
   | Error s -> Error s)
| Papp2 (o, e1, e2) ->
  (match remove_glob_e ii env e1 with
   | Ok x ->
     (match remove_glob_e ii env e2 with
      | Ok x0 -> Ok (Papp2 (o, x, x0))
      | Error s -> Error s)
   | Error s -> Error s)
| PappN (op, es) ->
  (match mapM (remove_glob_e ii env) es with
   | Ok x -> Ok (PappN (op, x))
   | Error s -> Error s)
| Pif (t0, e0, e1, e2) ->
  (match remove_glob_e ii env e0 with
   | Ok x ->
     (match remove_glob_e ii env e1 with
      | Ok x0 ->
        (match remove_glob_e ii env e2 with
         | Ok x1 -> Ok (Pif (t0, x, x0, x1))
         | Error s -> Error s)
      | Error s -> Error s)
   | Error s -> Error s)
| _ -> Ok e

(** val remove_glob_lv :
    instr_info -> Var.var Mvar.t -> lval -> (pp_error_loc, lval) result **)

let remove_glob_lv ii env lv = match lv with
| Lnone (_, _) -> Ok lv
| Lvar xi ->
  let x = xi.v_var in
  if is_glob_var x then Error (E.rm_glob_error ii xi.v_var) else Ok lv
| Lmem (ws, xi, e) ->
  let x = xi.v_var in
  if is_glob_var x
  then Error (E.rm_glob_error ii xi.v_var)
  else (match remove_glob_e ii env e with
        | Ok x0 -> Ok (Lmem (ws, xi, x0))
        | Error s -> Error s)
| Laset (aa, ws, xi, e) ->
  let x = xi.v_var in
  if is_glob_var x
  then Error (E.rm_glob_error ii xi.v_var)
  else (match remove_glob_e ii env e with
        | Ok x0 -> Ok (Laset (aa, ws, xi, x0))
        | Error s -> Error s)
| Lasub (aa, ws, len, xi, e) ->
  let x = xi.v_var in
  if is_glob_var x
  then Error (E.rm_glob_error ii xi.v_var)
  else (match remove_glob_e ii env e with
        | Ok x0 -> Ok (Lasub (aa, ws, len, xi, x0))
        | Error s -> Error s)

(** val remove_glob :
    'a1 asmOp -> (Var.var Mvar.t -> 'a1 instr -> (Var.var Mvar.t * 'a1 instr
    list) cexec) -> Var.var Mvar.t -> 'a1 instr list -> (Var.var Mvar.t * 'a1
    instr list) cexec **)

let rec remove_glob asmop remove_glob_i0 e = function
| [] -> Ok (e, [])
| i :: c0 ->
  (match remove_glob_i0 e i with
   | Ok x ->
     (match remove_glob asmop remove_glob_i0 (fst x) c0 with
      | Ok x0 -> Ok ((fst x0), (app (snd x) (snd x0)))
      | Error s -> Error s)
   | Error s -> Error s)

(** val merge_glob :
    Var.var -> Var.var option -> Var.var option -> Var.var option **)

let merge_glob _ o1 o2 =
  match o1 with
  | Some g1 ->
    (match o2 with
     | Some g2 ->
       if eq_op Var.var_eqType (Obj.magic g1) (Obj.magic g2) then o1 else None
     | None -> None)
  | None -> None

(** val coq_Mincl : Var.var Mvar.t -> Var.var Mvar.t -> bool **)

let coq_Mincl m1 m2 =
  all (fun xg ->
    match Mvar.get m2 (fst xg) with
    | Some g' -> eq_op Var.var_eqType (snd (Obj.magic xg)) (Obj.magic g')
    | None -> false) (Mvar.elements m1)

(** val merge_env : Var.var Mvar.t -> Var.var Mvar.t -> Var.var Mvar.t **)

let merge_env env1 env2 =
  Mvar.map2 (Obj.magic merge_glob) env1 env2

(** val loop :
    'a1 asmOp -> (Var.var Mvar.t -> (Var.var Mvar.t * 'a1 instr list) cexec)
    -> nat -> Var.var Mvar.t -> (pp_error_loc, Var.var Mvar.t * 'a1 instr
    list) result **)

let rec loop asmop check_c n m =
  match n with
  | O -> Error E.loop_iterator
  | S n0 ->
    (match check_c m with
     | Ok x ->
       if coq_Mincl m (fst x)
       then Ok (m, (snd x))
       else loop asmop check_c n0 (merge_env m (fst x))
     | Error s -> Error s)

type 'asm_op check2_r =
| Check2_r of pexpr * (Var.var Mvar.t * 'asm_op instr list)
   * (Var.var Mvar.t * 'asm_op instr list)

type 'asm_op loop2_r =
| Loop2_r of pexpr * 'asm_op instr list * 'asm_op instr list * Var.var Mvar.t

(** val loop2 :
    'a1 asmOp -> (Var.var Mvar.t -> 'a1 check2_r cexec) -> nat -> Var.var
    Mvar.t -> (pp_error_loc, 'a1 loop2_r) result **)

let rec loop2 asmop check_c2 n m =
  match n with
  | O -> Error E.loop_iterator
  | S n0 ->
    (match check_c2 m with
     | Ok x ->
       let Check2_r (e, p, p0) = x in
       let (m1, c1) = p in
       let (m2, c2) = p0 in
       if coq_Mincl m m2
       then Ok (Loop2_r (e, c1, c2, m1))
       else loop2 asmop check_c2 n0 (merge_env m m2)
     | Error s -> Error s)

(** val remove_glob_i :
    'a1 asmOp -> glob_decl list -> Var.var Mvar.t -> 'a1 instr -> (Var.var
    Mvar.t * 'a1 instr list) cexec **)

let rec remove_glob_i asmop gd env = function
| MkI (ii, i0) ->
  (match i0 with
   | Cassgn (lv, tag, ty, e) ->
     (match remove_glob_e ii env e with
      | Ok x ->
        (match lv with
         | Lvar xi ->
           let x0 = xi.v_var in
           if is_glob_var x0
           then (match x with
                 | Papp1 (s, p) ->
                   (match s with
                    | Oword_of_int ws ->
                      (match p with
                       | Pconst z ->
                         if (&&)
                              (eq_op stype_eqType (Obj.magic ty)
                                (Obj.magic (Coq_sword ws)))
                              (eq_op stype_eqType (Obj.magic Var.vtype x0)
                                (Obj.magic (Coq_sword ws)))
                         then (match find_glob ii xi gd ws (wrepr ws z) with
                               | Ok x1 ->
                                 Ok ((Mvar.set env (Obj.magic x0) x1), [])
                               | Error s0 -> Error s0)
                         else Error (E.rm_glob_error ii xi.v_var)
                       | _ -> Error (E.rm_glob_error ii xi.v_var))
                    | _ -> Error (E.rm_glob_error ii xi.v_var))
                 | _ -> Error (E.rm_glob_error ii xi.v_var))
           else (match remove_glob_lv ii env lv with
                 | Ok x1 ->
                   Ok (env, ((MkI (ii, (Cassgn (x1, tag, ty, x)))) :: []))
                 | Error s -> Error s)
         | _ ->
           (match remove_glob_lv ii env lv with
            | Ok x0 -> Ok (env, ((MkI (ii, (Cassgn (x0, tag, ty, x)))) :: []))
            | Error s -> Error s))
      | Error s -> Error s)
   | Copn (lvs, tag, o, es) ->
     (match mapM (remove_glob_lv ii env) lvs with
      | Ok x ->
        (match mapM (remove_glob_e ii env) es with
         | Ok x0 -> Ok (env, ((MkI (ii, (Copn (x, tag, o, x0)))) :: []))
         | Error s -> Error s)
      | Error s -> Error s)
   | Csyscall (lvs, o, es) ->
     (match mapM (remove_glob_lv ii env) lvs with
      | Ok x ->
        (match mapM (remove_glob_e ii env) es with
         | Ok x0 -> Ok (env, ((MkI (ii, (Csyscall (x, o, x0)))) :: []))
         | Error s -> Error s)
      | Error s -> Error s)
   | Cif (e, c1, c2) ->
     (match remove_glob_e ii env e with
      | Ok x ->
        (match remove_glob asmop (remove_glob_i asmop gd) env c1 with
         | Ok x0 ->
           let env1 = fst x0 in
           let c3 = snd x0 in
           (match remove_glob asmop (remove_glob_i asmop gd) env c2 with
            | Ok x1 ->
              let env2 = fst x1 in
              let c4 = snd x1 in
              let env0 = merge_env env1 env2 in
              Ok (env0, ((MkI (ii, (Cif (x, c3, c4)))) :: []))
            | Error s -> Error s)
         | Error s -> Error s)
      | Error s -> Error s)
   | Cfor (xi, r, c) ->
     let (p, e2) = r in
     let (d, e1) = p in
     if is_glob_var xi.v_var
     then Error (E.rm_glob_error ii xi.v_var)
     else (match remove_glob_e ii env e1 with
           | Ok x ->
             (match remove_glob_e ii env e2 with
              | Ok x0 ->
                let check_c = fun env0 ->
                  remove_glob asmop (remove_glob_i asmop gd) env0 c
                in
                (match loop asmop check_c Loop.nb env with
                 | Ok x1 ->
                   let (env0, c0) = x1 in
                   Ok (env0, ((MkI (ii, (Cfor (xi, ((d, x), x0),
                   c0)))) :: []))
                 | Error s -> Error s)
              | Error s -> Error s)
           | Error s -> Error s)
   | Cwhile (a, c1, e, c2) ->
     let check_c = fun env0 ->
       match remove_glob asmop (remove_glob_i asmop gd) env0 c1 with
       | Ok x ->
         let env1 = fst x in
         (match remove_glob_e ii env1 e with
          | Ok x0 ->
            (match remove_glob asmop (remove_glob_i asmop gd) env1 c2 with
             | Ok x1 -> Ok (Check2_r (x0, x, x1))
             | Error s -> Error s)
          | Error s -> Error s)
       | Error s -> Error s
     in
     (match loop2 asmop check_c Loop.nb env with
      | Ok x ->
        let Loop2_r (e0, c3, c4, env0) = x in
        Ok (env0, ((MkI (ii, (Cwhile (a, c3, e0, c4)))) :: []))
      | Error s -> Error s)
   | Ccall (lvs, fn, es) ->
     (match mapM (remove_glob_lv ii env) lvs with
      | Ok x ->
        (match mapM (remove_glob_e ii env) es with
         | Ok x0 -> Ok (env, ((MkI (ii, (Ccall (x, fn, x0)))) :: []))
         | Error s -> Error s)
      | Error s -> Error s))

(** val remove_glob_fundef :
    'a1 asmOp -> glob_decl list -> 'a1 ufundef -> (pp_error_loc, ('a1,
    extra_fun_t) _fundef) result **)

let remove_glob_fundef asmop gd f =
  let check_var = fun xi ->
    if is_glob_var xi.v_var
    then Error (E.rm_glob_error dummy_instr_info xi.v_var)
    else Ok ()
  in
  (match mapM check_var f.f_params with
   | Ok _ ->
     (match mapM check_var f.f_res with
      | Ok _ ->
        (match remove_glob asmop (remove_glob_i asmop gd) Mvar.empty f.f_body with
         | Ok x ->
           Ok { f_info = f.f_info; f_tyin = f.f_tyin; f_params = f.f_params;
             f_body = (snd x); f_tyout = f.f_tyout; f_res = f.f_res;
             f_extra = f.f_extra }
         | Error s -> Error s)
      | Error s -> Error s)
   | Error s -> Error s)

(** val remove_glob_prog :
    'a1 asmOp -> (glob_decl list -> Var.var -> Ident.Ident.ident) -> 'a1
    uprog -> (pp_error_loc, ('a1, extra_fun_t, extra_prog_t) _prog) result **)

let remove_glob_prog asmop fresh_id p =
  match extend_glob_prog asmop fresh_id p with
  | Ok x ->
    if uniq Var.var_eqType (map (Obj.magic fst) x)
    then (match map_cfprog_gen (fun x0 -> x0.f_info)
                  (remove_glob_fundef asmop x) p.p_funcs with
          | Ok x0 -> Ok { p_funcs = x0; p_globs = x; p_extra = p.p_extra }
          | Error s -> Error s)
    else Error
           (E.rm_glob_ierror
             ('T'::('w'::('o'::(' '::('g'::('l'::('o'::('b'::('a'::('l'::(' '::('d'::('e'::('c'::('l'::('a'::('r'::('a'::('t'::('i'::('o'::('n'::('s'::(' '::('h'::('a'::('v'::('e'::(' '::('t'::('h'::('e'::(' '::('s'::('a'::('m'::('e'::(' '::('n'::('a'::('m'::('e'::[])))))))))))))))))))))))))))))))))))))))))))
  | Error s -> Error s
