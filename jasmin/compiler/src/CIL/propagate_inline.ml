open Datatypes
open Compiler_util
open Constant_prop
open Eqtype
open Expr
open Flag_combination
open Seq
open Sopn
open Utils0
open Var0

module E =
 struct
  (** val pass : char list **)

  let pass =
    'p'::('r'::('o'::('p'::('a'::('g'::('a'::('t'::('e'::(' '::('i'::('n'::('l'::('i'::('n'::('e'::[])))))))))))))))

  (** val ii_loop_iterator : instr_info -> pp_error_loc **)

  let ii_loop_iterator =
    ii_loop_iterator pass
 end

type pi_cel = { pi_def : pexpr; pi_fv : SvExtra.Sv.t; pi_m : bool }

type pimap = pi_cel Mvar.t

(** val piempty : pimap **)

let piempty =
  Mvar.empty

(** val remove : pimap -> Var.var -> pi_cel Mvar.t **)

let remove pi x =
  Mvar.filter_map (fun y c ->
    if (||) (eq_op Var.var_eqType (Obj.magic x) y)
         (SvExtra.Sv.mem (Obj.magic x) c.pi_fv)
    then None
    else Some c) pi

(** val remove_m : pimap -> pi_cel Mvar.t **)

let remove_m pi =
  Mvar.filter_map (fun _ c -> if c.pi_m then None else Some c) pi

(** val set : pimap -> Var.var -> pexpr -> pimap **)

let set pi x e =
  let fv = read_e e in
  let use = use_mem e in
  if SvExtra.Sv.mem (Obj.magic x) fv
  then pi
  else Mvar.set pi (Obj.magic x) { pi_def = e; pi_fv = fv; pi_m = use }

(** val merge : pimap -> pimap -> pi_cel Mvar.t **)

let merge pi1 pi2 =
  let ondefs = fun _ o1 o2 ->
    match o1 with
    | Some c1 ->
      (match o2 with
       | Some c2 -> if eq_expr c1.pi_def c2.pi_def then o1 else None
       | None -> None)
    | None -> None
  in
  Mvar.map2 ondefs pi1 pi2

(** val incl : pimap -> pimap -> bool **)

let incl pi1 pi2 =
  Mvar.incl (fun _ c1 c2 -> eq_expr c1.pi_def c2.pi_def) pi1 pi2

(** val scfc :
    coq_FlagCombinationParams -> combine_flags -> pexpr list -> pexpr **)

let scfc fcp cf es = match es with
| [] -> PappN ((Ocombine_flags cf), es)
| eof :: l ->
  (match l with
   | [] -> PappN ((Ocombine_flags cf), es)
   | ecf :: l0 ->
     (match l0 with
      | [] -> PappN ((Ocombine_flags cf), es)
      | esf :: l1 ->
        (match l1 with
         | [] -> PappN ((Ocombine_flags cf), es)
         | ezf :: l2 ->
           (match l2 with
            | [] -> cf_xsem fcp snot sand sor sbeq eof ecf esf ezf cf
            | _ :: _ -> PappN ((Ocombine_flags cf), es)))))

(** val pi_e : coq_FlagCombinationParams -> pimap -> pexpr -> pexpr **)

let rec pi_e fcp pi e = match e with
| Pvar x ->
  if is_lvar x
  then (match Mvar.get pi (Obj.magic x.gv.v_var) with
        | Some c -> c.pi_def
        | None -> e)
  else e
| Pget (aa, ws, x, e0) -> Pget (aa, ws, x, (pi_e fcp pi e0))
| Psub (aa, ws, len, x, e0) -> Psub (aa, ws, len, x, (pi_e fcp pi e0))
| Pload (ws, x, e0) -> Pload (ws, x, (pi_e fcp pi e0))
| Papp1 (o, e0) -> Papp1 (o, (pi_e fcp pi e0))
| Papp2 (o, e1, e2) -> Papp2 (o, (pi_e fcp pi e1), (pi_e fcp pi e2))
| PappN (o, es) ->
  let es0 = map (pi_e fcp pi) es in
  (match o with
   | Opack (_, _) -> PappN (o, es0)
   | Ocombine_flags c -> scfc fcp c es0)
| Pif (t0, e0, e1, e2) ->
  Pif (t0, (pi_e fcp pi e0), (pi_e fcp pi e1), (pi_e fcp pi e2))
| _ -> e

(** val pi_es :
    coq_FlagCombinationParams -> pimap -> pexpr list -> pexpr list **)

let pi_es fcp pi es =
  map (pi_e fcp pi) es

(** val pi_lv : coq_FlagCombinationParams -> pimap -> lval -> pimap * lval **)

let pi_lv fcp pi lv = match lv with
| Lnone (_, _) -> (pi, lv)
| Lvar x -> ((remove pi x.v_var), lv)
| Lmem (ws, x, e) -> ((remove_m pi), (Lmem (ws, x, (pi_e fcp pi e))))
| Laset (aa, ws, x, e) ->
  ((remove pi x.v_var), (Laset (aa, ws, x, (pi_e fcp pi e))))
| Lasub (aa, ws, len, x, e) ->
  ((remove pi x.v_var), (Lasub (aa, ws, len, x, (pi_e fcp pi e))))

(** val pi_lvs :
    coq_FlagCombinationParams -> pimap -> lval list -> pimap * lval list **)

let pi_lvs fcp pi xs =
  fmap (pi_lv fcp) pi xs

(** val set_lv : pimap -> lval -> Equality.sort -> pexpr -> pimap **)

let set_lv pi x tag e =
  match x with
  | Lvar x0 ->
    if eq_op assgn_tag_eqType tag (Obj.magic AT_inline)
    then set pi x0.v_var e
    else pi
  | _ -> pi

(** val pi_c :
    'a1 asmOp -> (pimap -> 'a1 instr -> (pimap * 'a1 instr) cexec) -> pimap
    -> 'a1 instr list -> (pp_error_loc, pimap * 'a1 instr list) result **)

let pi_c _ =
  fmapM

(** val loop_for :
    'a1 asmOp -> (pimap -> 'a1 instr -> (pimap * 'a1 instr) cexec) ->
    instr_info -> Var.var -> 'a1 instr list -> nat -> pimap -> (pp_error_loc,
    pimap * 'a1 instr list) result **)

let rec loop_for asmop pi_i0 ii x c n pi =
  match n with
  | O -> Error (E.ii_loop_iterator ii)
  | S n0 ->
    let pii = remove pi x in
    (match pi_c asmop pi_i0 pii c with
     | Ok x0 ->
       if incl pi (fst x0)
       then Ok (pi, (snd x0))
       else loop_for asmop pi_i0 ii x c n0 (merge pi (fst x0))
     | Error s -> Error s)

(** val loop_while :
    'a1 asmOp -> coq_FlagCombinationParams -> (pimap -> 'a1 instr ->
    (pimap * 'a1 instr) cexec) -> instr_info -> 'a1 instr list -> pexpr ->
    'a1 instr list -> nat -> pimap -> (pp_error_loc, ((pimap * 'a1 instr
    list) * pexpr) * 'a1 instr list) result **)

let rec loop_while asmop fcp pi_i0 ii c1 e c2 n pi =
  match n with
  | O -> Error (E.ii_loop_iterator ii)
  | S n0 ->
    (match pi_c asmop pi_i0 pi c1 with
     | Ok x ->
       (match pi_c asmop pi_i0 (fst x) c2 with
        | Ok x0 ->
          if incl pi (fst x0)
          then Ok ((((fst x), (snd x)), (pi_e fcp (fst x) e)), (snd x0))
          else loop_while asmop fcp pi_i0 ii c1 e c2 n0 (merge pi (fst x0))
        | Error s -> Error s)
     | Error s -> Error s)

(** val pi_i :
    'a1 asmOp -> coq_FlagCombinationParams -> pimap -> 'a1 instr ->
    (pp_error_loc, pimap * 'a1 instr) result **)

let rec pi_i asmop fcp pi = function
| MkI (ii, ir) ->
  (match ir with
   | Cassgn (x, tag, ty, e) ->
     let e0 = pi_e fcp pi e in
     let (pi0, x0) = pi_lv fcp pi x in
     let pi1 = set_lv pi0 x0 (Obj.magic tag) e0 in
     Ok (pi1, (MkI (ii, (Cassgn (x0, tag, ty, e0)))))
   | Copn (xs, tag, o, es) ->
     let es0 = pi_es fcp pi es in
     let (pi0, xs0) = pi_lvs fcp pi xs in
     Ok (pi0, (MkI (ii, (Copn (xs0, tag, o, es0)))))
   | Csyscall (xs, o, es) ->
     let es0 = pi_es fcp pi es in
     let pi0 = remove_m pi in
     let (pi1, xs0) = pi_lvs fcp pi0 xs in
     Ok (pi1, (MkI (ii, (Csyscall (xs0, o, es0)))))
   | Cif (e, c1, c2) ->
     let e0 = pi_e fcp pi e in
     (match pi_c asmop (pi_i asmop fcp) pi c1 with
      | Ok x ->
        (match pi_c asmop (pi_i asmop fcp) pi c2 with
         | Ok x0 ->
           let pi0 = merge (fst x) (fst x0) in
           Ok (pi0, (MkI (ii, (Cif (e0, (snd x), (snd x0))))))
         | Error s -> Error s)
      | Error s -> Error s)
   | Cfor (x, r, c) ->
     let (p, e2) = r in
     let (d, e1) = p in
     let e3 = pi_e fcp pi e1 in
     let e4 = pi_e fcp pi e2 in
     (match loop_for asmop (pi_i asmop fcp) ii x.v_var c Loop.nb pi with
      | Ok x0 ->
        Ok ((fst x0), (MkI (ii, (Cfor (x, ((d, e3), e4), (snd x0))))))
      | Error s -> Error s)
   | Cwhile (a, c1, e, c2) ->
     (match loop_while asmop fcp (pi_i asmop fcp) ii c1 e c2 Loop.nb pi with
      | Ok x ->
        let (y, c3) = x in
        let (y0, e0) = y in
        let (pi0, c4) = y0 in Ok (pi0, (MkI (ii, (Cwhile (a, c4, e0, c3)))))
      | Error s -> Error s)
   | Ccall (xs, f, es) ->
     let es0 = pi_es fcp pi es in
     let (pi0, xs0) = pi_lvs fcp (remove_m pi) xs in
     Ok (pi0, (MkI (ii, (Ccall (xs0, f, es0))))))

(** val pi_fun :
    'a1 asmOp -> coq_FlagCombinationParams -> progT -> 'a1 fundef ->
    (pp_error_loc, ('a1, extra_fun_t) _fundef) result **)

let pi_fun asmop fcp _ f =
  let { f_info = ii; f_tyin = si; f_params = p; f_body = c; f_tyout = so;
    f_res = r; f_extra = ev } = f
  in
  (match pi_c asmop (pi_i asmop fcp) piempty c with
   | Ok x ->
     Ok { f_info = ii; f_tyin = si; f_params = p; f_body = (snd x); f_tyout =
       so; f_res = r; f_extra = ev }
   | Error s -> Error s)

(** val pi_prog :
    'a1 asmOp -> coq_FlagCombinationParams -> progT -> 'a1 prog ->
    (pp_error_loc, ('a1, extra_fun_t, extra_prog_t) _prog) result **)

let pi_prog asmop fcp pT p =
  match map_cfprog_gen (fun x -> x.f_info) (pi_fun asmop fcp pT) p.p_funcs with
  | Ok x -> Ok { p_funcs = x; p_globs = p.p_globs; p_extra = p.p_extra }
  | Error s -> Error s
