open List0
open Expr
open Seq
open Sopn
open Var0

(** val map_repeat : ('a1 -> 'a2 * bool) -> 'a1 list -> 'a2 list * bool **)

let map_repeat f m =
  fold_right (fun u pat ->
    let (vs, a) = pat in let (v, b) = f u in ((v :: vs), ((||) a b))) ([],
    false) m

(** val unroll_cmd :
    'a1 asmOp -> ('a1 instr -> 'a1 instr list * bool) -> 'a1 instr list ->
    'a1 instr list * bool **)

let unroll_cmd _ unroll_i0 c =
  fold_right (fun i pat ->
    let (c', a) = pat in
    let (i', b) = unroll_i0 i in ((cat i' c'), ((||) a b))) ([], false) c

(** val assgn : 'a1 asmOp -> instr_info -> var_i -> pexpr -> 'a1 instr **)

let assgn _ ii x e =
  MkI (ii, (Cassgn ((Lvar x), AT_inline, (Var.vtype x.v_var), e)))

(** val unroll_i : 'a1 asmOp -> 'a1 instr -> 'a1 instr list * bool **)

let rec unroll_i asmop i = match i with
| MkI (ii, ir) ->
  (match ir with
   | Cif (b, c1, c2) ->
     let (c1', b1) = unroll_cmd asmop (unroll_i asmop) c1 in
     let (c2', b2) = unroll_cmd asmop (unroll_i asmop) c2 in
     (((MkI (ii, (Cif (b, c1', c2')))) :: []), ((||) b1 b2))
   | Cfor (i0, r, c) ->
     let (p, hi) = r in
     let (dir, low) = p in
     let (c', b) = unroll_cmd asmop (unroll_i asmop) c in
     (match is_const low with
      | Some vlo ->
        (match is_const hi with
         | Some vhi ->
           let l = wrange dir vlo vhi in
           let cs = map (fun n -> (assgn asmop ii i0 (Pconst n)) :: c') l in
           ((flatten cs), true)
         | None -> (((MkI (ii, (Cfor (i0, ((dir, low), hi), c')))) :: []), b))
      | None -> (((MkI (ii, (Cfor (i0, ((dir, low), hi), c')))) :: []), b))
   | Cwhile (a, c1, e, c2) ->
     let (c1', b1) = unroll_cmd asmop (unroll_i asmop) c1 in
     let (c2', b2) = unroll_cmd asmop (unroll_i asmop) c2 in
     (((MkI (ii, (Cwhile (a, c1', e, c2')))) :: []), ((||) b1 b2))
   | _ -> ((i :: []), false))

(** val unroll_fun :
    'a1 asmOp -> progT -> 'a1 fun_decl -> (funname * ('a1, extra_fun_t)
    _fundef) * bool **)

let unroll_fun asmop _ = function
| (fn, f0) ->
  let { f_info = ii; f_tyin = si; f_params = p; f_body = c; f_tyout = so;
    f_res = r; f_extra = ev } = f0
  in
  let (c', b) = unroll_cmd asmop (unroll_i asmop) c in
  ((fn, { f_info = ii; f_tyin = si; f_params = p; f_body = c'; f_tyout = so;
  f_res = r; f_extra = ev }), b)

(** val unroll_prog : 'a1 asmOp -> progT -> 'a1 prog -> 'a1 prog * bool **)

let unroll_prog asmop pT p =
  let (fds, b) = map_repeat (unroll_fun asmop pT) p.p_funcs in
  ({ p_funcs = fds; p_globs = p.p_globs; p_extra = p.p_extra }, b)
