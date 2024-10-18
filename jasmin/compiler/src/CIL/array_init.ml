open Datatypes
open Compiler_util
open Expr
open Seq
open Sopn
open Type
open Var0

(** val remove_init_i :
    'a1 asmOp -> (Var.var -> bool) -> 'a1 instr -> 'a1 instr list **)

let rec remove_init_i asmop is_reg_array i = match i with
| MkI (ii, ir) ->
  (match ir with
   | Cassgn (x, _, _, e) ->
     if is_array_init e
     then let t0 =
            match x with
            | Lvar x0 -> is_reg_array x0.v_var
            | Lasub (_, _, _, x0, _) -> is_reg_array x0.v_var
            | _ -> true
          in
          if t0 then [] else i :: []
     else i :: []
   | Cif (e, c1, c2) ->
     let c3 =
       foldr (fun i0 c -> cat (remove_init_i asmop is_reg_array i0) c) [] c1
     in
     let c4 =
       foldr (fun i0 c -> cat (remove_init_i asmop is_reg_array i0) c) [] c2
     in
     (MkI (ii, (Cif (e, c3, c4)))) :: []
   | Cfor (x, r, c) ->
     let c0 =
       foldr (fun i0 c0 -> cat (remove_init_i asmop is_reg_array i0) c0) [] c
     in
     (MkI (ii, (Cfor (x, r, c0)))) :: []
   | Cwhile (a, c, e, c') ->
     let c0 =
       foldr (fun i0 c0 -> cat (remove_init_i asmop is_reg_array i0) c0) [] c
     in
     let c'0 =
       foldr (fun i0 c1 -> cat (remove_init_i asmop is_reg_array i0) c1) [] c'
     in
     (MkI (ii, (Cwhile (a, c0, e, c'0)))) :: []
   | _ -> i :: [])

(** val remove_init_c :
    'a1 asmOp -> (Var.var -> bool) -> 'a1 instr list -> 'a1 instr list **)

let remove_init_c asmop is_reg_array c =
  foldr (fun i c0 -> cat (remove_init_i asmop is_reg_array i) c0) [] c

(** val remove_init_fd :
    'a1 asmOp -> (Var.var -> bool) -> progT -> 'a1 fundef -> ('a1,
    extra_fun_t) _fundef **)

let remove_init_fd asmop is_reg_array _ fd =
  { f_info = fd.f_info; f_tyin = fd.f_tyin; f_params = fd.f_params; f_body =
    (remove_init_c asmop is_reg_array fd.f_body); f_tyout = fd.f_tyout;
    f_res = fd.f_res; f_extra = fd.f_extra }

(** val remove_init_prog :
    'a1 asmOp -> (Var.var -> bool) -> progT -> 'a1 prog -> 'a1 prog **)

let remove_init_prog asmop is_reg_array pT p =
  map_prog asmop pT (remove_init_fd asmop is_reg_array pT) p

(** val add_init_c :
    'a1 asmOp -> (SvExtra.Sv.t -> 'a1 instr -> 'a1 instr list * SvExtra.Sv.t)
    -> SvExtra.Sv.t -> 'a1 instr list -> 'a1 instr list * SvExtra.Sv.t **)

let rec add_init_c asmop add_init_i0 i = function
| [] -> ([], i)
| i0 :: c0 ->
  let (i1, i2) = add_init_i0 i i0 in
  let (c1, i3) = add_init_c asmop add_init_i0 i2 c0 in ((cat i1 c1), i3)

(** val add_init_aux :
    'a1 asmOp -> instr_info -> Var.var -> 'a1 instr list -> 'a1 instr list **)

let add_init_aux _ ii x c =
  match Var.vtype x with
  | Coq_sarr n ->
    if negb (is_ptr x)
    then let x0 = { v_var = x; v_info = dummy_var_info } in
         (MkI (ii, (Cassgn ((Lvar x0), AT_none, (Coq_sarr n), (Parr_init
         n))))) :: c
    else c
  | _ -> c

(** val add_init :
    'a1 asmOp -> instr_info -> SvExtra.Sv.t -> SvExtra.Sv.t -> 'a1 instr ->
    'a1 instr list **)

let add_init asmop ii i extra i0 =
  SvExtra.Sv.fold (Obj.magic add_init_aux asmop ii) (SvExtra.Sv.diff extra i)
    (i0 :: [])

(** val add_init_i :
    'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr -> 'a1 instr list * SvExtra.Sv.t **)

let rec add_init_i asmop i i0 = match i0 with
| MkI (ii, ir) ->
  (match ir with
   | Cif (e, c1, c2) ->
     let (c3, i1) = add_init_c asmop (add_init_i asmop) i c1 in
     let (c4, i2) = add_init_c asmop (add_init_i asmop) i c2 in
     let extra =
       SvExtra.Sv.union (read_e e)
         (SvExtra.Sv.union (SvExtra.Sv.diff i1 i2) (SvExtra.Sv.diff i2 i1))
     in
     let i3 = MkI (ii, (Cif (e, c3, c4))) in
     ((add_init asmop ii i extra i3), (SvExtra.Sv.union i1 i2))
   | _ ->
     let wi = write_i asmop ir in
     let ri = read_i asmop ir in
     let extra = SvExtra.Sv.union wi ri in
     ((add_init asmop (ii_with_location ii) i extra i0),
     (SvExtra.Sv.union i wi)))

(** val add_init_fd :
    'a1 asmOp -> progT -> 'a1 fundef -> ('a1, extra_fun_t) _fundef **)

let add_init_fd asmop _ fd =
  let i = vrvs (map (fun i -> Lvar i) fd.f_params) in
  let f_body0 = fst (add_init_c asmop (add_init_i asmop) i fd.f_body) in
  { f_info = fd.f_info; f_tyin = fd.f_tyin; f_params = fd.f_params; f_body =
  f_body0; f_tyout = fd.f_tyout; f_res = fd.f_res; f_extra = fd.f_extra }

(** val add_init_prog : 'a1 asmOp -> progT -> 'a1 prog -> 'a1 prog **)

let add_init_prog asmop pT p =
  map_prog asmop pT (add_init_fd asmop pT) p
