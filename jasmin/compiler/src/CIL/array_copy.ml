open BinInt
open BinNums
open Compiler_util
open Eqtype
open Expr
open Pseudo_operator
open Seq
open Sopn
open Type
open Utils0
open Var0
open Warray_
open Word0
open Wsize

module E =
 struct
  (** val pass : char list **)

  let pass =
    'a'::('r'::('r'::('a'::('y'::(' '::('c'::('o'::('p'::('y'::[])))))))))

  (** val error : pp_error_loc **)

  let error =
    pp_internal_error_s pass
      ('f'::('r'::('e'::('s'::('h'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::('s'::(' '::('a'::('r'::('e'::(' '::('n'::('o'::('t'::(' '::('f'::('r'::('e'::('s'::('h'::(' '::('.'::('.'::('.'::[])))))))))))))))))))))))))))))))))
 end

(** val direct_copy :
    'a1 asmOp -> wsize -> var_i -> gvar -> pexpr -> 'a1 instr_r list **)

let direct_copy _ ws x y i =
  (Cassgn ((Laset (AAscale, ws, x, i)), AT_none, (Coq_sword ws), (Pget
    (AAscale, ws, y, i)))) :: []

(** val tmp_var : (wsize -> Ident.Ident.ident) -> wsize -> Var.var **)

let tmp_var fresh_temporary ws =
  { Var.vtype = (Coq_sword ws); Var.vname = (fresh_temporary ws) }

(** val indirect_copy :
    'a1 asmOp -> (wsize -> Ident.Ident.ident) -> wsize -> var_i -> gvar ->
    pexpr -> 'a1 instr_r list **)

let indirect_copy _ fresh_temporary ws x y i =
  let tmp = { v_var = (tmp_var fresh_temporary ws); v_info = x.v_info } in
  (Cassgn ((Lvar tmp), AT_none, (Coq_sword ws), (Pget (AAscale, ws, y,
  i)))) :: ((Cassgn ((Laset (AAscale, ws, x, i)), AT_none, (Coq_sword ws),
  (Pvar (mk_lvar tmp)))) :: [])

(** val needs_temporary : Var.var -> Var.var -> bool **)

let needs_temporary x y =
  (&&) (is_var_in_memory x) (is_var_in_memory y)

(** val array_copy :
    'a1 asmOp -> Ident.Ident.ident -> (wsize -> Ident.Ident.ident) ->
    instr_info -> var_i -> wsize -> positive -> gvar -> 'a1 instr list **)

let array_copy asmop fresh_counter fresh_temporary ii x ws n y =
  let i = { v_var = { Var.vtype = Coq_sint; Var.vname = fresh_counter };
    v_info = x.v_info }
  in
  let ei = Pvar (mk_lvar i) in
  let sz = Z.to_pos (Z.mul (wsize_size ws) (Zpos n)) in
  let pre =
    if (||) (eq_gvar (mk_lvar x) y) (is_ptr x.v_var)
    then Copn ([], AT_none, (sopn_nop asmop), [])
    else Cassgn ((Lvar x), AT_none, (Coq_sarr sz), (Parr_init sz))
  in
  (MkI (ii, pre)) :: ((MkI (ii, (Cfor (i, ((UpTo, (Pconst Z0)), (Pconst (Zpos
  n))),
  (map (fun i0 -> MkI (ii, i0))
    (if needs_temporary x.v_var y.gv.v_var
     then indirect_copy asmop fresh_temporary ws x y ei
     else direct_copy asmop ws x y ei)))))) :: [])

(** val array_copy_c :
    'a1 asmOp -> ('a1 instr -> 'a1 instr list cexec) -> 'a1 instr list -> 'a1
    instr list cexec **)

let array_copy_c _ =
  conc_mapM

(** val is_copy : 'a1 asmOp -> 'a1 sopn -> (wsize * positive) option **)

let is_copy _ = function
| Opseudo_op p0 -> (match p0 with
                    | Ocopy (ws, p) -> Some (ws, p)
                    | _ -> None)
| _ -> None

(** val is_Pvar : pexpr list -> gvar option **)

let is_Pvar = function
| [] -> None
| y :: l ->
  (match y with
   | Pvar x -> (match l with
                | [] -> Some x
                | _ :: _ -> None)
   | _ -> None)

(** val is_Lvar : lval list -> var_i option **)

let is_Lvar = function
| [] -> None
| y :: l ->
  (match y with
   | Lvar x -> (match l with
                | [] -> Some x
                | _ :: _ -> None)
   | _ -> None)

(** val array_copy_i :
    'a1 asmOp -> Ident.Ident.ident -> (wsize -> Ident.Ident.ident) -> 'a1
    instr -> 'a1 instr list cexec **)

let rec array_copy_i asmop fresh_counter fresh_temporary i = match i with
| MkI (ii, id) ->
  (match id with
   | Copn (xs, _, o, es) ->
     (match is_copy asmop o with
      | Some p ->
        let (ws, n) = p in
        (match is_Pvar es with
         | Some y ->
           (match is_Lvar xs with
            | Some x ->
              if eq_op stype_eqType (Obj.magic Var.vtype x.v_var)
                   (Obj.magic (Coq_sarr (Z.to_pos (arr_size ws n))))
              then Ok
                     (array_copy asmop fresh_counter fresh_temporary ii x ws
                       n y)
              else let s =
                     pp_internal_error_s_at E.pass ii
                       ('b'::('a'::('d'::(' '::('t'::('y'::('p'::('e'::(' '::('f'::('o'::('r'::(' '::('c'::('o'::('p'::('y'::[])))))))))))))))))
                   in
                   Error s
            | None ->
              Error
                (pp_internal_error_s_at E.pass ii
                  ('c'::('o'::('p'::('y'::(' '::('d'::('e'::('s'::('t'::('i'::('n'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('v'::('a'::('r'::[])))))))))))))))))))))))))))))))
         | None ->
           Error
             (pp_internal_error_s_at E.pass ii
               ('c'::('o'::('p'::('y'::(' '::('s'::('o'::('u'::('r'::('c'::('e'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('v'::('a'::('r'::[]))))))))))))))))))))))))))
      | None -> Ok (i :: []))
   | Cif (e, c1, c2) ->
     (match array_copy_c asmop
              (array_copy_i asmop fresh_counter fresh_temporary) c1 with
      | Ok x ->
        (match array_copy_c asmop
                 (array_copy_i asmop fresh_counter fresh_temporary) c2 with
         | Ok x0 -> Ok ((MkI (ii, (Cif (e, x, x0)))) :: [])
         | Error s -> Error s)
      | Error s -> Error s)
   | Cfor (i0, r, c) ->
     (match array_copy_c asmop
              (array_copy_i asmop fresh_counter fresh_temporary) c with
      | Ok x -> Ok ((MkI (ii, (Cfor (i0, r, x)))) :: [])
      | Error s -> Error s)
   | Cwhile (a, c1, e, c2) ->
     (match array_copy_c asmop
              (array_copy_i asmop fresh_counter fresh_temporary) c1 with
      | Ok x ->
        (match array_copy_c asmop
                 (array_copy_i asmop fresh_counter fresh_temporary) c2 with
         | Ok x0 -> Ok ((MkI (ii, (Cwhile (a, x, e, x0)))) :: [])
         | Error s -> Error s)
      | Error s -> Error s)
   | _ -> Ok (i :: []))

(** val array_copy_fd :
    'a1 asmOp -> Ident.Ident.ident -> (wsize -> Ident.Ident.ident) -> progT
    -> 'a1 fundef -> (pp_error_loc, ('a1, extra_fun_t) _fundef) result **)

let array_copy_fd asmop fresh_counter fresh_temporary _ f =
  let { f_info = fi; f_tyin = tyin; f_params = params; f_body = c; f_tyout =
    tyout; f_res = res; f_extra = ev } = f
  in
  (match array_copy_c asmop
           (array_copy_i asmop fresh_counter fresh_temporary) c with
   | Ok x ->
     Ok { f_info = fi; f_tyin = tyin; f_params = params; f_body = x;
       f_tyout = tyout; f_res = res; f_extra = ev }
   | Error s -> Error s)

(** val array_copy_prog :
    'a1 asmOp -> Ident.Ident.ident -> (wsize -> Ident.Ident.ident) -> progT
    -> 'a1 prog -> (pp_error_loc, ('a1, extra_fun_t, extra_prog_t) _prog)
    result **)

let array_copy_prog asmop fresh_counter fresh_temporary pT p =
  let v = vars_p asmop pT p.p_funcs in
  let fresh =
    SvExtra.Sv.add
      (Obj.magic { Var.vtype = Coq_sint; Var.vname = fresh_counter })
      (SvExtra.sv_of_list (Obj.magic tmp_var fresh_temporary) wsizes)
  in
  if SvExtra.disjoint fresh v
  then (match map_cfprog_gen (fun x -> x.f_info)
                (array_copy_fd asmop fresh_counter fresh_temporary pT)
                p.p_funcs with
        | Ok x -> Ok { p_funcs = x; p_globs = p.p_globs; p_extra = p.p_extra }
        | Error s -> Error s)
  else Error E.error
