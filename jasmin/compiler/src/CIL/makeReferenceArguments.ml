open Datatypes
open Hexadecimal
open HexadecimalString
open String0
open Compiler_util
open Expr
open Seq
open Sopn
open Syscall
open Type
open Utils0
open Var0

module E =
 struct
  (** val pass : char list **)

  let pass =
    'm'::('a'::('k'::('e'::(' '::('r'::('e'::('f'::('e'::('r'::('e'::('n'::('c'::('e'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::[])))))))))))))))))))))))

  (** val make_ref_error : instr_info -> char list -> pp_error_loc **)

  let make_ref_error =
    pp_internal_error_s_at pass
 end

(** val with_id :
    (instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident) ->
    instr_info -> uint -> var_info -> Ident.Ident.name -> stype -> var_i **)

let with_id fresh_reg_ptr ii sfx vi id ty =
  let id0 =
    Ident.Ident.name_of_string
      (append (Ident.Ident.string_of_name id) (NilEmpty.string_of_uint sfx))
  in
  { v_var = { Var.vtype = ty; Var.vname = (fresh_reg_ptr ii id0 ty) };
  v_info = vi }

(** val is_reg_ptr_expr :
    (instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident) ->
    instr_info -> uint -> bool -> Ident.Ident.name -> stype -> pexpr -> var_i
    option **)

let is_reg_ptr_expr fresh_reg_ptr ii sfx doit id ty = function
| Pvar x' ->
  if (&&) doit ((||) (is_glob x') (negb (is_reg_ptr x'.gv.v_var)))
  then Some (with_id fresh_reg_ptr ii sfx x'.gv.v_info id ty)
  else None
| Psub (_, _, _, x', _) ->
  if doit
  then Some (with_id fresh_reg_ptr ii sfx x'.gv.v_info id ty)
  else None
| _ -> None

(** val is_reg_ptr_lval :
    (instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident) ->
    instr_info -> uint -> bool -> Ident.Ident.name -> stype -> lval -> var_i
    option **)

let is_reg_ptr_lval fresh_reg_ptr ii sfx doit id ty = function
| Lvar x' ->
  if (&&) doit (negb (is_reg_ptr x'.v_var))
  then Some (with_id fresh_reg_ptr ii sfx x'.v_info id ty)
  else None
| Lasub (_, _, _, x', _) ->
  if doit then Some (with_id fresh_reg_ptr ii sfx x'.v_info id ty) else None
| _ -> None

(** val make_prologue :
    'a1 asmOp -> (instr_info -> Ident.Ident.name -> stype ->
    Ident.Ident.ident) -> instr_info -> SvExtra.Sv.t -> uint ->
    ((bool * Ident.Ident.name) * stype) list -> pexpr list -> (pp_error_loc,
    'a1 instr list * pexpr list) result **)

let rec make_prologue asmop fresh_reg_ptr ii x ctr xtys es =
  match xtys with
  | [] ->
    (match es with
     | [] -> Ok ([], [])
     | _ :: _ ->
       Error
         (E.make_ref_error ii
           ('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::(' '::('('::('p'::('r'::('o'::('l'::('o'::('g'::('u'::('e'::(')'::[])))))))))))))))))))))))))
  | y :: xtys0 ->
    let (y0, ty) = y in
    let (doit, id) = y0 in
    (match es with
     | [] ->
       Error
         (E.make_ref_error ii
           ('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::(' '::('('::('p'::('r'::('o'::('l'::('o'::('g'::('u'::('e'::(')'::[]))))))))))))))))))))))))
     | e :: es0 ->
       (match is_reg_ptr_expr fresh_reg_ptr ii ctr doit id ty e with
        | Some y1 ->
          if negb (SvExtra.Sv.mem (Obj.magic y1.v_var) x)
          then (match make_prologue asmop fresh_reg_ptr ii
                        (SvExtra.Sv.add (Obj.magic y1.v_var) x)
                        (Little.succ ctr) xtys0 es0 with
                | Ok x0 ->
                  let (p, es') = x0 in
                  Ok (((MkI (ii, (Cassgn ((Lvar y1), AT_rename, ty,
                  e)))) :: p), ((coq_Plvar y1) :: es'))
                | Error s -> Error s)
          else let s =
                 E.make_ref_error ii
                   ('b'::('a'::('d'::(' '::('f'::('r'::('e'::('s'::('h'::(' '::('i'::('d'::(' '::('('::('p'::('r'::('o'::('l'::('o'::('g'::('u'::('e'::(')'::[])))))))))))))))))))))))
               in
               Error s
        | None ->
          (match make_prologue asmop fresh_reg_ptr ii x ctr xtys0 es0 with
           | Ok x0 -> let (p, es') = x0 in Ok (p, (e :: es'))
           | Error s -> Error s)))

type pseudo_instr =
| PI_lv of lval
| PI_i of lval * stype * var_i

(** val make_pseudo_epilogue :
    (instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident) ->
    instr_info -> SvExtra.Sv.t -> uint -> ((bool * Ident.Ident.name) * stype)
    list -> lval list -> (pp_error_loc, pseudo_instr list) result **)

let rec make_pseudo_epilogue fresh_reg_ptr ii x ctr xtys rs =
  match xtys with
  | [] ->
    (match rs with
     | [] -> Ok []
     | _ :: _ ->
       Error
         (E.make_ref_error ii
           ('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::(' '::('('::('e'::('p'::('i'::('l'::('o'::('g'::('u'::('e'::(')'::[])))))))))))))))))))))))))
  | y :: xtys0 ->
    let (y0, ty) = y in
    let (doit, id) = y0 in
    (match rs with
     | [] ->
       Error
         (E.make_ref_error ii
           ('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::(' '::('('::('e'::('p'::('i'::('l'::('o'::('g'::('u'::('e'::(')'::[]))))))))))))))))))))))))
     | r :: rs0 ->
       (match is_reg_ptr_lval fresh_reg_ptr ii ctr doit id ty r with
        | Some y1 ->
          if negb (SvExtra.Sv.mem (Obj.magic y1.v_var) x)
          then (match make_pseudo_epilogue fresh_reg_ptr ii x
                        (Little.succ ctr) xtys0 rs0 with
                | Ok x0 ->
                  Ok ((PI_lv (Lvar y1)) :: ((PI_i (r, ty, y1)) :: x0))
                | Error s -> Error s)
          else let s =
                 E.make_ref_error ii
                   ('b'::('a'::('d'::(' '::('f'::('r'::('e'::('s'::('h'::(' '::('i'::('d'::(' '::('('::('e'::('p'::('i'::('l'::('o'::('g'::('u'::('e'::(')'::[])))))))))))))))))))))))
               in
               Error s
        | None ->
          (match make_pseudo_epilogue fresh_reg_ptr ii x ctr xtys0 rs0 with
           | Ok x0 -> Ok ((PI_lv r) :: x0)
           | Error s -> Error s)))

(** val mk_ep_i :
    'a1 asmOp -> instr_info -> lval -> stype -> var_i -> 'a1 instr **)

let mk_ep_i _ ii r ty y =
  MkI (ii, (Cassgn (r, AT_rename, ty, (coq_Plvar y))))

(** val wf_lv : lval -> bool **)

let wf_lv = function
| Lvar _ -> true
| Lasub (_, _, _, _, e) -> negb (use_mem e)
| _ -> false

(** val swapable :
    'a1 asmOp -> instr_info -> pseudo_instr list -> (pp_error_loc, lval
    list * 'a1 instr list) result **)

let rec swapable asmop ii = function
| [] -> Ok ([], [])
| p0 :: pis0 ->
  (match p0 with
   | PI_lv lv ->
     (match swapable asmop ii pis0 with
      | Ok x -> let (lvs, ep) = x in Ok ((lv :: lvs), ep)
      | Error s -> Error s)
   | PI_i (r, ty, y) ->
     (match swapable asmop ii pis0 with
      | Ok x ->
        let (lvs, ep) = x in
        let i = mk_ep_i asmop ii r ty y in
        if SvExtra.disjoint (read_rvs lvs) (write_I asmop i)
        then if SvExtra.disjoint (vrvs lvs)
                  (SvExtra.Sv.union (write_I asmop i) (read_I asmop i))
             then if wf_lv r
                  then Ok (lvs, (i :: ep))
                  else let s =
                         E.make_ref_error ii
                           ('c'::('a'::('n'::('n'::('o'::('t'::(' '::('s'::('w'::('a'::('p'::(' '::('3'::[])))))))))))))
                       in
                       Error s
             else let s =
                    E.make_ref_error ii
                      ('c'::('a'::('n'::('n'::('o'::('t'::(' '::('s'::('w'::('a'::('p'::(' '::('2'::[])))))))))))))
                  in
                  Error s
        else let s =
               E.make_ref_error ii
                 ('c'::('a'::('n'::('n'::('o'::('t'::(' '::('s'::('w'::('a'::('p'::(' '::('1'::[])))))))))))))
             in
             Error s
      | Error s -> Error s))

(** val make_epilogue :
    'a1 asmOp -> (instr_info -> Ident.Ident.name -> stype ->
    Ident.Ident.ident) -> instr_info -> SvExtra.Sv.t ->
    ((bool * Ident.Ident.name) * stype) list -> lval list -> (pp_error_loc,
    lval list * 'a1 instr list) result **)

let make_epilogue asmop fresh_reg_ptr ii x xtys rs =
  match make_pseudo_epilogue fresh_reg_ptr ii x Nil xtys rs with
  | Ok x0 -> swapable asmop ii x0
  | Error s -> Error s

(** val update_c :
    'a1 asmOp -> ('a1 instr -> 'a1 instr list cexec) -> 'a1 instr list ->
    (pp_error_loc, 'a1 instr list) result **)

let update_c _ =
  conc_mapM

(** val mk_info : var_i -> stype -> (bool * Ident.Ident.name) * stype **)

let mk_info x ty =
  (((is_reg_ptr x.v_var), (Ident.Ident.id_name (Var.vname x.v_var))), ty)

(** val get_sig :
    'a1 asmOp -> 'a1 uprog -> funname -> ((bool * Ident.Ident.name) * stype)
    list * ((bool * Ident.Ident.name) * stype) list **)

let get_sig _ p fn =
  match get_fundef p.p_funcs fn with
  | Some fd ->
    ((map2 mk_info fd.f_params fd.f_tyin), (map2 mk_info fd.f_res fd.f_tyout))
  | None -> ([], [])

(** val get_syscall_sig :
    BinNums.positive Syscall_t.syscall_t ->
    ((bool * Ident.Ident.name) * stype)
    list * ((bool * Ident.Ident.name) * stype) list **)

let get_syscall_sig o =
  ((map (fun ty -> (((is_sarr ty),
     (Ident.Ident.name_of_string ('_'::('_'::('p'::('_'::('_'::[]))))))),
     ty)) (syscall_sig_u o).scs_tin),
    (map (fun ty -> (((is_sarr ty),
      (Ident.Ident.name_of_string ('_'::('_'::('p'::('_'::('_'::[]))))))),
      ty)) (syscall_sig_u o).scs_tout))

(** val update_i :
    'a1 asmOp -> (instr_info -> Ident.Ident.name -> stype ->
    Ident.Ident.ident) -> 'a1 uprog -> SvExtra.Sv.t -> 'a1 instr -> 'a1 instr
    list cexec **)

let rec update_i asmop fresh_reg_ptr p x i = match i with
| MkI (ii, ir) ->
  (match ir with
   | Csyscall (xs, o, es) ->
     let (params, returns) = get_syscall_sig o in
     (match make_prologue asmop fresh_reg_ptr ii x Nil params es with
      | Ok x0 ->
        let (prologue, es0) = x0 in
        (match make_epilogue asmop fresh_reg_ptr ii x returns xs with
         | Ok x1 ->
           let (xs0, epilogue) = x1 in
           Ok
           (cat prologue ((MkI (ii, (Csyscall (xs0, o, es0)))) :: epilogue))
         | Error s -> Error s)
      | Error s -> Error s)
   | Cif (b, c1, c2) ->
     (match update_c asmop (update_i asmop fresh_reg_ptr p x) c1 with
      | Ok x0 ->
        (match update_c asmop (update_i asmop fresh_reg_ptr p x) c2 with
         | Ok x1 -> Ok ((MkI (ii, (Cif (b, x0, x1)))) :: [])
         | Error s -> Error s)
      | Error s -> Error s)
   | Cfor (x0, r, c) ->
     (match update_c asmop (update_i asmop fresh_reg_ptr p x) c with
      | Ok x1 -> Ok ((MkI (ii, (Cfor (x0, r, x1)))) :: [])
      | Error s -> Error s)
   | Cwhile (a, c, e, c') ->
     (match update_c asmop (update_i asmop fresh_reg_ptr p x) c with
      | Ok x0 ->
        (match update_c asmop (update_i asmop fresh_reg_ptr p x) c' with
         | Ok x1 -> Ok ((MkI (ii, (Cwhile (a, x0, e, x1)))) :: [])
         | Error s -> Error s)
      | Error s -> Error s)
   | Ccall (xs, fn, es) ->
     let (params, returns) = get_sig asmop p fn in
     (match make_prologue asmop fresh_reg_ptr ii x Nil params es with
      | Ok x0 ->
        let (prologue, es0) = x0 in
        (match make_epilogue asmop fresh_reg_ptr ii x returns xs with
         | Ok x1 ->
           let (xs0, epilogue) = x1 in
           Ok (cat prologue ((MkI (ii, (Ccall (xs0, fn, es0)))) :: epilogue))
         | Error s -> Error s)
      | Error s -> Error s)
   | _ -> Ok (i :: []))

(** val update_fd :
    'a1 asmOp -> (instr_info -> Ident.Ident.name -> stype ->
    Ident.Ident.ident) -> 'a1 uprog -> 'a1 ufundef -> (pp_error_loc, ('a1,
    extra_fun_t) _fundef) result **)

let update_fd asmop fresh_reg_ptr p fd =
  let body = fd.f_body in
  let write = write_c asmop body in
  let read = read_c asmop body in
  let returns = read_es (map coq_Plvar fd.f_res) in
  let x = SvExtra.Sv.union returns (SvExtra.Sv.union write read) in
  (match update_c asmop (update_i asmop fresh_reg_ptr p x) body with
   | Ok x0 -> Ok (with_body asmop fd x0)
   | Error s -> Error s)

(** val makereference_prog :
    'a1 asmOp -> (instr_info -> Ident.Ident.name -> stype ->
    Ident.Ident.ident) -> 'a1 uprog -> 'a1 uprog cexec **)

let makereference_prog asmop fresh_reg_ptr p =
  match map_cfprog_gen (fun x -> x.f_info) (update_fd asmop fresh_reg_ptr p)
          p.p_funcs with
  | Ok x -> Ok { p_funcs = x; p_globs = p.p_globs; p_extra = p.p_extra }
  | Error s -> Error s
