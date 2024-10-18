open Datatypes
open Allocation
open Compiler_util
open Expr
open Sem_type
open Seq
open Sopn
open Type
open Utils0
open Var0

module E =
 struct
  (** val pass : char list **)

  let pass =
    'i'::('n'::('l'::('i'::('n'::('i'::('n'::('g'::[])))))))

  (** val inline_error : pp_error -> pp_error_loc **)

  let inline_error msg =
    { pel_msg = msg; pel_fn = None; pel_fi = None; pel_ii = None; pel_vi =
      None; pel_pass = (Some pass); pel_internal = true }
 end

(** val get_flag : lval -> assgn_tag -> assgn_tag **)

let get_flag x flag =
  match x with
  | Lvar x0 -> if is_inline_var x0.v_var then AT_inline else flag
  | _ -> flag

(** val assgn_tuple :
    'a1 asmOp -> instr_info -> lval list -> assgn_tag -> stype list -> pexpr
    list -> 'a1 instr list **)

let assgn_tuple _ iinfo xs flag tys es =
  let assgn = fun xe -> MkI (iinfo, (Cassgn ((fst xe),
    (get_flag (fst xe) flag), (fst (snd xe)), (snd (snd xe)))))
  in
  map assgn (zip xs (zip tys es))

(** val inline_c :
    'a1 asmOp -> ('a1 instr -> SvExtra.Sv.t -> (SvExtra.Sv.t * 'a1 instr
    list) cexec) -> 'a1 instr list -> SvExtra.Sv.t -> (pp_error_loc,
    SvExtra.Sv.t * 'a1 instr list) result **)

let inline_c _ inline_i0 c s =
  foldr (fun i r ->
    match r with
    | Ok x ->
      (match inline_i0 i (fst x) with
       | Ok x0 -> Ok ((fst x0), (cat (snd x0) (snd x)))
       | Error s0 -> Error s0)
    | Error s0 -> Error s0) (Ok (s, [])) c

(** val locals_p : 'a1 asmOp -> 'a1 ufundef -> SvExtra.Sv.t **)

let locals_p asmop fd =
  let s = read_es (map coq_Plvar fd.f_res) in
  let w = write_c_rec asmop s fd.f_body in
  let r = read_c_rec asmop w fd.f_body in
  vrvs_rec r (map (fun x -> Lvar x) fd.f_params)

(** val check_rename :
    coq_WithSubWord -> 'a1 asmOp -> funname -> 'a1 ufundef -> 'a1 ufundef ->
    SvExtra.Sv.t -> (pp_error_loc, unit) result **)

let check_rename wsw asmop f fd1 fd2 s =
  match check_ufundef wsw asmop (Obj.magic ()) (Obj.magic ()) (f, fd1) (f,
          fd2) () with
  | Ok _ ->
    let s2 = locals_p asmop fd2 in
    if SvExtra.disjoint s s2
    then Ok ()
    else Error
           (E.inline_error (PPEstring
             ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('f'::('r'::('e'::('s'::('h'::('i'::('n'::('g'::(' '::('i'::('n'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))))))
  | Error s0 -> Error s0

(** val get_fun :
    'a1 asmOp -> 'a1 ufun_decls -> funname -> (pp_error_loc, 'a1 fundef)
    result **)

let get_fun _ p f =
  match get_fundef p f with
  | Some fd -> Ok fd
  | None ->
    Error
      (E.inline_error
        (pp_box ((PPEstring
          ('U'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::[]))))))))))))))))) :: ((PPEfunname
          f) :: []))))

(** val inline_i :
    coq_WithSubWord -> 'a1 asmOp -> (instr_info -> funname -> 'a1 ufundef ->
    'a1 ufundef) -> 'a1 ufun_decls -> 'a1 instr -> SvExtra.Sv.t ->
    (SvExtra.Sv.t * 'a1 instr list) cexec **)

let rec inline_i wsw asmop rename_fd p i x =
  let MkI (iinfo, ir) = i in
  (match ir with
   | Cif (e, c1, c2) ->
     (match inline_c asmop (inline_i wsw asmop rename_fd p) c1 x with
      | Ok x0 ->
        (match inline_c asmop (inline_i wsw asmop rename_fd p) c2 x with
         | Ok x1 ->
           Ok ((read_e_rec (SvExtra.Sv.union (fst x0) (fst x1)) e), ((MkI
             (iinfo, (Cif (e, (snd x0), (snd x1))))) :: []))
         | Error s -> Error s)
      | Error s -> Error s)
   | Cfor (x0, r, c) ->
     let x1 = SvExtra.Sv.union (read_i asmop ir) x in
     (match inline_c asmop (inline_i wsw asmop rename_fd p) c x1 with
      | Ok x2 -> Ok (x1, ((MkI (iinfo, (Cfor (x0, r, (snd x2))))) :: []))
      | Error s -> Error s)
   | Cwhile (a, c, e, c') ->
     let x0 = SvExtra.Sv.union (read_i asmop ir) x in
     (match inline_c asmop (inline_i wsw asmop rename_fd p) c x0 with
      | Ok x1 ->
        (match inline_c asmop (inline_i wsw asmop rename_fd p) c' x0 with
         | Ok x2 ->
           Ok (x0, ((MkI (iinfo, (Cwhile (a, (snd x1), e, (snd x2))))) :: []))
         | Error s -> Error s)
      | Error s -> Error s)
   | Ccall (xs, f, es) ->
     let x0 = SvExtra.Sv.union (read_i asmop ir) x in
     if ii_is_inline iinfo
     then (match add_iinfo iinfo (get_fun asmop p f) with
           | Ok x1 ->
             let fd' = rename_fd iinfo f x1 in
             (match add_iinfo iinfo
                      (check_rename wsw asmop f x1 fd'
                        (SvExtra.Sv.union (vrvs xs) x0)) with
              | Ok _ ->
                let ii = ii_with_location iinfo in
                let rename_args =
                  assgn_tuple asmop ii (map (fun x2 -> Lvar x2) fd'.f_params)
                    AT_rename fd'.f_tyin es
                in
                let rename_res =
                  assgn_tuple asmop ii xs AT_rename fd'.f_tyout
                    (map coq_Plvar fd'.f_res)
                in
                Ok (x0, (cat rename_args (cat fd'.f_body rename_res)))
              | Error s -> Error s)
           | Error s -> Error s)
     else Ok (x0, (i :: []))
   | _ -> Ok ((SvExtra.Sv.union (read_i asmop ir) x), (i :: [])))

(** val inline_fd :
    coq_WithSubWord -> 'a1 asmOp -> (instr_info -> funname -> 'a1 ufundef ->
    'a1 ufundef) -> 'a1 ufun_decls -> 'a1 ufundef -> (pp_error_loc, ('a1,
    extra_fun_t) _fundef) result **)

let inline_fd wsw asmop rename_fd p fd =
  let { f_info = ii; f_tyin = tyin; f_params = params; f_body = c; f_tyout =
    tyout; f_res = res; f_extra = ef } = fd
  in
  let s = read_es (map coq_Plvar res) in
  (match inline_c asmop (inline_i wsw asmop rename_fd p) c s with
   | Ok x ->
     Ok { f_info = ii; f_tyin = tyin; f_params = params; f_body = (snd x);
       f_tyout = tyout; f_res = res; f_extra = ef }
   | Error s0 -> Error s0)

(** val inline_fd_cons :
    coq_WithSubWord -> 'a1 asmOp -> (instr_info -> funname -> 'a1 ufundef ->
    'a1 ufundef) -> (funname * 'a1 ufundef) -> 'a1 ufun_decls cexec ->
    (pp_error_loc, (funname * 'a1 fundef) list) result **)

let inline_fd_cons wsw asmop rename_fd ffd = function
| Ok x ->
  let f = fst ffd in
  (match add_funname f
           (add_finfo (snd ffd).f_info
             (inline_fd wsw asmop rename_fd x (snd ffd))) with
   | Ok x0 -> Ok ((f, x0) :: x)
   | Error s -> Error s)
| Error s -> Error s

(** val inline_prog :
    coq_WithSubWord -> 'a1 asmOp -> (instr_info -> funname -> 'a1 ufundef ->
    'a1 ufundef) -> 'a1 ufun_decls -> 'a1 ufun_decls cexec **)

let inline_prog wsw asmop rename_fd p =
  foldr (inline_fd_cons wsw asmop rename_fd) (Ok []) p

(** val inline_prog_err :
    coq_WithSubWord -> 'a1 asmOp -> (instr_info -> funname -> 'a1 ufundef ->
    'a1 ufundef) -> 'a1 uprog -> (pp_error_loc, ('a1, extra_fun_t,
    extra_prog_t) _prog) result **)

let inline_prog_err wsw asmop rename_fd p =
  if uniq funname_eqType (map (fun x -> fst (Obj.magic x)) p.p_funcs)
  then (match inline_prog wsw asmop rename_fd p.p_funcs with
        | Ok x -> Ok { p_funcs = x; p_globs = p.p_globs; p_extra = p.p_extra }
        | Error s -> Error s)
  else Error
         (E.inline_error (PPEstring
           ('t'::('w'::('o'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('d'::('e'::('c'::('l'::('a'::('r'::('a'::('t'::('i'::('o'::('n'::('s'::(' '::('w'::('i'::('t'::('h'::(' '::('t'::('h'::('e'::(' '::('s'::('a'::('m'::('e'::(' '::('n'::('a'::('m'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))))
