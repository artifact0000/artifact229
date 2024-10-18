open Datatypes
open Compiler_util
open Eqtype
open Expr
open Seq
open Sopn
open Utils0
open Var0

module E =
 struct
  (** val pass : char list **)

  let pass =
    'd'::('e'::('a'::('d'::(' '::('c'::('o'::('d'::('e'::[]))))))))

  (** val ii_loop_iterator : instr_info -> pp_error_loc **)

  let ii_loop_iterator =
    ii_loop_iterator pass

  (** val dead_code_error : char list -> pp_error_loc **)

  let dead_code_error =
    pp_internal_error_s pass
 end

(** val dead_code_c :
    'a1 asmOp -> ('a1 instr -> SvExtra.Sv.t -> (SvExtra.Sv.t * 'a1 instr
    option) cexec) -> 'a1 instr list -> SvExtra.Sv.t -> (SvExtra.Sv.t * 'a1
    instr list) cexec **)

let dead_code_c _ =
  let ocat = fun o c -> match o with
                        | Some i -> i :: c
                        | None -> c in
  (fun dead_code_i0 c s ->
  foldr (fun i r ->
    match r with
    | Ok x ->
      (match dead_code_i0 i (fst x) with
       | Ok x0 -> Ok ((fst x0), (ocat (snd x0) (snd x)))
       | Error s0 -> Error s0)
    | Error s0 -> Error s0) (Ok (s, [])) c)

(** val loop :
    'a1 asmOp -> (SvExtra.Sv.t -> (SvExtra.Sv.t * 'a1 instr list) cexec) ->
    instr_info -> nat -> SvExtra.Sv.t -> SvExtra.Sv.t -> SvExtra.Sv.t ->
    (SvExtra.Sv.t * 'a1 instr list) cexec **)

let rec loop asmop dead_code_c0 ii n rx wx s =
  match n with
  | O -> Error (E.ii_loop_iterator ii)
  | S n0 ->
    (match dead_code_c0 s with
     | Ok x ->
       let (s', c') = x in
       let s'0 = SvExtra.Sv.union rx (SvExtra.Sv.diff s' wx) in
       if SvExtra.Sv.subset s'0 s
       then Ok (s, c')
       else loop asmop dead_code_c0 ii n0 rx wx (SvExtra.Sv.union s s'0)
     | Error s0 -> Error s0)

(** val wloop :
    'a1 asmOp -> (SvExtra.Sv.t -> (SvExtra.Sv.t * (SvExtra.Sv.t * ('a1 instr
    list * 'a1 instr list))) cexec) -> instr_info -> nat -> SvExtra.Sv.t ->
    (SvExtra.Sv.t * ('a1 instr list * 'a1 instr list)) cexec **)

let rec wloop asmop dead_code_c2 ii n s =
  match n with
  | O -> Error (E.ii_loop_iterator ii)
  | S n0 ->
    (match dead_code_c2 s with
     | Ok x ->
       let (s', sic) = x in
       if SvExtra.Sv.subset s' s
       then Ok sic
       else wloop asmop dead_code_c2 ii n0 (SvExtra.Sv.union s s')
     | Error s0 -> Error s0)

(** val check_nop : lval -> pexpr -> bool **)

let check_nop rv e =
  match rv with
  | Lvar x1 ->
    (match e with
     | Pvar x2 ->
       (&&) (is_lvar x2)
         (eq_op Var.var_eqType (Obj.magic x1.v_var) (Obj.magic x2.gv.v_var))
     | _ -> false)
  | _ -> false

(** val check_nop_opn :
    'a1 asmOp -> ('a1 asm_op_t -> bool) -> lval list -> 'a1 sopn -> pexpr
    list -> bool **)

let check_nop_opn _ is_move_op xs o es =
  match xs with
  | [] -> false
  | x :: l ->
    (match l with
     | [] ->
       (match o with
        | Oasm op ->
          (match es with
           | [] -> false
           | e :: l0 ->
             (match l0 with
              | [] -> (&&) (is_move_op op) (check_nop x e)
              | _ :: _ -> false))
        | _ -> false)
     | _ :: _ -> false)

(** val keep_only : 'a1 list -> bool list -> 'a1 list **)

let rec keep_only l = function
| [] -> l
| b :: tokeep0 ->
  (match l with
   | [] -> []
   | x :: l0 -> let l1 = keep_only l0 tokeep0 in if b then x :: l1 else l1)

(** val fn_keep_only :
    (funname -> bool list option) -> funname -> 'a1 list -> 'a1 list **)

let fn_keep_only onfun fn l =
  match onfun fn with
  | Some tokeep -> keep_only l tokeep
  | None -> l

(** val check_keep_only :
    lval list -> bool list -> SvExtra.Sv.t -> (SvExtra.Sv.t * lval list) cexec **)

let rec check_keep_only xs tokeep s =
  match tokeep with
  | [] ->
    (match xs with
     | [] -> Ok (s, [])
     | _ :: _ ->
       Error
         (E.dead_code_error
           ('c'::('h'::('e'::('c'::('k'::('_'::('k'::('e'::('e'::('p'::('_'::('o'::('n'::('l'::('y'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('s'::('i'::('z'::('e'::[]))))))))))))))))))))))))))))))
  | b :: tokeep0 ->
    (match xs with
     | [] ->
       Error
         (E.dead_code_error
           ('c'::('h'::('e'::('c'::('k'::('_'::('k'::('e'::('e'::('p'::('_'::('o'::('n'::('l'::('y'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('s'::('i'::('z'::('e'::[])))))))))))))))))))))))))))))
     | x :: xs0 ->
       (match check_keep_only xs0 tokeep0 s with
        | Ok x0 ->
          let (s0, xs1) = x0 in
          if b
          then Ok ((read_rv_rec (SvExtra.Sv.diff s0 (vrv x)) x), (x :: xs1))
          else let w = vrv x in
               if (&&) (SvExtra.disjoint s0 w) (negb (lv_write_mem x))
               then Ok (s0, xs1)
               else Error
                      (E.dead_code_error
                        ('c'::('h'::('e'::('c'::('k'::('_'::('k'::('e'::('e'::('p'::('_'::('o'::('n'::('l'::('y'::[]))))))))))))))))
        | Error s0 -> Error s0))

(** val dead_code_i :
    'a1 asmOp -> ('a1 asm_op_t -> bool) -> bool -> (funname -> bool list
    option) -> 'a1 instr -> SvExtra.Sv.t -> (SvExtra.Sv.t * 'a1 instr option)
    cexec **)

let rec dead_code_i asmop is_move_op do_nop onfun i s =
  let MkI (ii, ir) = i in
  (match ir with
   | Cassgn (x, tag, _, e) ->
     let w = write_i asmop ir in
     if negb (eq_op assgn_tag_eqType (Obj.magic tag) (Obj.magic AT_keep))
     then if (||) ((&&) (SvExtra.disjoint s w) (negb (lv_write_mem x)))
               ((&&)
                 ((||) do_nop
                   (eq_op assgn_tag_eqType (Obj.magic tag)
                     (Obj.magic AT_rename))) (check_nop x e))
          then Ok (s, None)
          else Ok ((read_rv_rec (read_e_rec (SvExtra.Sv.diff s w) e) x),
                 (Some i))
     else Ok ((read_rv_rec (read_e_rec (SvExtra.Sv.diff s w) e) x), (Some i))
   | Copn (xs, tag, o, es) ->
     let w = vrvs xs in
     if negb (eq_op assgn_tag_eqType (Obj.magic tag) (Obj.magic AT_keep))
     then if (&&) (SvExtra.disjoint s w) (negb (has lv_write_mem xs))
          then Ok (s, None)
          else if check_nop_opn asmop is_move_op xs o es
               then Ok (s, None)
               else Ok
                      ((read_es_rec (read_rvs_rec (SvExtra.Sv.diff s w) xs)
                         es), (Some i))
     else Ok ((read_es_rec (read_rvs_rec (SvExtra.Sv.diff s w) xs) es), (Some
            i))
   | Csyscall (xs, _, es) ->
     Ok ((read_es_rec (read_rvs_rec (SvExtra.Sv.diff s (vrvs xs)) xs) es),
       (Some i))
   | Cif (b, c1, c2) ->
     (match dead_code_c asmop (dead_code_i asmop is_move_op do_nop onfun) c1 s with
      | Ok x ->
        (match dead_code_c asmop (dead_code_i asmop is_move_op do_nop onfun)
                 c2 s with
         | Ok x0 ->
           let (s1, c3) = x in
           let (s2, c4) = x0 in
           Ok ((read_e_rec (SvExtra.Sv.union s1 s2) b), (Some (MkI (ii, (Cif
           (b, c3, c4))))))
         | Error s0 -> Error s0)
      | Error s0 -> Error s0)
   | Cfor (x, r, c) ->
     let (p, e2) = r in
     let (dir, e1) = p in
     (match loop asmop
              (dead_code_c asmop (dead_code_i asmop is_move_op do_nop onfun)
                c) ii Loop.nb (read_rv (Lvar x)) (vrv (Lvar x)) s with
      | Ok x0 ->
        let (s0, c0) = x0 in
        Ok ((read_e_rec (read_e_rec s0 e2) e1), (Some (MkI (ii, (Cfor (x,
        ((dir, e1), e2), c0))))))
      | Error s0 -> Error s0)
   | Cwhile (a, c, e, c') ->
     let dobody = fun s_o ->
       let s_o' = read_e_rec s_o e in
       (match dead_code_c asmop (dead_code_i asmop is_move_op do_nop onfun) c
                s_o' with
        | Ok x ->
          let (s_i, c0) = x in
          (match dead_code_c asmop
                   (dead_code_i asmop is_move_op do_nop onfun) c' s_i with
           | Ok x0 -> let (s_i', c'0) = x0 in Ok (s_i', (s_i, (c0, c'0)))
           | Error s0 -> Error s0)
        | Error s0 -> Error s0)
     in
     (match wloop asmop dobody ii Loop.nb s with
      | Ok x ->
        let (s0, y) = x in
        let (c0, c'0) = y in
        Ok (s0, (Some (MkI (ii, (Cwhile (a, c0, e, c'0))))))
      | Error s0 -> Error s0)
   | Ccall (xs, fn, es) ->
     (match match onfun fn with
            | Some bs -> add_iinfo ii (check_keep_only xs bs s)
            | None -> Ok ((read_rvs_rec (SvExtra.Sv.diff s (vrvs xs)) xs), xs) with
      | Ok x ->
        let (si, xs0) = x in
        Ok ((read_es_rec si es), (Some (MkI (ii, (Ccall (xs0, fn, es))))))
      | Error s0 -> Error s0))

(** val dead_code_fd :
    'a1 asmOp -> ('a1 asm_op_t -> bool) -> bool -> (funname -> bool list
    option) -> funname -> ('a1, 'a2) _fundef -> ('a1, 'a2) _fundef cexec **)

let dead_code_fd asmop is_move_op do_nop onfun fn fd =
  let { f_info = ii; f_tyin = tyi; f_params = params; f_body = c; f_tyout =
    tyo; f_res = res; f_extra = ef } = fd
  in
  let res0 = fn_keep_only onfun fn res in
  let tyo0 = fn_keep_only onfun fn tyo in
  let s = read_es (map coq_Plvar res0) in
  (match dead_code_c asmop (dead_code_i asmop is_move_op do_nop onfun) c s with
   | Ok x ->
     Ok { f_info = ii; f_tyin = tyi; f_params = params; f_body = (snd x);
       f_tyout = tyo0; f_res = res0; f_extra = ef }
   | Error s0 -> Error s0)

(** val dead_code_prog_tokeep :
    'a1 asmOp -> ('a1 asm_op_t -> bool) -> bool -> (funname -> bool list
    option) -> progT -> 'a1 prog -> 'a1 prog cexec **)

let dead_code_prog_tokeep asmop is_move_op do_nop onfun _ p =
  match map_cfprog_name_gen (fun x -> x.f_info)
          (dead_code_fd asmop is_move_op do_nop onfun) p.p_funcs with
  | Ok x -> Ok { p_funcs = x; p_globs = p.p_globs; p_extra = p.p_extra }
  | Error s -> Error s

(** val dead_code_prog :
    'a1 asmOp -> ('a1 asm_op_t -> bool) -> progT -> 'a1 prog -> bool -> 'a1
    prog cexec **)

let dead_code_prog asmop is_move_op pT p do_nop =
  dead_code_prog_tokeep asmop is_move_op do_nop (fun _ -> None) pT p
