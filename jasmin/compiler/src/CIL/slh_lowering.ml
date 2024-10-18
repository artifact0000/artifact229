open BinNums
open Datatypes
open Compiler_util
open Constant_prop
open Eqtype
open Expr
open Flag_combination
open Return_address_kind
open Seq
open Slh_ops
open Sopn
open Type
open Utils0
open Var0
open Wsize

module E =
 struct
  (** val pass : char list **)

  let pass =
    's'::('p'::('e'::('c'::('u'::('l'::('a'::('t'::('i'::('v'::('e'::(' '::('e'::('x'::('e'::('c'::('u'::('t'::('i'::('o'::('n'::(' '::('l'::('o'::('w'::('e'::('r'::('i'::('n'::('g'::[])))))))))))))))))))))))))))))

  (** val pp_user_error :
      instr_info option -> var_info option -> pp_error -> pp_error_loc **)

  let pp_user_error ii vi pp =
    { pel_msg =
      (pp_vbox (pp :: ((PPEstring
        ('D'::('i'::('d'::(' '::('y'::('o'::('u'::(' '::('r'::('u'::('n'::(' '::('t'::('h'::('e'::(' '::('s'::('p'::('e'::('c'::('u'::('l'::('a'::('t'::('i'::('v'::('e'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::(' '::('t'::('i'::('m'::('e'::(' '::('c'::('h'::('e'::('c'::('k'::('e'::('r'::(' '::('f'::('i'::('r'::('s'::('t'::('?'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: [])));
      pel_fn = None; pel_fi = None; pel_ii = ii; pel_vi = vi; pel_pass =
      (Some pass); pel_internal = false }

  (** val cond_not_found :
      instr_info -> pexpr option -> pexpr -> pp_error_loc **)

  let cond_not_found ii oe e =
    let pp_oe =
      match oe with
      | Some e0 ->
        (PPEstring
          ('k'::('n'::('o'::('w'::('n'::(' '::('e'::('x'::('p'::('r'::('e'::('s'::('s'::('i'::('o'::('n'::[]))))))))))))))))) :: ((PPEexpr
          e0) :: [])
      | None ->
        (PPEstring
          ('n'::('o'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('a'::('r'::('e'::(' '::('k'::('n'::('o'::('w'::('n'::[]))))))))))))))))))))))) :: []
    in
    pp_user_error (Some ii) None
      (pp_vbox
        ((pp_hov ((PPEstring
           ('N'::('o'::('t'::(' '::('a'::('b'::('l'::('e'::(' '::('t'::('o'::(' '::('p'::('r'::('o'::('v'::('e'::(' '::('t'::('h'::('a'::('t'::[]))))))))))))))))))))))) :: ((PPEexpr
           e) :: ((PPEstring
           ('e'::('v'::('a'::('l'::('u'::('a'::('t'::('e'::(' '::('t'::('o'::(' '::('t'::('r'::('u'::('e'::(','::[])))))))))))))))))) :: [])))) :: (
        (pp_hov pp_oe) :: [])))

  (** val lvar_variable : instr_info -> pp_error_loc **)

  let lvar_variable ii =
    pp_user_error (Some ii) None (PPEstring
      ('m'::('i'::('s'::('s'::('p'::('e'::('c'::('u'::('l'::('a'::('t'::('i'::('o'::('n'::(' '::('f'::('l'::('a'::('g'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('s'::('t'::('o'::('r'::('e'::('d'::(' '::('i'::('n'::('t'::('o'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[])))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val expr_variable : instr_info -> pexpr -> pp_error_loc **)

  let expr_variable ii e =
    pp_user_error (Some ii) None
      (pp_vbox ((PPEstring
        ('o'::('n'::('l'::('y'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::(' '::('a'::('l'::('l'::('o'::('w'::('e'::('d'::(' '::('f'::('o'::('r'::(' '::('m'::('i'::('s'::('s'::('p'::('e'::('c'::('u'::('l'::('a'::('t'::('i'::('o'::('n'::(' '::('f'::('l'::('a'::('g'::(':'::[]))))))))))))))))))))))))))))))))))))))))))))))) :: ((PPEexpr
        e) :: [])))

  (** val msf_not_found_r : var_i -> SvExtra.Sv.t -> pp_error_loc **)

  let msf_not_found_r x known =
    pp_user_error None (Some x.v_info)
      (pp_vbox
        ((pp_box ((PPEstring
           ('V'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[]))))))))) :: ((PPEvar
           x.v_var) :: ((PPEstring
           ('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('m'::('i'::('s'::('s'::('p'::('e'::('c'::('u'::('l'::('a'::('t'::('i'::('o'::('n'::(' '::('f'::('l'::('a'::('g'::[]))))))))))))))))))))))))))))) :: [])))) :: (
        (pp_box ((PPEstring
          ('K'::('n'::('o'::('w'::('n'::(' '::('a'::('r'::('e'::[])))))))))) :: (
          (pp_Sv known) :: []))) :: [])))

  (** val msf_not_found :
      instr_info -> var_i -> SvExtra.Sv.t -> pp_error_loc **)

  let msf_not_found ii x known =
    pp_at_ii ii (msf_not_found_r x known)

  (** val invalid_nb_args : pp_error_loc **)

  let invalid_nb_args =
    pp_internal_error_s pass
      ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::[])))))))))))))))))))))))))))

  (** val invalid_nb_lvals : pp_error_loc **)

  let invalid_nb_lvals =
    pp_internal_error_s pass
      ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('l'::('e'::('f'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::('s'::[])))))))))))))))))))))))))))))

  (** val cond_uses_mem : instr_info -> pexpr -> pp_error_loc **)

  let cond_uses_mem ii e =
    pp_user_error (Some ii) None
      (pp_vbox ((PPEstring
        ('C'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('h'::('a'::('s'::(' '::('a'::(' '::('m'::('e'::('m'::('o'::('r'::('y'::(' '::('a'::('c'::('c'::('e'::('s'::('s'::(':'::[]))))))))))))))))))))))))))))))) :: ((PPEexpr
        e) :: [])))

  (** val lowering_failed : instr_info -> pp_error_loc **)

  let lowering_failed ii =
    pp_user_error (Some ii) None (PPEstring
      ('T'::('h'::('e'::(' '::('a'::('r'::('c'::('h'::('i'::('t'::('e'::('c'::('t'::('u'::('r'::('e'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('p'::('r'::('o'::('v'::('i'::('d'::('e'::('s'::(' '::('p'::('r'::('o'::('t'::('e'::('c'::('t'::('i'::('o'::('n'::(' '::('f'::('o'::('r'::(' '::('s'::('e'::('l'::('e'::('c'::('t'::('i'::('v'::('e'::(' '::('s'::('p'::('e'::('c'::('u'::('l'::('a'::('t'::('i'::('v'::('e'::(' '::('l'::('o'::('a'::('d'::(' '::('h'::('a'::('r'::('d'::('e'::('n'::('i'::('n'::('g'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val invalid_type_for_msf : instr_info -> pp_error_loc **)

  let invalid_type_for_msf ii =
    pp_user_error (Some ii) None (PPEstring
      ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('t'::('y'::('p'::('e'::(' '::('f'::('o'::('r'::(' '::('m'::('s'::('f'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))))))))))

  (** val update_after_call_failed :
      instr_info -> char list option -> pp_error_loc **)

  let update_after_call_failed ii omsg =
    let reason =
      match omsg with
      | Some msg -> ('('::[]) :: (msg :: ((')'::[]) :: []))
      | None -> []
    in
    let msg =
      'C'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('i'::('n'::('t'::('r'::('o'::('d'::('u'::('c'::('e'::(' '::('M'::('S'::('F'::(' '::('u'::('p'::('d'::('a'::('t'::('e'::(' '::('a'::('f'::('t'::('e'::('r'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::[]))))))))))))))))))))))))))))))))))))))))))
    in
    { pel_msg = (pp_box (map (fun x -> PPEstring x) (msg :: reason)));
    pel_fn = None; pel_fi = None; pel_ii = (Some ii); pel_vi = None;
    pel_pass = (Some pass); pel_internal = true }

  (** val not_implemented : funname -> char list -> pp_error_loc **)

  let not_implemented fn msg =
    { pel_msg = (PPEstring msg); pel_fn = (Some fn); pel_fi = None; pel_ii =
      None; pel_vi = None; pel_pass = (Some pass); pel_internal = true }
 end

module Env =
 struct
  type t = { cond : pexpr option; msf_vars : SvExtra.Sv.t }

  (** val cond : t -> pexpr option **)

  let cond t0 =
    t0.cond

  (** val msf_vars : t -> SvExtra.Sv.t **)

  let msf_vars t0 =
    t0.msf_vars

  (** val restrict_cond : pexpr option -> SvExtra.Sv.t -> pexpr option **)

  let restrict_cond oc xs =
    match oc with
    | Some c -> if negb (SvExtra.disjoint (read_e c) xs) then None else oc
    | None -> oc

  (** val empty : t **)

  let empty =
    { cond = None; msf_vars = SvExtra.Sv.empty }

  (** val initial : Var.var option -> t **)

  let initial ox =
    { cond = None; msf_vars = (SvExtra.sv_of_option (Obj.magic ox)) }

  (** val update_cond : t -> pexpr -> t **)

  let update_cond env c =
    { cond = (Some c); msf_vars = env.msf_vars }

  (** val meet : t -> t -> t **)

  let meet env0 env1 =
    let c =
      match env0.cond with
      | Some c0 ->
        (match env1.cond with
         | Some c1 -> if eq_expr c0 c1 then Some c0 else None
         | None -> None)
      | None -> None
    in
    { cond = c; msf_vars = (SvExtra.Sv.inter env0.msf_vars env1.msf_vars) }

  (** val le : t -> t -> bool **)

  let le env0 env1 =
    let bcond =
      match env0.cond with
      | Some c0 ->
        (match env1.cond with
         | Some c1 -> eq_expr c0 c1
         | None -> false)
      | None -> true
    in
    (&&) bcond (SvExtra.Sv.subset env0.msf_vars env1.msf_vars)

  (** val is_msf_var : t -> Var.var -> bool **)

  let is_msf_var env x =
    SvExtra.Sv.mem (Obj.magic x) env.msf_vars

  (** val is_cond : t -> pexpr -> bool **)

  let is_cond env c =
    (||) (eq_expr c (Pbool true))
      (match env.cond with
       | Some c' -> eq_expr c c'
       | None -> false)

  (** val after_SLHmove : t -> Var.var option -> t **)

  let after_SLHmove env ox =
    let s = SvExtra.sv_of_option (Obj.magic ox) in
    { cond = (restrict_cond env.cond s); msf_vars =
    (SvExtra.Sv.union s env.msf_vars) }

  (** val after_assign_var : t -> Var.var -> t **)

  let after_assign_var env x =
    { cond = (restrict_cond env.cond (SvExtra.Sv.singleton (Obj.magic x)));
      msf_vars = (SvExtra.Sv.remove (Obj.magic x) env.msf_vars) }

  (** val after_assign_vars : t -> SvExtra.Sv.t -> t **)

  let after_assign_vars env xs =
    { cond = (restrict_cond env.cond xs); msf_vars =
      (SvExtra.Sv.diff env.msf_vars xs) }
 end

(** val check_e_msf :
    instr_info -> Env.t -> pexpr -> (pp_error_loc, unit) result **)

let check_e_msf ii env e = match e with
| Pvar msf ->
  if (&&) (Env.is_msf_var env msf.gv.v_var) (is_lvar msf)
  then Ok ()
  else Error (E.msf_not_found ii msf.gv env.Env.msf_vars)
| _ -> Error (E.expr_variable ii e)

(** val check_lv :
    instr_info -> lval -> (pp_error_loc, Var.var option) result **)

let check_lv ii = function
| Lnone (_, _) -> Ok None
| Lvar x -> Ok (Some x.v_var)
| _ -> Error (E.lvar_variable ii)

(** val check_lv_msf :
    coq_MSFsize -> instr_info -> lval -> (pp_error_loc, Var.var option) result **)

let check_lv_msf msfsz ii lv =
  match check_lv ii lv with
  | Ok x ->
    if match x with
       | Some x0 ->
         eq_op stype_eqType (Obj.magic Var.vtype x0)
           (Obj.magic (Coq_sword (msf_size msfsz)))
       | None -> true
    then Ok x
    else let s = E.invalid_type_for_msf ii in Error s
  | Error s -> Error s

(** val check_slho :
    coq_MSFsize -> instr_info -> lval list -> slh_op -> pexpr list -> Env.t
    -> Env.t cexec **)

let check_slho msfsz ii lvs slho es env =
  match slho with
  | SLHinit ->
    (match check_lv_msf msfsz ii
             (nth (Lnone (dummy_var_info, Coq_sint)) lvs O) with
     | Ok x -> Ok (Env.initial x)
     | Error s -> Error s)
  | SLHupdate ->
    let e = nth (Pconst Z0) es O in
    if Env.is_cond env e
    then (match check_e_msf ii env (nth (Pconst Z0) es (S O)) with
          | Ok _ ->
            (match check_lv_msf msfsz ii
                     (nth (Lnone (dummy_var_info, Coq_sint)) lvs O) with
             | Ok x -> Ok (Env.after_SLHmove env x)
             | Error s -> Error s)
          | Error s -> Error s)
    else let s = E.cond_not_found ii env.Env.cond e in Error s
  | SLHmove ->
    (match check_e_msf ii env (nth (Pconst Z0) es O) with
     | Ok _ ->
       (match check_lv_msf msfsz ii
                (nth (Lnone (dummy_var_info, Coq_sint)) lvs O) with
        | Ok x -> Ok (Env.after_SLHmove env x)
        | Error s -> Error s)
     | Error s -> Error s)
  | SLHprotect_ptr_fail _ ->
    Ok
      (Env.after_assign_vars env
        (vrv (nth (Lnone (dummy_var_info, Coq_sint)) lvs O)))
  | _ ->
    (match check_e_msf ii env (nth (Pconst Z0) es (S O)) with
     | Ok _ ->
       Ok
         (Env.after_assign_vars env
           (vrv (nth (Lnone (dummy_var_info, Coq_sint)) lvs O)))
     | Error s -> Error s)

(** val check_f_arg :
    instr_info -> Env.t -> pexpr -> slh_t -> (pp_error_loc, unit) result **)

let check_f_arg ii env e = function
| Slh_None -> Ok ()
| Slh_msf -> check_e_msf ii env e

(** val check_f_args :
    instr_info -> Env.t -> pexpr list -> slh_t list -> (pp_error_loc, unit
    list) result **)

let check_f_args ii env es tys =
  mapM2 E.invalid_nb_args (check_f_arg ii env) es tys

(** val check_f_lv :
    coq_MSFsize -> instr_info -> Env.t -> lval -> slh_t -> (pp_error_loc,
    Env.t) result **)

let check_f_lv msfsz ii env lv = function
| Slh_None -> Ok (Env.after_assign_vars env (vrv lv))
| Slh_msf ->
  (match check_lv_msf msfsz ii lv with
   | Ok x -> Ok (Env.after_SLHmove env x)
   | Error s -> Error s)

(** val check_f_lvs :
    coq_MSFsize -> instr_info -> Env.t -> lval list -> slh_t list ->
    (pp_error_loc, Env.t) result **)

let rec check_f_lvs msfsz ii env lvs tys =
  match lvs with
  | [] -> (match tys with
           | [] -> Ok env
           | _ :: _ -> Error E.invalid_nb_lvals)
  | lv :: lvs0 ->
    (match tys with
     | [] -> Error E.invalid_nb_lvals
     | ty :: tys0 ->
       (match check_f_lv msfsz ii env lv ty with
        | Ok x -> check_f_lvs msfsz ii x lvs0 tys0
        | Error s -> Error s))

(** val init_fun_env :
    coq_MSFsize -> Env.t -> var_i list -> stype list -> slh_t list ->
    (pp_error_loc, Env.t) result **)

let rec init_fun_env msfsz env xs ttys tys =
  match xs with
  | [] ->
    (match ttys with
     | [] ->
       (match tys with
        | [] -> Ok env
        | _ :: _ ->
          Error
            (pp_internal_error_s E.pass
              ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('p'::('a'::('r'::('a'::('m'::('s'::(' '::('('::('n'::('b'::(')'::[])))))))))))))))))))))
     | _ :: _ ->
       Error
         (pp_internal_error_s E.pass
           ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('p'::('a'::('r'::('a'::('m'::('s'::(' '::('('::('n'::('b'::(')'::[])))))))))))))))))))))
  | x :: xs0 ->
    (match ttys with
     | [] ->
       Error
         (pp_internal_error_s E.pass
           ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('p'::('a'::('r'::('a'::('m'::('s'::(' '::('('::('n'::('b'::(')'::[]))))))))))))))))))))
     | t0 :: ttys0 ->
       (match tys with
        | [] ->
          Error
            (pp_internal_error_s E.pass
              ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('p'::('a'::('r'::('a'::('m'::('s'::(' '::('('::('n'::('b'::(')'::[]))))))))))))))))))))
        | ty :: tys0 ->
          (match match ty with
                 | Slh_None -> Ok (Env.after_assign_var env x.v_var)
                 | Slh_msf ->
                   if (&&)
                        (eq_op stype_eqType (Obj.magic Var.vtype x.v_var)
                          (Obj.magic (Coq_sword (msf_size msfsz))))
                        (eq_op stype_eqType (Obj.magic t0)
                          (Obj.magic (Coq_sword (msf_size msfsz))))
                   then Ok (Env.after_SLHmove env (Some x.v_var))
                   else let s =
                          pp_internal_error_s E.pass
                            ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('p'::('a'::('r'::('a'::('m'::('s'::(' '::('('::('t'::('y'::('p'::('e'::(')'::[])))))))))))))))))))))
                        in
                        Error s with
           | Ok x0 -> init_fun_env msfsz x0 xs0 ttys0 tys0
           | Error s -> Error s)))

(** val check_res :
    coq_MSFsize -> Env.t -> var_i list -> stype list -> slh_t list ->
    (pp_error_loc, unit) result **)

let rec check_res msfsz env xs ttys tys =
  match xs with
  | [] ->
    (match ttys with
     | [] ->
       (match tys with
        | [] -> Ok ()
        | _ :: _ ->
          Error
            (pp_internal_error_s E.pass
              ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('('::('n'::('b'::(')'::[])))))))))))))))))))))
     | _ :: _ ->
       Error
         (pp_internal_error_s E.pass
           ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('('::('n'::('b'::(')'::[])))))))))))))))))))))
  | x :: xs0 ->
    (match ttys with
     | [] ->
       Error
         (pp_internal_error_s E.pass
           ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('('::('n'::('b'::(')'::[]))))))))))))))))))))
     | t0 :: ttys0 ->
       (match tys with
        | [] ->
          Error
            (pp_internal_error_s E.pass
              ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('('::('n'::('b'::(')'::[]))))))))))))))))))))
        | ty :: tys0 ->
          if match ty with
             | Slh_None -> true
             | Slh_msf -> Env.is_msf_var env x.v_var
          then if match ty with
                  | Slh_None -> true
                  | Slh_msf ->
                    eq_op stype_eqType (Obj.magic t0)
                      (Obj.magic (Coq_sword (msf_size msfsz)))
               then check_res msfsz env xs0 ttys0 tys0
               else let s =
                      pp_internal_error_s E.pass
                        ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('('::('t'::('y'::('p'::('e'::(')'::[])))))))))))))))))))))
                    in
                    Error s
          else let s = E.msf_not_found_r x env.Env.msf_vars in Error s))

(** val check_for :
    instr_info -> Var.var -> (Env.t -> Env.t cexec) -> nat -> Env.t -> Env.t
    cexec **)

let rec check_for ii x check_c fuel env =
  match fuel with
  | O -> Error (ii_loop_iterator E.pass ii)
  | S n ->
    (match check_c (Env.after_assign_var env x) with
     | Ok x0 ->
       if Env.le env x0
       then Ok env
       else check_for ii x check_c n (Env.meet env x0)
     | Error s -> Error s)

(** val neg_const_prop : coq_FlagCombinationParams -> pexpr -> pexpr **)

let neg_const_prop fcparams e =
  const_prop_e fcparams None empty_cpm (enot e)

(** val check_while :
    coq_FlagCombinationParams -> instr_info -> pexpr -> (Env.t -> Env.t
    cexec) -> (Env.t -> Env.t cexec) -> nat -> Env.t -> Env.t cexec **)

let rec check_while fcparams ii cond0 check_c0 check_c1 fuel env =
  match fuel with
  | O -> Error (ii_loop_iterator E.pass ii)
  | S n ->
    (match check_c0 env with
     | Ok x ->
       (match check_c1 (Env.update_cond x cond0) with
        | Ok x0 ->
          if Env.le env x0
          then Ok (Env.update_cond x (neg_const_prop fcparams cond0))
          else check_while fcparams ii cond0 check_c0 check_c1 n
                 (Env.meet env x0)
        | Error s -> Error s)
     | Error s -> Error s)

type 'asm_op sh_params = { shp_lower : (lval list -> slh_op -> pexpr list ->
                                       ((lval list * 'asm_op sopn) * pexpr
                                       list) option);
                           shp_update_after_call : ((char list option ->
                                                   pp_error_loc) -> var_i ->
                                                   ((lval list * 'asm_op
                                                   sopn) * pexpr list) cexec) }

type slh_function_info = { slhfi_tin : slh_t list; slhfi_tout : slh_t list;
                           slhfi_rak : return_address_kind }

(** val check_i :
    'a1 asmOp -> coq_MSFsize -> coq_FlagCombinationParams -> (funname ->
    slh_function_info) -> 'a1 instr -> Env.t -> Env.t cexec **)

let rec check_i asmop msfsz fcparams slh_fun_info i env =
  let MkI (ii, ir) = i in
  (match ir with
   | Cassgn (lv, _, _, _) -> Ok (Env.after_assign_vars env (vrv lv))
   | Copn (lvs, _, op, es) ->
     (match op with
      | Oslh slho -> check_slho msfsz ii lvs slho es env
      | _ -> Ok (Env.after_assign_vars env (vrvs lvs)))
   | Csyscall (_, _, _) -> Ok Env.empty
   | Cif (cond0, c0, c1) ->
     if negb (use_mem cond0)
     then (match let env0 = Env.update_cond env cond0 in
                 foldM (check_i asmop msfsz fcparams slh_fun_info) env0 c0 with
           | Ok x ->
             (match let env0 =
                      Env.update_cond env (neg_const_prop fcparams cond0)
                    in
                    foldM (check_i asmop msfsz fcparams slh_fun_info) env0 c1 with
              | Ok x0 -> Ok (Env.meet x x0)
              | Error s -> Error s)
           | Error s -> Error s)
     else let s = E.cond_uses_mem ii cond0 in Error s
   | Cfor (x, _, c) ->
     check_for ii x.v_var (fun env0 ->
       foldM (check_i asmop msfsz fcparams slh_fun_info) env0 c) Loop.nb env
   | Cwhile (_, c0, cond0, c1) ->
     if negb (use_mem cond0)
     then check_while fcparams ii cond0 (fun env0 ->
            foldM (check_i asmop msfsz fcparams slh_fun_info) env0 c0)
            (fun env0 ->
            foldM (check_i asmop msfsz fcparams slh_fun_info) env0 c1)
            Loop.nb env
     else let s = E.cond_uses_mem ii cond0 in Error s
   | Ccall (xs, fn, es) ->
     let slhfi = slh_fun_info fn in
     (match check_f_args ii env es slhfi.slhfi_tin with
      | Ok _ -> check_f_lvs msfsz ii env xs slhfi.slhfi_tout
      | Error s -> Error s))

(** val check_cmd :
    'a1 asmOp -> coq_MSFsize -> coq_FlagCombinationParams -> (funname ->
    slh_function_info) -> Env.t -> 'a1 instr list -> Env.t cexec **)

let check_cmd asmop msfsz fcparams slh_fun_info env c =
  foldM (check_i asmop msfsz fcparams slh_fun_info) env c

(** val check_fd :
    'a1 asmOp -> coq_MSFsize -> progT -> coq_FlagCombinationParams ->
    (funname -> slh_function_info) -> funname -> 'a1 fundef -> Env.t cexec **)

let check_fd asmop msfsz _ fcparams slh_fun_info fn fd =
  let slhfi = slh_fun_info fn in
  (match init_fun_env msfsz Env.empty fd.f_params fd.f_tyin slhfi.slhfi_tin with
   | Ok x ->
     (match check_cmd asmop msfsz fcparams slh_fun_info x fd.f_body with
      | Ok x0 ->
        (match check_res msfsz x0 fd.f_res fd.f_tyout slhfi.slhfi_tout with
         | Ok _ -> Ok x0
         | Error s -> Error s)
      | Error s -> Error s)
   | Error s -> Error s)

(** val is_protect_ptr : slh_op -> positive option **)

let is_protect_ptr = function
| SLHprotect_ptr p -> Some p
| _ -> None

(** val lower_slho :
    'a1 asmOp -> 'a1 sh_params -> instr_info -> lval list -> assgn_tag ->
    slh_op -> pexpr list -> 'a1 instr_r cexec **)

let lower_slho asmop shparams ii lvs tg slho es =
  match is_protect_ptr slho with
  | Some p -> Ok (Copn (lvs, tg, (Oslh (SLHprotect_ptr_fail p)), es))
  | None ->
    (match shparams.shp_lower lvs slho es with
     | Some args -> Ok (instr_of_copn_args asmop tg args)
     | None -> Error (E.lowering_failed ii))

(** val output_msfs :
    (funname -> slh_function_info) -> funname -> lval list -> var_i list **)

let output_msfs slh_fun_info fn lvs =
  let get_msf = fun pat ->
    let (lv, t0) = pat in
    (match lv with
     | Lnone (_, _) -> None
     | Lvar x -> (match t0 with
                  | Slh_None -> None
                  | Slh_msf -> Some x)
     | _ -> None)
  in
  pmap get_msf (zip lvs (slh_fun_info fn).slhfi_tout)

(** val update_msf :
    'a1 asmOp -> 'a1 sh_params -> (funname -> slh_function_info) ->
    instr_info -> funname -> lval list -> 'a1 instr_r list cexec **)

let update_msf asmop shparams slh_fun_info ii fn lvs =
  if ii_update_after_call ii
  then let on_err = E.update_after_call_failed ii in
       (match output_msfs slh_fun_info fn lvs with
        | [] ->
          Error
            (on_err (Some
              ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::('e'::('d'::(' '::('M'::('S'::('F'::('s'::[])))))))))))))))))))))))))))))))))
        | msf :: l ->
          (match l with
           | [] ->
             (match shparams.shp_update_after_call on_err msf with
              | Ok x -> Ok ((instr_of_copn_args asmop AT_keep x) :: [])
              | Error s -> Error s)
           | _ :: _ ->
             Error
               (on_err (Some
                 ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::('e'::('d'::(' '::('M'::('S'::('F'::('s'::[])))))))))))))))))))))))))))))))))))
  else Ok []

(** val lower_i :
    'a1 asmOp -> coq_PointerData -> 'a1 sh_params -> (funname ->
    slh_function_info) -> bool -> 'a1 instr -> 'a1 instr list cexec **)

let rec lower_i asmop pd shparams slh_fun_info protect_calls i =
  let lower_cmd0 = fun c ->
    conc_mapM (lower_i asmop pd shparams slh_fun_info protect_calls) c
  in
  let MkI (ii, ir) = i in
  (match match ir with
         | Cassgn (_, _, _, _) -> Ok (ir :: [])
         | Copn (lvs, tg, op, es) ->
           (match match op with
                  | Oslh slho -> lower_slho asmop shparams ii lvs tg slho es
                  | _ -> Ok ir with
            | Ok x -> Ok (x :: [])
            | Error s -> Error s)
         | Csyscall (_, _, _) -> Ok (ir :: [])
         | Cif (b, c0, c1) ->
           (match lower_cmd0 c0 with
            | Ok x ->
              (match lower_cmd0 c1 with
               | Ok x0 -> Ok ((Cif (b, x, x0)) :: [])
               | Error s -> Error s)
            | Error s -> Error s)
         | Cfor (x, r, c) ->
           (match lower_cmd0 c with
            | Ok x0 -> Ok ((Cfor (x, r, x0)) :: [])
            | Error s -> Error s)
         | Cwhile (al, c0, b, c1) ->
           (match lower_cmd0 c0 with
            | Ok x ->
              (match lower_cmd0 c1 with
               | Ok x0 -> Ok ((Cwhile (al, x, b, x0)) :: [])
               | Error s -> Error s)
            | Error s -> Error s)
         | Ccall (lvs, callee, _) ->
           if protect_calls
           then let pre =
                  match (slh_fun_info callee).slhfi_rak with
                  | RAKnone -> []
                  | RAKstack -> []
                  | RAKregister -> []
                  | RAKextra_register ->
                    (use_vars_get_reg asmop pd IRpc_save_scratch) :: []
                in
                (match update_msf asmop shparams slh_fun_info ii callee lvs with
                 | Ok x -> Ok (cat pre (ir :: x))
                 | Error s -> Error s)
           else Ok (ir :: []) with
   | Ok x -> Ok (map (fun x0 -> MkI (ii, x0)) x)
   | Error s -> Error s)

(** val lower_cmd :
    'a1 asmOp -> coq_PointerData -> 'a1 sh_params -> (funname ->
    slh_function_info) -> bool -> 'a1 instr list -> 'a1 instr list cexec **)

let lower_cmd asmop pd shparams slh_fun_info protect_calls c =
  conc_mapM (lower_i asmop pd shparams slh_fun_info protect_calls) c

(** val protected_ret :
    'a1 asmOp -> coq_PointerData -> progT -> (funname -> slh_function_info)
    -> Env.t -> funname -> 'a1 fundef -> 'a1 instr list cexec **)

let protected_ret asmop pd _ slh_fun_info _ fn _ =
  match (slh_fun_info fn).slhfi_rak with
  | RAKnone -> Ok []
  | RAKextra_register ->
    Ok ((MkI (dummy_instr_info,
      (use_vars_get_reg asmop pd IRpc_load_scratch))) :: [])
  | _ ->
    let msg =
      'R'::('e'::('t'::('u'::('r'::('n'::(' '::('t'::('a'::('g'::('s'::(' '::('a'::('r'::('e'::(' '::('o'::('n'::('l'::('y'::(' '::('a'::('l'::('l'::('o'::('w'::('e'::('d'::(' '::('i'::('n'::(' '::('M'::('M'::('X'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::('s'::[]))))))))))))))))))))))))))))))))))))))))))))
    in
    Error (E.not_implemented fn msg)

(** val lower_fd :
    'a1 asmOp -> coq_PointerData -> coq_MSFsize -> progT ->
    coq_FlagCombinationParams -> 'a1 sh_params -> (funname ->
    slh_function_info) -> bool -> funname -> 'a1 fundef -> 'a1 fundef cexec **)

let lower_fd asmop pd msfsz pT fcparams shparams slh_fun_info protect_calls fn fd =
  match check_fd asmop msfsz pT fcparams slh_fun_info fn fd with
  | Ok x ->
    let { f_info = ii; f_tyin = si; f_params = p; f_body = c; f_tyout = so;
      f_res = r; f_extra = ev } = fd
    in
    (match lower_cmd asmop pd shparams slh_fun_info protect_calls c with
     | Ok x0 ->
       (match if protect_calls
              then protected_ret asmop pd pT slh_fun_info x fn fd
              else Ok [] with
        | Ok x1 ->
          Ok { f_info = ii; f_tyin = si; f_params = p; f_body = (cat x0 x1);
            f_tyout = so; f_res = r; f_extra = ev }
        | Error s -> Error s)
     | Error s -> Error s)
  | Error s -> Error s

(** val lower_slh_prog :
    'a1 asmOp -> coq_PointerData -> coq_MSFsize -> progT ->
    coq_FlagCombinationParams -> 'a1 sh_params -> (funname ->
    slh_function_info) -> bool -> funname list -> 'a1 prog -> 'a1 prog cexec **)

let lower_slh_prog asmop pd msfsz pT fcparams shparams slh_fun_info protect_calls entries p =
  match let msg =
          'e'::('x'::('p'::('o'::('r'::('t'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('t'::('a'::('k'::('e'::(' '::('a'::(' '::('m'::('i'::('s'::('s'::('s'::('p'::('e'::('c'::('u'::('l'::('a'::('t'::('i'::('o'::('n'::(' '::('f'::('l'::('a'::('g'::(' '::('a'::('s'::(' '::('i'::('n'::('p'::('u'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        in
        if all (fun f -> all is_shl_none (slh_fun_info f).slhfi_tin) entries
        then Ok ()
        else Error (E.pp_user_error None None (PPEstring msg)) with
  | Ok _ ->
    (match map_cfprog_name_gen (fun x -> x.f_info)
             (lower_fd asmop pd msfsz pT fcparams shparams slh_fun_info
               protect_calls) p.p_funcs with
     | Ok x -> Ok { p_funcs = x; p_globs = p.p_globs; p_extra = p.p_extra }
     | Error s -> Error s)
  | Error s -> Error s
