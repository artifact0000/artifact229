open BinInt
open BinNums
open BinPos
open Datatypes
open String0
open Compiler_util
open Eqtype
open Expr
open Fexpr
open Label
open Linear
open Path
open Seq
open Sopn
open Ssrbool
open Ssrint
open Type
open Utils0
open Var0
open Word_ssrZ
open Wsize
open Xseq

module E =
 struct
  (** val pass : char list **)

  let pass =
    'p'::('r'::('o'::('t'::('e'::('c'::('t'::(' '::('c'::('a'::('l'::('l'::('s'::[]))))))))))))

  (** val assoc_failed : pp_error_loc **)

  let assoc_failed =
    pp_internal_error_s pass
      ('a'::('s'::('s'::('o'::('c'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))))

  (** val debug : pp_error_loc **)

  let debug =
    pp_internal_error_s pass
      ('d'::('e'::('b'::('u'::('g'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))))

  (** val cant_get_lti : pp_error_loc **)

  let cant_get_lti =
    pp_internal_error_s pass
      ('c'::('a'::('n'::('\''::('t'::(' '::('g'::('e'::('t'::(' '::('l'::('o'::('a'::('d'::(' '::('t'::('a'::('g'::(' '::('i'::('n'::('f'::('o'::[])))))))))))))))))))))))

  (** val invalid_use_vars : pp_error_loc **)

  let invalid_use_vars =
    pp_internal_error_s pass
      ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('O'::('u'::('s'::('e'::('_'::('v'::('a'::('r'::('s'::[])))))))))))))))))

  (** val invalid_state : pp_error_loc **)

  let invalid_state =
    pp_internal_error_s pass
      ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('p'::('r'::('o'::('t'::('e'::('c'::('t'::(' '::('c'::('a'::('l'::('l'::('s'::(' '::('s'::('t'::('a'::('t'::('e'::[])))))))))))))))))))))))))))

  (** val cant_get_lta : pp_error_loc **)

  let cant_get_lta =
    pp_internal_error_s pass
      ('c'::('a'::('n'::('\''::('t'::(' '::('g'::('e'::('t'::(' '::('l'::('o'::('a'::('d'::(' '::('t'::('a'::('g'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::[]))))))))))))))))))))))))))))

  (** val cant_get_tag_reg : pp_error_loc **)

  let cant_get_tag_reg =
    pp_internal_error_s pass
      ('c'::('a'::('n'::('\''::('t'::(' '::('g'::('e'::('t'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::(' '::('w'::('i'::('t'::('h'::(' '::('t'::('a'::('g'::[])))))))))))))))))))))))))))

  (** val gen_err_msg :
      char list -> instr_info -> char list option -> pp_error_loc **)

  let gen_err_msg pre ii omsg =
    let reason =
      concat []
        (match omsg with
         | Some msg -> ('('::[]) :: (msg :: ((')'::[]) :: []))
         | None -> [])
    in
    { pel_msg = (pp_box ((PPEstring pre) :: ((PPEstring reason) :: [])));
    pel_fn = None; pel_fi = None; pel_ii = (Some ii); pel_vi = None;
    pel_pass = (Some pass); pel_internal = true }

  (** val save_tag_failed : instr_info -> char list option -> pp_error_loc **)

  let save_tag_failed =
    gen_err_msg
      ('c'::('a'::('n'::('\''::('t'::(' '::('s'::('a'::('v'::('e'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('t'::('a'::('g'::[])))))))))))))))))))))

  (** val lower_ret_failed :
      instr_info -> char list option -> pp_error_loc **)

  let lower_ret_failed =
    gen_err_msg
      ('c'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('l'::('o'::('w'::('e'::('r'::(' '::('L'::('r'::('e'::('t'::[]))))))))))))))))))))

  (** val lower_update_after_call_failed :
      instr_info -> char list option -> pp_error_loc **)

  let lower_update_after_call_failed =
    gen_err_msg
      ('C'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('l'::('o'::('w'::('e'::('r'::(' '::('u'::('p'::('d'::('a'::('t'::('e'::(' '::('a'::('f'::('t'::('e'::('r'::(' '::('c'::('a'::('l'::('l'::[])))))))))))))))))))))))))))))))))
 end

type cs_info = remote_label * coq_Z

type cst_value = cs_info list * label

type cs_table = cst_value Mf.t

(** val cst_lookup : cs_table -> funname -> cst_value **)

let cst_lookup cst fn =
  match Mf.get cst (Obj.magic fn) with
  | Some x -> x
  | None -> ([], Coq_xH)

(** val label_info :
    'a1 asmOp -> (funname * label) list -> label -> 'a1 lcmd ->
    (funname * label) list * label **)

let rec label_info asmop ris max_lbl = function
| [] -> (ris, max_lbl)
| l :: lc0 ->
  let { li_ii = _; li_i = li_i0 } = l in
  (match li_i0 with
   | Lcall (_, r) ->
     let (fn, _) = r in
     (match lc0 with
      | [] -> label_info asmop ris max_lbl lc0
      | l1 :: lc1 ->
        let { li_ii = _; li_i = li_i1 } = l1 in
        (match li_i1 with
         | Llabel (l2, lbl) ->
           (match l2 with
            | InternalLabel -> label_info asmop ris max_lbl lc0
            | ExternalLabel ->
              label_info asmop ((fn, lbl) :: ris) (Pos.max max_lbl lbl) lc1)
         | _ -> label_info asmop ris max_lbl lc0))
   | Llabel (l0, lbl) ->
     (match l0 with
      | InternalLabel -> label_info asmop ris (Pos.max max_lbl lbl) lc0
      | ExternalLabel -> label_info asmop ris max_lbl lc0)
   | _ -> label_info asmop ris max_lbl lc0)

(** val next_tag : cs_info list -> coq_Z **)

let next_tag = function
| [] -> Z0
| c :: _ -> let (_, t0) = c in Z.succ t0

(** val acc_entry : funname -> cs_table -> (funname * label) -> cs_table **)

let acc_entry caller tbl = function
| (callee, ret_lbl) ->
  let (old_info, max_lbl) = cst_lookup tbl callee in
  let new_info = ((caller, ret_lbl), (next_tag old_info)) :: old_info in
  Mf.set tbl (Obj.magic callee) (new_info, max_lbl)

(** val add_call_sites :
    'a1 asmOp -> cs_table -> funname -> 'a1 lfundef -> cs_table **)

let add_call_sites asmop tbl0 caller lfd =
  let (ris, max_lbl) = label_info asmop [] Coq_xH lfd.lfd_body in
  let (old_info, _) = cst_lookup tbl0 caller in
  let tbl1 = Mf.set tbl0 (Obj.magic caller) (old_info, max_lbl) in
  foldl (acc_entry caller) tbl1 ris

(** val call_sites_table : 'a1 asmOp -> 'a1 lprog -> cs_table **)

let call_sites_table asmop lp =
  foldl (fun tbl -> uncurry (add_call_sites asmop tbl)) Mf.empty lp.lp_funcs

type load_tag_info =
| LTIstack of var_i * var_i
| LTIregister of var_i
| LTIextra_register of var_i * var_i

type lti_table = load_tag_info Mf.t

type lti_state = { ltist_scratch : var_i option; ltist_msf : var_i option }

(** val ltist_empty : lti_state **)

let ltist_empty =
  { ltist_scratch = None; ltist_msf = None }

(** val ltist_get_lti :
    'a1 asmOp -> lti_state -> 'a1 linstr_r -> load_tag_info cexec **)

let ltist_get_lti _ st = function
| Lret ->
  (match st.ltist_scratch with
   | Some r ->
     (match st.ltist_msf with
      | Some msf -> Ok (LTIstack (r, msf))
      | None -> Error E.cant_get_lti)
   | None -> Error E.cant_get_lti)
| Ligoto r0 ->
  (match r0 with
   | Load (_, _, _) -> Error E.cant_get_lti
   | Rexpr f ->
     (match f with
      | Fvar r ->
        (match st.ltist_scratch with
         | Some r' ->
           (match st.ltist_msf with
            | Some _ -> Error E.cant_get_lti
            | None -> Ok (LTIextra_register (r, r')))
         | None ->
           (match st.ltist_msf with
            | Some _ -> Error E.cant_get_lti
            | None -> Ok (LTIregister r)))
      | _ -> Error E.cant_get_lti))
| _ -> Error E.cant_get_lti

(** val ltist_set_scratch : lti_state -> lexpr list -> lti_state cexec **)

let ltist_set_scratch st = function
| [] -> Error E.invalid_use_vars
| l :: l0 ->
  (match l with
   | Store (_, _, _) -> Error E.invalid_use_vars
   | LLvar r ->
     (match l0 with
      | [] -> Ok { ltist_scratch = (Some r); ltist_msf = st.ltist_msf }
      | _ :: _ -> Error E.invalid_use_vars))

(** val ltist_set_msf : lti_state -> rexpr list -> lti_state cexec **)

let ltist_set_msf st = function
| [] -> Error E.invalid_use_vars
| r :: l ->
  (match r with
   | Load (_, _, _) -> Error E.invalid_use_vars
   | Rexpr f ->
     (match f with
      | Fvar msf ->
        (match l with
         | [] ->
           Ok { ltist_scratch = st.ltist_scratch; ltist_msf = (Some msf) }
         | _ :: _ -> Error E.invalid_use_vars)
      | _ -> Error E.invalid_use_vars))

(** val lti_lcmd :
    'a1 asmOp -> lti_state -> 'a1 lcmd -> (load_tag_info * 'a1 lcmd) cexec **)

let rec lti_lcmd asmop st lc = match lc with
| [] -> Error E.cant_get_lti
| li :: lc' ->
  let { li_ii = _; li_i = lir } = li in
  (match lir with
   | Lopn (les, s, res) ->
     (match s with
      | Ointernal i ->
        let Ouse_vars (i0, _, _) = i in
        (match i0 with
         | IRpc_load_scratch ->
           (match lc' with
            | [] ->
              (match ltist_get_lti asmop st lir with
               | Ok x -> Ok (x, lc)
               | Error s0 -> Error s0)
            | _ :: _ ->
              (match ltist_set_scratch st les with
               | Ok x -> lti_lcmd asmop x lc'
               | Error s0 -> Error s0))
         | IRpc_load_msf ->
           (match lc' with
            | [] ->
              (match ltist_get_lti asmop st lir with
               | Ok x -> Ok (x, lc)
               | Error s0 -> Error s0)
            | _ :: _ ->
              (match ltist_set_msf st res with
               | Ok x -> lti_lcmd asmop x lc'
               | Error s0 -> Error s0))
         | IRpc_save_scratch ->
           (match lc' with
            | [] ->
              (match ltist_get_lti asmop st lir with
               | Ok x -> Ok (x, lc)
               | Error s0 -> Error s0)
            | _ :: _ ->
              (match lti_lcmd asmop st lc' with
               | Ok x -> let (lti, lc'') = x in Ok (lti, (li :: lc''))
               | Error s0 -> Error s0)))
      | _ ->
        (match lc' with
         | [] ->
           (match ltist_get_lti asmop st lir with
            | Ok x -> Ok (x, lc)
            | Error s0 -> Error s0)
         | _ :: _ ->
           (match lti_lcmd asmop st lc' with
            | Ok x -> let (lti, lc'') = x in Ok (lti, (li :: lc''))
            | Error s0 -> Error s0)))
   | Llabel (_, _) ->
     (match lc' with
      | [] ->
        (match ltist_get_lti asmop st lir with
         | Ok x -> Ok (x, lc)
         | Error s -> Error s)
      | _ :: _ ->
        (match lti_lcmd asmop st lc' with
         | Ok x -> let (lti, lc'') = x in Ok (lti, (li :: lc''))
         | Error s -> Error s))
   | LstoreLabel (_, _) ->
     (match lc' with
      | [] ->
        (match ltist_get_lti asmop st lir with
         | Ok x -> Ok (x, lc)
         | Error s -> Error s)
      | _ :: _ ->
        (match lti_lcmd asmop st lc' with
         | Ok x -> let (lti, lc'') = x in Ok (lti, (li :: lc''))
         | Error s -> Error s))
   | Lcond (_, _) ->
     (match lc' with
      | [] ->
        (match ltist_get_lti asmop st lir with
         | Ok x -> Ok (x, lc)
         | Error s -> Error s)
      | _ :: _ ->
        (match lti_lcmd asmop st lc' with
         | Ok x -> let (lti, lc'') = x in Ok (lti, (li :: lc''))
         | Error s -> Error s))
   | _ ->
     (match lc' with
      | [] ->
        (match ltist_get_lti asmop st lir with
         | Ok x -> Ok (x, lc)
         | Error s -> Error s)
      | _ :: _ ->
        (match lti_lcmd asmop st lc' with
         | Ok x -> let (lti, lc'') = x in Ok (lti, (li :: lc''))
         | Error s -> Error s)))

(** val lti_lfd :
    'a1 asmOp -> funname list -> lti_table -> funname -> 'a1 lfundef ->
    (lti_table * (funname * 'a1 lfundef)) cexec **)

let lti_lfd asmop export_fs tbl fn lfd =
  if in_mem (Obj.magic fn)
       (mem (seq_predType funname_eqType) (Obj.magic export_fs))
  then Ok (tbl, (fn, lfd))
  else (match lti_lcmd asmop ltist_empty lfd.lfd_body with
        | Ok x ->
          let (lti, lbody') = x in
          Ok ((Mf.set tbl (Obj.magic fn) lti), (fn,
          (with_lbody asmop lfd lbody')))
        | Error s -> Error s)

(** val lti_lfuncs :
    'a1 asmOp -> funname list -> (funname * 'a1 lfundef) list ->
    (lti_table * (funname * 'a1 lfundef) list) cexec **)

let lti_lfuncs asmop export_fs lfuncs =
  fmapM (fun tbl pat ->
    let (fn, lfd) = pat in lti_lfd asmop export_fs tbl fn lfd) Mf.empty lfuncs

type save_tag_args =
| STAstack of var_i
| STAregister of var_i
| STAextra_register of var_i * var_i

type load_tag_args =
| LTAstack of var_i * var_i * var_i
| LTAregister of var_i
| LTAextra_register of var_i * var_i

type 'asm_op protect_calls_params = { pcp_is_update_after_call : ('asm_op
                                                                 sopn -> bool);
                                      pcp_lower_update_after_call : ((char list
                                                                    option ->
                                                                    pp_error_loc)
                                                                    -> coq_Z
                                                                    -> var_i
                                                                    ->
                                                                    cs_info
                                                                    bintree
                                                                    -> lexpr
                                                                    list ->
                                                                    rexpr
                                                                    list ->
                                                                    ((lexpr
                                                                    list * 'asm_op
                                                                    sopn) * rexpr
                                                                    list)
                                                                    list
                                                                    cexec);
                                      pcp_load_tag : ((char list option ->
                                                     pp_error_loc) ->
                                                     load_tag_args ->
                                                     (var_i * ((lexpr
                                                     list * 'asm_op
                                                     sopn) * rexpr list)
                                                     list) cexec);
                                      pcp_cmpi : ((char list option ->
                                                 pp_error_loc) -> var_i ->
                                                 coq_Z -> ((lexpr
                                                 list * 'asm_op sopn) * rexpr
                                                 list) cexec);
                                      pcp_cond_ne : fexpr;
                                      pcp_cond_gt : fexpr;
                                      pcp_save_ra : ((char list option ->
                                                    pp_error_loc) ->
                                                    save_tag_args -> coq_Z ->
                                                    ((lexpr list * 'asm_op
                                                    sopn) * rexpr list) list
                                                    cexec) }

(** val lcond_remote :
    'a1 asmOp -> fexpr -> label -> remote_label -> 'a1 linstr_r list cexec **)

let lcond_remote _ cond lbl_fresh lbl_remote =
  Ok ((Lcond (cond, lbl_fresh)) :: ((Lgoto lbl_remote) :: ((Llabel
    (InternalLabel, lbl_fresh)) :: [])))

(** val lcmd_of_tree :
    'a1 asmOp -> 'a1 protect_calls_params -> instr_info -> var_i -> label ->
    cs_info bintree -> ('a1 linstr_r list * label) cexec **)

let rec lcmd_of_tree asmop pcparams ii ra lbl = function
| BTleaf -> Ok ([], lbl)
| BTnode (c, t1, t2) ->
  let (ret_lbl, tag) = c in
  (match t1 with
   | BTleaf ->
     (match t2 with
      | BTleaf -> Ok (((Lgoto ret_lbl) :: []), lbl)
      | BTnode (_, _, _) ->
        (match pcparams.pcp_cmpi (E.lower_ret_failed ii) ra tag with
         | Ok x ->
           (match lcond_remote asmop pcparams.pcp_cond_ne lbl ret_lbl with
            | Ok x0 ->
              (match lcmd_of_tree asmop pcparams ii ra (next_lbl lbl) t1 with
               | Ok x1 ->
                 let (lcmd_t0, lbl0) = x1 in
                 (match lcmd_of_tree asmop pcparams ii ra (next_lbl lbl0) t2 with
                  | Ok x2 ->
                    let (lcmd_t1, lbl1) = x2 in
                    if (||) (is_nil lcmd_t0) (is_nil lcmd_t1)
                    then let p = ([], []) in
                         let (jmp_gt, lbl_gt) = p in
                         let lc =
                           (lir_of_fopn_args asmop x) :: (cat x0
                                                           (cat jmp_gt
                                                             (cat lcmd_t0
                                                               (cat lbl_gt
                                                                 lcmd_t1))))
                         in
                         Ok (lc, lbl1)
                    else let p = (((Lcond (pcparams.pcp_cond_gt,
                           lbl1)) :: []), ((Llabel (InternalLabel,
                           lbl1)) :: []))
                         in
                         let lbl2 = next_lbl lbl1 in
                         let (jmp_gt, lbl_gt) = p in
                         let lc =
                           (lir_of_fopn_args asmop x) :: (cat x0
                                                           (cat jmp_gt
                                                             (cat lcmd_t0
                                                               (cat lbl_gt
                                                                 lcmd_t1))))
                         in
                         Ok (lc, lbl2)
                  | Error s -> Error s)
               | Error s -> Error s)
            | Error s -> Error s)
         | Error s -> Error s))
   | BTnode (_, _, _) ->
     (match pcparams.pcp_cmpi (E.lower_ret_failed ii) ra tag with
      | Ok x ->
        (match lcond_remote asmop pcparams.pcp_cond_ne lbl ret_lbl with
         | Ok x0 ->
           (match lcmd_of_tree asmop pcparams ii ra (next_lbl lbl) t1 with
            | Ok x1 ->
              let (lcmd_t0, lbl0) = x1 in
              (match lcmd_of_tree asmop pcparams ii ra (next_lbl lbl0) t2 with
               | Ok x2 ->
                 let (lcmd_t1, lbl1) = x2 in
                 if (||) (is_nil lcmd_t0) (is_nil lcmd_t1)
                 then let p = ([], []) in
                      let (jmp_gt, lbl_gt) = p in
                      let lc =
                        (lir_of_fopn_args asmop x) :: (cat x0
                                                        (cat jmp_gt
                                                          (cat lcmd_t0
                                                            (cat lbl_gt
                                                              lcmd_t1))))
                      in
                      Ok (lc, lbl1)
                 else let p = (((Lcond (pcparams.pcp_cond_gt, lbl1)) :: []),
                        ((Llabel (InternalLabel, lbl1)) :: []))
                      in
                      let lbl2 = next_lbl lbl1 in
                      let (jmp_gt, lbl_gt) = p in
                      let lc =
                        (lir_of_fopn_args asmop x) :: (cat x0
                                                        (cat jmp_gt
                                                          (cat lcmd_t0
                                                            (cat lbl_gt
                                                              lcmd_t1))))
                      in
                      Ok (lc, lbl2)
               | Error s -> Error s)
            | Error s -> Error s)
         | Error s -> Error s)
      | Error s -> Error s))

(** val return_table :
    'a1 asmOp -> 'a1 protect_calls_params -> (funname -> cs_info list ->
    cs_info bintree) -> instr_info -> funname -> load_tag_args -> cst_value
    -> 'a1 linstr_r list cexec **)

let return_table asmop pcparams return_tree ii callee lta = function
| (ris, max_lbl) ->
  (match pcparams.pcp_load_tag (E.lower_ret_failed ii) lta with
   | Ok x ->
     let (ra, args) = x in
     let t0 = return_tree callee ris in
     (match lcmd_of_tree asmop pcparams ii ra (next_lbl max_lbl) t0 with
      | Ok x0 ->
        let (lc, _) = x0 in
        let pop =
          match lc with
          | [] -> map (lir_of_fopn_args asmop) args
          | y :: l ->
            (match y with
             | Lgoto _ ->
               (match l with
                | [] -> []
                | _ :: _ -> map (lir_of_fopn_args asmop) args)
             | _ -> map (lir_of_fopn_args asmop) args)
        in
        (match let is_label = fun i ->
                 match i with
                 | Lopn (_, _, _) -> None
                 | Lsyscall _ -> None
                 | Lcall (_, _) -> None
                 | Lret -> None
                 | Lalign -> None
                 | Llabel (_, lbl) -> Some lbl
                 | _ -> None
               in
               let is_jump = fun i ->
                 match i with
                 | Lopn (_, _, _) -> None
                 | Lsyscall _ -> None
                 | Lcall (_, _) -> None
                 | Lret -> None
                 | Lalign -> None
                 | Llabel (_, _) -> None
                 | Lgoto lbl -> Some lbl
                 | _ -> None
               in
               let lbls = pmap is_label lc in
               let remote_lbls = map fst ris in
               let targets = pmap is_jump lc in
               if (&&) (uniq pos_eqType (Obj.magic lbls))
                    ((&&)
                      (all (fun l ->
                        in_mem (Obj.magic l)
                          (mem
                            (seq_predType
                              (prod_eqType funname_eqType pos_eqType))
                            (Obj.magic remote_lbls))) targets)
                      (all (fun l ->
                        in_mem (Obj.magic l)
                          (mem
                            (seq_predType
                              (prod_eqType funname_eqType pos_eqType))
                            (Obj.magic targets))) remote_lbls))
               then Ok ()
               else Error
                      (E.lower_ret_failed ii (Some
                        ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))) with
         | Ok _ -> Ok (cat pop lc)
         | Error s -> Error s)
      | Error s -> Error s)
   | Error s -> Error s)

(** val fn_csi : cs_table -> funname -> cst_value **)

let fn_csi =
  cst_lookup

(** val get_lta : var_i -> lti_table -> funname -> load_tag_args cexec **)

let get_lta rsp lti_tbl fn =
  match Mf.get lti_tbl (Obj.magic fn) with
  | Some l ->
    (match l with
     | LTIstack (r, msf) -> Ok (LTAstack (rsp, r, msf))
     | LTIregister r -> Ok (LTAregister r)
     | LTIextra_register (rx, r) -> Ok (LTAextra_register (rx, r)))
  | None -> Error E.cant_get_lta

(** val do_ret :
    'a1 asmOp -> 'a1 protect_calls_params -> (funname -> cs_info list ->
    cs_info bintree) -> var_i -> lti_table -> funname -> instr_info ->
    cst_value -> 'a1 lcmd cexec **)

let do_ret asmop pcparams return_tree rsp lti_tbl fn ii csi =
  match let (l, _) = csi in
        (match l with
         | [] ->
           Error
             (E.lower_ret_failed ii (Some
               ('e'::('m'::('p'::('t'::('y'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))
         | _ :: _ ->
           (match get_lta rsp lti_tbl fn with
            | Ok x -> return_table asmop pcparams return_tree ii fn x csi
            | Error s -> Error s)) with
  | Ok x -> Ok (map (fun x0 -> { li_ii = ii; li_i = x0 }) x)
  | Error s -> Error s

(** val do_ret_li :
    'a1 asmOp -> 'a1 protect_calls_params -> (funname -> cs_info list ->
    cs_info bintree) -> var_i -> cs_table -> lti_table -> funname -> 'a1
    linstr -> 'a1 lcmd cexec **)

let do_ret_li asmop pcparams return_tree rsp cs_tbl lti_tbl fn li =
  let { li_ii = ii; li_i = li_i0 } = li in
  (match li_i0 with
   | Lret ->
     do_ret asmop pcparams return_tree rsp lti_tbl fn ii (fn_csi cs_tbl fn)
   | Ligoto _ ->
     do_ret asmop pcparams return_tree rsp lti_tbl fn ii (fn_csi cs_tbl fn)
   | _ -> Ok (li :: []))

(** val do_ret_lcmd :
    'a1 asmOp -> 'a1 protect_calls_params -> (funname -> cs_info list ->
    cs_info bintree) -> var_i -> cs_table -> lti_table -> funname -> 'a1 lcmd
    -> 'a1 lcmd cexec **)

let do_ret_lcmd asmop pcparams return_tree rsp cs_tbl lti_tbl fn lc =
  conc_mapM (do_ret_li asmop pcparams return_tree rsp cs_tbl lti_tbl fn) lc

type state =
| STempty
| STscratch of var_i
| STupdate_args of cs_info list * coq_Z * var_i

(** val get_sta : var_i -> state -> var_i option -> save_tag_args * state **)

let get_sta rsp st = function
| Some r ->
  (match st with
   | STscratch r0 -> ((STAextra_register (r, r0)), STempty)
   | _ -> ((STAregister r), st))
| None -> ((STAstack rsp), st)

(** val get_update_args :
    state -> (((cs_info list * coq_Z) * var_i) * state) cexec **)

let get_update_args = function
| STupdate_args (ris, tag, r) -> Ok (((ris, tag), r), STempty)
| _ -> Error E.invalid_state

(** val set_scratch : lexpr list -> state cexec **)

let set_scratch = function
| [] -> Error E.invalid_use_vars
| l :: l0 ->
  (match l with
   | Store (_, _, _) -> Error E.invalid_use_vars
   | LLvar r ->
     (match l0 with
      | [] -> Ok (STscratch r)
      | _ :: _ -> Error E.invalid_use_vars))

(** val set_update_args :
    state -> cs_info list -> coq_Z -> var_i -> state cexec **)

let set_update_args st ris tag r =
  match st with
  | STempty -> Ok (STupdate_args (ris, tag, r))
  | _ -> Error E.invalid_state

(** val get_tag_reg : lti_table -> funname -> var_i cexec **)

let get_tag_reg lti_tbl callee =
  match Mf.get lti_tbl (Obj.magic callee) with
  | Some l ->
    (match l with
     | LTIstack (r, _) -> Ok r
     | LTIregister r -> Ok r
     | LTIextra_register (_, r) -> Ok r)
  | None -> Error E.cant_get_tag_reg

(** val do_call :
    'a1 asmOp -> 'a1 protect_calls_params -> var_i -> cs_table -> lti_table
    -> funname -> instr_info -> state -> var_i option -> remote_label ->
    label -> ('a1 lcmd * state) cexec **)

let do_call asmop pcparams rsp cs_tbl lti_tbl fn ii st ra_loc callee ret_lbl =
  let (ris, _) = cst_lookup cs_tbl (fst callee) in
  (match o2r E.assoc_failed
           (assoc (prod_eqType funname_eqType pos_eqType) (Obj.magic ris)
             (Obj.magic (fn, ret_lbl))) with
   | Ok x ->
     let (sta, st') = get_sta rsp st ra_loc in
     (match ris with
      | [] ->
        let s =
          E.save_tag_failed ii (Some
            ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))
        in
        Error s
      | _ :: l ->
        (match l with
         | [] ->
           let x0 = [] in
           let lc = rcons x0 { li_ii = ii; li_i = (Lgoto callee) } in
           (match get_tag_reg lti_tbl (fst callee) with
            | Ok x1 ->
              (match set_update_args st' ris x x1 with
               | Ok x2 -> Ok (lc, x2)
               | Error s -> Error s)
            | Error s -> Error s)
         | _ :: _ ->
           (match pcparams.pcp_save_ra (E.save_tag_failed ii) sta x with
            | Ok x0 ->
              let x1 = map (li_of_fopn_args asmop ii) x0 in
              let lc = rcons x1 { li_ii = ii; li_i = (Lgoto callee) } in
              (match get_tag_reg lti_tbl (fst callee) with
               | Ok x2 ->
                 (match set_update_args st' ris x x2 with
                  | Ok x3 -> Ok (lc, x3)
                  | Error s -> Error s)
               | Error s -> Error s)
            | Error s -> Error s)))
   | Error s -> Error s)

(** val do_update_after_call :
    'a1 asmOp -> 'a1 protect_calls_params -> (funname -> cs_info list ->
    cs_info bintree) -> funname -> instr_info -> state -> lexpr list -> rexpr
    list -> ('a1 lcmd * state) cexec **)

let do_update_after_call asmop pcparams return_tree fn ii st les res =
  let err = E.lower_update_after_call_failed ii in
  (match get_update_args st with
   | Ok x ->
     let (y, st') = x in
     let (y0, r) = y in
     let (ris, tag) = y0 in
     let t0 = return_tree fn ris in
     (match pcparams.pcp_lower_update_after_call err tag r t0 les res with
      | Ok x0 -> Ok ((map (li_of_fopn_args asmop ii) x0), st')
      | Error s -> Error s)
   | Error s -> Error s)

(** val do_call_lcmd :
    'a1 asmOp -> 'a1 protect_calls_params -> (funname -> cs_info list ->
    cs_info bintree) -> var_i -> cs_table -> lti_table -> funname -> state ->
    'a1 lcmd -> 'a1 lcmd cexec **)

let rec do_call_lcmd asmop pcparams return_tree rsp cs_tbl lti_tbl fn st = function
| [] -> Ok []
| li :: lc0 ->
  let { li_ii = ii; li_i = li_i0 } = li in
  (match li_i0 with
   | Lopn (les, op, res) ->
     (match op with
      | Ointernal i ->
        let Ouse_vars (i0, _, _) = i in
        (match i0 with
         | IRpc_save_scratch ->
           (match set_scratch les with
            | Ok x ->
              do_call_lcmd asmop pcparams return_tree rsp cs_tbl lti_tbl fn x
                lc0
            | Error s -> Error s)
         | _ ->
           (match if pcparams.pcp_is_update_after_call op
                  then do_update_after_call asmop pcparams return_tree fn ii
                         st les res
                  else Ok ((li :: []), st) with
            | Ok x ->
              let (cmd_update, st') = x in
              (match do_call_lcmd asmop pcparams return_tree rsp cs_tbl
                       lti_tbl fn st' lc0 with
               | Ok x0 -> Ok (cat cmd_update x0)
               | Error s -> Error s)
            | Error s -> Error s))
      | _ ->
        (match if pcparams.pcp_is_update_after_call op
               then do_update_after_call asmop pcparams return_tree fn ii st
                      les res
               else Ok ((li :: []), st) with
         | Ok x ->
           let (cmd_update, st') = x in
           (match do_call_lcmd asmop pcparams return_tree rsp cs_tbl lti_tbl
                    fn st' lc0 with
            | Ok x0 -> Ok (cat cmd_update x0)
            | Error s -> Error s)
         | Error s -> Error s))
   | Lcall (ra_loc, callee) ->
     (match lc0 with
      | [] ->
        (match do_call_lcmd asmop pcparams return_tree rsp cs_tbl lti_tbl fn
                 st lc0 with
         | Ok x -> Ok (li :: x)
         | Error s -> Error s)
      | li_ret_lbl :: lc1 ->
        let { li_ii = _; li_i = li_i1 } = li_ret_lbl in
        (match li_i1 with
         | Llabel (l, ret_lbl) ->
           (match l with
            | InternalLabel ->
              (match do_call_lcmd asmop pcparams return_tree rsp cs_tbl
                       lti_tbl fn st lc0 with
               | Ok x -> Ok (li :: x)
               | Error s -> Error s)
            | ExternalLabel ->
              (match do_call asmop pcparams rsp cs_tbl lti_tbl fn ii st
                       ra_loc callee ret_lbl with
               | Ok x ->
                 let (cmd_call, st') = x in
                 (match do_call_lcmd asmop pcparams return_tree rsp cs_tbl
                          lti_tbl fn st' lc1 with
                  | Ok x0 -> Ok (cat cmd_call (li_ret_lbl :: x0))
                  | Error s -> Error s)
               | Error s -> Error s))
         | _ ->
           (match do_call_lcmd asmop pcparams return_tree rsp cs_tbl lti_tbl
                    fn st lc0 with
            | Ok x -> Ok (li :: x)
            | Error s -> Error s)))
   | _ ->
     (match do_call_lcmd asmop pcparams return_tree rsp cs_tbl lti_tbl fn st
              lc0 with
      | Ok x -> Ok (li :: x)
      | Error s -> Error s))

(** val pc_lfd :
    'a1 asmOp -> 'a1 protect_calls_params -> (funname -> cs_info list ->
    cs_info bintree) -> funname list -> var_i -> cs_table -> lti_table ->
    funname -> 'a1 lfundef -> 'a1 lfundef cexec **)

let pc_lfd asmop pcparams return_tree export_fs rsp cs_tbl lti_tbl fn lfd =
  match if in_mem (Obj.magic fn)
             (mem (seq_predType funname_eqType) (Obj.magic export_fs))
        then Ok lfd.lfd_body
        else do_ret_lcmd asmop pcparams return_tree rsp cs_tbl lti_tbl fn
               lfd.lfd_body with
  | Ok x ->
    (match do_call_lcmd asmop pcparams return_tree rsp cs_tbl lti_tbl fn
             STempty x with
     | Ok x0 -> Ok (with_lbody asmop lfd x0)
     | Error s -> Error s)
  | Error s -> Error s

(** val chk_f : 'a1 asmOp -> 'a1 lprog -> funname -> cst_value -> bool **)

let chk_f _ =
  let get_label = fun i ->
    match i.li_i with
    | Lopn (_, _, _) -> None
    | Lsyscall _ -> None
    | Lcall (_, _) -> None
    | Lret -> None
    | Lalign -> None
    | Llabel (_, lbl) -> Some lbl
    | _ -> None
  in
  let labels_in_lcmd = fun body -> pmap get_label body in
  let is_max_label_in_fbody = fun lp fn l ->
    match get_fundef lp.lp_funcs fn with
    | Some fd -> all (fun x -> Pos.leb x l) (labels_in_lcmd fd.lfd_body)
    | None -> false
  in
  (fun lp fn v ->
  let (s, max_lbl) = v in
  let tags = map snd s in
  (&&)
    (eq_op (seq_eqType coq_Z_eqType) (Obj.magic sort Z.ltb tags)
      (Obj.magic ziota Z0 (int_to_Z (Posz (size tags)))))
    (is_max_label_in_fbody lp fn max_lbl))

(** val pc_lprog :
    coq_PointerData -> 'a1 asmOp -> 'a1 protect_calls_params -> (funname ->
    cs_info list -> cs_info bintree) -> funname list -> bool -> 'a1 lprog ->
    'a1 lprog cexec **)

let pc_lprog pd asmop pcparams return_tree export_fs protect_calls lp =
  if protect_calls
  then let cs_tbl = call_sites_table asmop lp in
       if Mf.all (Obj.magic chk_f asmop lp) cs_tbl
       then (match lti_lfuncs asmop export_fs lp.lp_funcs with
             | Ok x ->
               let (lti_tbl, lfuncs) = x in
               let f =
                 pc_lfd asmop pcparams return_tree export_fs
                   (mk_var_i { Var.vtype = (Coq_sword (coq_Uptr pd));
                     Var.vname = lp.lp_rsp }) cs_tbl lti_tbl
               in
               (match map_cfprog_name_gen (fun l -> l.lfd_info) f lfuncs with
                | Ok x0 -> Ok (with_lfds asmop lp x0)
                | Error s -> Error s)
             | Error s -> Error s)
       else Error E.debug
  else Ok lp
