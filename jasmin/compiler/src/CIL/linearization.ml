open BinInt
open BinNums
open BinPos
open Datatypes
open Compiler_util
open Constant_prop
open Eqtype
open Expr
open Fexpr
open Label
open Linear
open Linear_util
open Memory_model
open Oseq
open Seq
open Sopn
open Ssralg
open Ssrbool
open Ssrfun
open Ssrint
open Ssrnat
open Type
open Utils0
open Var0
open Word0
open Word_ssrZ
open Wsize

module E =
 struct
  (** val pass_name : char list **)

  let pass_name =
    'l'::('i'::('n'::('e'::('a'::('r'::('i'::('z'::('a'::('t'::('i'::('o'::('n'::[]))))))))))))

  (** val my_error : pp_error -> pp_error_loc **)

  let my_error msg =
    { pel_msg = msg; pel_fn = None; pel_fi = None; pel_ii = None; pel_vi =
      None; pel_pass = (Some pass_name); pel_internal = false }

  (** val gen_error :
      bool -> instr_info option -> pp_error -> pp_error_loc **)

  let gen_error internal ii msg =
    { pel_msg = msg; pel_fn = None; pel_fi = None; pel_ii = ii; pel_vi =
      None; pel_pass = (Some pass_name); pel_internal = internal }

  (** val ii_error : instr_info -> char list -> pp_error_loc **)

  let ii_error ii msg =
    gen_error false (Some ii) (PPEstring msg)

  (** val error : char list -> pp_error_loc **)

  let error msg =
    gen_error false None (PPEstring msg)

  (** val internal_error : char list -> pp_error_loc **)

  let internal_error msg =
    gen_error true None (PPEstring msg)

  (** val assign_remains : instr_info -> lval -> pexpr -> pp_error_loc **)

  let assign_remains ii lv e =
    gen_error false (Some ii)
      (pp_nobox ((PPEstring
        ('T'::('h'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('a'::('s'::('s'::('i'::('g'::('n'::('m'::('e'::('n'::('t'::(' '::('r'::('e'::('m'::('a'::('i'::('n'::('s'::(':'::[])))))))))))))))))))))))))))))))))) :: (PPEbreak :: ((PPElval
        lv) :: ((PPEstring (' '::('='::(' '::[])))) :: ((PPEexpr
        e) :: (PPEbreak :: ((PPEstring
        ('I'::('s'::(' '::('t'::('h'::('e'::('r'::('e'::(' '::('a'::('n'::(' '::('i'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('i'::('o'::('n'::(' '::('i'::('n'::(' '::('t'::('h'::('e'::(' '::('t'::('a'::('r'::('g'::('e'::('t'::(' '::('a'::('r'::('c'::('h'::('i'::('t'::('e'::('c'::('t'::('u'::('r'::('e'::(' '::('t'::('h'::('a'::('t'::(' '::('c'::('a'::('n'::(' '::('i'::('m'::('p'::('l'::('e'::('m'::('e'::('n'::('t'::(' '::('i'::('t'::('?'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: (PPEbreak :: ((PPEstring
        ('M'::('o'::('r'::('e'::(' '::('i'::('n'::('f'::('o'::('r'::('m'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('a'::('y'::(' '::('b'::('e'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('o'::('n'::('l'::('i'::('n'::('e'::(':'::(' '::('h'::('t'::('t'::('p'::('s'::(':'::('/'::('/'::('g'::('i'::('t'::('h'::('u'::('b'::('.'::('c'::('o'::('m'::('/'::('j'::('a'::('s'::('m'::('i'::('n'::('-'::('l'::('a'::('n'::('g'::('/'::('j'::('a'::('s'::('m'::('i'::('n'::('/'::('w'::('i'::('k'::('i'::('/'::('F'::('A'::('Q'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []))))))))))
 end

type 'asm_op linearization_params = { lip_tmp : Ident.Ident.ident;
                                      lip_tmp2 : Ident.Ident.ident;
                                      lip_not_saved_stack : Ident.Ident.ident
                                                            list;
                                      lip_allocate_stack_frame : (var_i ->
                                                                 var_i option
                                                                 -> coq_Z ->
                                                                 ((lexpr
                                                                 list * 'asm_op
                                                                 sopn) * rexpr
                                                                 list) list);
                                      lip_free_stack_frame : (var_i -> var_i
                                                             option -> coq_Z
                                                             -> ((lexpr
                                                             list * 'asm_op
                                                             sopn) * rexpr
                                                             list) list);
                                      lip_set_up_sp_register : (var_i ->
                                                               coq_Z -> wsize
                                                               -> var_i ->
                                                               var_i ->
                                                               ((lexpr
                                                               list * 'asm_op
                                                               sopn) * rexpr
                                                               list) list);
                                      lip_lmove : (var_i -> var_i -> (lexpr
                                                  list * 'asm_op
                                                  sopn) * rexpr list);
                                      lip_check_ws : (wsize -> bool);
                                      lip_lstore : (var_i -> coq_Z -> var_i
                                                   -> (lexpr list * 'asm_op
                                                   sopn) * rexpr list);
                                      lip_lstores : (var_i ->
                                                    (Var.var * coq_Z) list ->
                                                    ((lexpr list * 'asm_op
                                                    sopn) * rexpr list) list);
                                      lip_lloads : (var_i ->
                                                   (Var.var * coq_Z) list ->
                                                   coq_Z -> ((lexpr
                                                   list * 'asm_op
                                                   sopn) * rexpr list) list) }

(** val lstores_dfl :
    'a1 asmOp -> (var_i -> coq_Z -> var_i -> (lexpr list * 'a1 sopn) * rexpr
    list) -> var_i -> (Var.var * coq_Z) list -> ((lexpr list * 'a1
    sopn) * rexpr list) list **)

let lstores_dfl _ lip_lstore0 rsp to_save =
  map (fun pat ->
    let (x, ofs) = pat in
    lip_lstore0 rsp ofs { v_var = x; v_info = dummy_var_info }) to_save

(** val lstores_imm_dfl :
    coq_PointerData -> 'a1 asmOp -> Ident.Ident.ident -> (var_i -> coq_Z ->
    var_i -> (lexpr list * 'a1 sopn) * rexpr list) -> (var_i -> var_i ->
    coq_Z -> ((lexpr list * 'a1 sopn) * rexpr list) list) -> (coq_Z -> bool)
    -> var_i -> (Var.var * coq_Z) list -> ((lexpr list * 'a1 sopn) * rexpr
    list) list **)

let lstores_imm_dfl pd asmop lip_tmp3 lip_lstore0 lip_add_imm lip_imm_small rsp to_save =
  if all (fun pat -> let (_, ofs) = pat in lip_imm_small ofs) to_save
  then lstores_dfl asmop lip_lstore0 rsp to_save
  else let ofs0 = snd (head (rsp.v_var, Z0) to_save) in
       let tmp2 = { v_var = { Var.vtype = (Coq_sword (coq_Uptr pd));
         Var.vname = lip_tmp3 }; v_info = dummy_var_info }
       in
       let to_save0 =
         map (fun pat -> let (x, ofs) = pat in (x, (Z.sub ofs ofs0))) to_save
       in
       cat (lip_add_imm tmp2 rsp ofs0)
         (lstores_dfl asmop lip_lstore0 tmp2 to_save0)

(** val lloads_aux :
    'a1 asmOp -> (var_i -> var_i -> coq_Z -> (lexpr list * 'a1 sopn) * rexpr
    list) -> var_i -> (Var.var * coq_Z) list -> ((lexpr list * 'a1
    sopn) * rexpr list) list **)

let lloads_aux _ lip_lload rsp to_restore =
  map (fun pat ->
    let (x, ofs) = pat in
    lip_lload { v_var = x; v_info = dummy_var_info } rsp ofs) to_restore

(** val lloads_dfl :
    'a1 asmOp -> (var_i -> var_i -> coq_Z -> (lexpr list * 'a1 sopn) * rexpr
    list) -> var_i -> (Var.var * coq_Z) list -> coq_Z -> ((lexpr list * 'a1
    sopn) * rexpr list) list **)

let lloads_dfl asmop lip_lload rsp to_restore spofs =
  lloads_aux asmop lip_lload rsp (cat to_restore ((rsp.v_var, spofs) :: []))

(** val lloads_imm_dfl :
    coq_PointerData -> 'a1 asmOp -> Ident.Ident.ident -> (var_i -> var_i ->
    coq_Z -> (lexpr list * 'a1 sopn) * rexpr list) -> (var_i -> var_i ->
    coq_Z -> ((lexpr list * 'a1 sopn) * rexpr list) list) -> (coq_Z -> bool)
    -> var_i -> (Var.var * coq_Z) list -> coq_Z -> ((lexpr list * 'a1
    sopn) * rexpr list) list **)

let lloads_imm_dfl pd asmop lip_tmp3 lip_lload lip_add_imm lip_imm_small rsp to_restore spofs =
  let to_restore0 = cat to_restore ((rsp.v_var, spofs) :: []) in
  if all (fun pat -> let (_, ofs) = pat in lip_imm_small ofs) to_restore0
  then lloads_aux asmop lip_lload rsp to_restore0
  else let ofs0 = snd (head (rsp.v_var, Z0) to_restore0) in
       let tmp2 = { v_var = { Var.vtype = (Coq_sword (coq_Uptr pd));
         Var.vname = lip_tmp3 }; v_info = dummy_var_info }
       in
       let to_restore1 =
         map (fun pat -> let (x, ofs) = pat in (x, (Z.sub ofs ofs0)))
           to_restore0
       in
       cat (lip_add_imm tmp2 rsp ofs0)
         (lloads_aux asmop lip_lload tmp2 to_restore1)

(** val lmove :
    'a1 asmOp -> 'a1 linearization_params -> var_i -> var_i -> 'a1 linstr **)

let lmove asmop liparams rd rs =
  li_of_fopn_args asmop dummy_instr_info (liparams.lip_lmove rd rs)

(** val lstore :
    'a1 asmOp -> 'a1 linearization_params -> var_i -> coq_Z -> var_i -> 'a1
    linstr **)

let lstore asmop liparams rd ofs rs =
  li_of_fopn_args asmop dummy_instr_info (liparams.lip_lstore rd ofs rs)

(** val set_up_sp_register :
    'a1 asmOp -> 'a1 linearization_params -> var_i -> coq_Z -> wsize -> var_i
    -> var_i -> 'a1 lcmd **)

let set_up_sp_register asmop liparams vrspi sf_sz al r tmp =
  map (li_of_fopn_args asmop dummy_instr_info)
    (liparams.lip_set_up_sp_register vrspi sf_sz al r tmp)

(** val check_Some :
    (char list -> 'a1) -> ('a2 -> 'a3 option) -> char list -> 'a2 -> ('a1,
    unit) result **)

let check_Some error0 conv msg a =
  if isSome (conv a) then Ok () else Error (error0 msg)

(** val to_fexpr : pexpr -> fexpr **)

let to_fexpr e =
  match fexpr_of_pexpr e with
  | Some r -> r
  | None -> Fconst Z0

(** val check_fexpr : instr_info -> pexpr -> (pp_error_loc, unit) result **)

let check_fexpr ii =
  let error0 = fun msg -> E.gen_error true (Some ii) (PPEstring msg) in
  check_Some error0 fexpr_of_pexpr
    ('c'::('h'::('e'::('c'::('k'::('_'::('f'::('e'::('x'::('p'::('r'::[])))))))))))

(** val check_rexpr : instr_info -> pexpr -> (pp_error_loc, unit) result **)

let check_rexpr ii =
  let error0 = fun msg -> E.gen_error true (Some ii) (PPEstring msg) in
  check_Some error0 rexpr_of_pexpr
    ('c'::('h'::('e'::('c'::('k'::('_'::('r'::('e'::('x'::('p'::('r'::[])))))))))))

(** val check_lexpr : instr_info -> lval -> (pp_error_loc, unit) result **)

let check_lexpr ii =
  let error0 = fun msg -> E.gen_error true (Some ii) (PPEstring msg) in
  check_Some error0 lexpr_of_lval
    ('c'::('h'::('e'::('c'::('k'::('_'::('l'::('e'::('x'::('p'::('r'::[])))))))))))

(** val ovar_of_ra : return_address_location -> Var.var option **)

let ovar_of_ra = function
| RAnone -> None
| RAreg (ra0, _) -> Some ra0
| RAstack (ra0, _, _) -> ra0

(** val ovari_of_ra : return_address_location -> var_i option **)

let ovari_of_ra ra =
  Ssrfun.Option.map mk_var_i (ovar_of_ra ra)

(** val tmp_of_ra : return_address_location -> Var.var option **)

let tmp_of_ra = function
| RAnone -> None
| RAreg (_, o) -> o
| RAstack (_, _, o) -> o

(** val tmpi_of_ra : return_address_location -> var_i option **)

let tmpi_of_ra ra =
  Ssrfun.Option.map mk_var_i (tmp_of_ra ra)

(** val stack_frame_allocation_size : stk_fun_extra -> coq_Z **)

let stack_frame_allocation_size e =
  round_ws e.sf_align (Z.add e.sf_stk_sz e.sf_stk_extra_sz)

(** val frame_size : stk_fun_extra -> coq_Z **)

let frame_size e =
  if is_RAnone e.sf_return_address
  then Z.add e.sf_stk_sz e.sf_stk_extra_sz
  else stack_frame_allocation_size e

(** val push_to_save :
    coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
    (Var.var * coq_Z) list -> (Var.var * coq_Z) -> 'a1 lcmd **)

let push_to_save pd asmop liparams p to_save sp =
  map (li_of_fopn_args asmop dummy_instr_info)
    (liparams.lip_lstores
      (mk_var_i { Var.vtype = (Coq_sword (coq_Uptr pd)); Var.vname =
        (Obj.magic p).p_extra.sp_rsp }) (cat to_save (sp :: [])))

(** val pop_to_save :
    coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
    (Var.var * coq_Z) list -> coq_Z -> 'a1 lcmd **)

let pop_to_save pd asmop liparams p to_save sp =
  map (li_of_fopn_args asmop dummy_instr_info)
    (liparams.lip_lloads
      (mk_var_i { Var.vtype = (Coq_sword (coq_Uptr pd)); Var.vname =
        (Obj.magic p).p_extra.sp_rsp }) to_save sp)

(** val check_c :
    'a1 asmOp -> ('a1 instr -> unit cexec) -> 'a1 instr list -> unit cexec **)

let rec check_c asmop check_i0 = function
| [] -> Ok ()
| i :: c0 ->
  (match check_c asmop check_i0 c0 with
   | Ok _ -> check_i0 i
   | Error s -> Error s)

(** val check_i :
    coq_PointerData -> 'a1 asmOp -> 'a1 sprog -> funname -> stk_fun_extra ->
    'a1 instr -> unit cexec **)

let rec check_i pd asmop p this e_caller = function
| MkI (ii, ir) ->
  (match ir with
   | Cassgn (lv, _, _, e) -> Error (E.assign_remains ii lv e)
   | Copn (xs, _, _, es) ->
     (match allM (check_rexpr ii) es with
      | Ok _ -> allM (check_lexpr ii) xs
      | Error s -> Error s)
   | Csyscall (_, _, _) -> Ok ()
   | Cif (b, c1, c2) ->
     (match match check_fexpr ii b with
            | Ok _ -> check_c asmop (check_i pd asmop p this e_caller) c1
            | Error s -> Error s with
      | Ok _ -> check_c asmop (check_i pd asmop p this e_caller) c2
      | Error s -> Error s)
   | Cfor (_, _, _) ->
     Error
       (E.ii_error ii
         ('f'::('o'::('r'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('i'::('n'::(' '::('l'::('i'::('n'::('e'::('a'::('r'::[]))))))))))))))))))))
   | Cwhile (_, c, e, c') ->
     (match is_bool e with
      | Some b ->
        if b
        then (match check_c asmop (check_i pd asmop p this e_caller) c with
              | Ok _ -> check_c asmop (check_i pd asmop p this e_caller) c'
              | Error s -> Error s)
        else check_c asmop (check_i pd asmop p this e_caller) c
      | None ->
        (match match check_fexpr ii e with
               | Ok _ -> check_c asmop (check_i pd asmop p this e_caller) c
               | Error s -> Error s with
         | Ok _ -> check_c asmop (check_i pd asmop p this e_caller) c'
         | Error s -> Error s))
   | Ccall (_, fn, _) ->
     if negb (eq_op funname_eqType (Obj.magic fn) (Obj.magic this))
     then (match get_fundef p.p_funcs fn with
           | Some fd ->
             let e = fd.f_extra in
             if negb (is_RAnone (Obj.magic e).sf_return_address)
             then if cmp_le wsize_cmp (Obj.magic e).sf_align e_caller.sf_align
                  then if Z.leb
                            (Z.add (Obj.magic e).sf_stk_max
                              (frame_size e_caller)) e_caller.sf_stk_max
                       then Ok ()
                       else let s =
                              E.ii_error ii
                                ('m'::('a'::('x'::(' '::('s'::('i'::('z'::('e'::(' '::('p'::('r'::('o'::('b'::('l'::('e'::('m'::[]))))))))))))))))
                            in
                            Error s
                  else let s =
                         E.ii_error ii
                           ('c'::('a'::('l'::('l'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::(' '::('a'::('l'::('i'::('g'::('n'::('m'::('e'::('n'::('t'::(' '::('g'::('r'::('e'::('a'::('t'::('e'::('r'::(' '::('t'::('h'::('a'::('n'::(' '::('c'::('a'::('l'::('l'::('e'::('e'::[])))))))))))))))))))))))))))))))))))))))))
                       in
                       Error s
             else let s =
                    E.ii_error ii
                      ('i'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::(' '::('c'::('a'::('l'::('l'::(' '::('t'::('o'::(' '::('a'::('n'::(' '::('e'::('x'::('p'::('o'::('r'::('t'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))))))))))
                  in
                  Error s
           | None ->
             Error
               (E.ii_error ii
                 ('c'::('a'::('l'::('l'::(' '::('t'::('o'::(' '::('u'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))
     else let s =
            E.ii_error ii
              ('c'::('a'::('l'::('l'::(' '::('t'::('o'::(' '::('s'::('e'::('l'::('f'::[]))))))))))))
          in
          Error s)

(** val check_to_save_slot : (Var.var * coq_Z) -> (coq_Z * wsize) cexec **)

let check_to_save_slot = function
| (x, ofs) ->
  (match is_word_type (Var.vtype x) with
   | Some ws -> Ok (ofs, ws)
   | None ->
     Error
       (E.error
         ('t'::('o'::('-'::('s'::('a'::('v'::('e'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('w'::('o'::('r'::('d'::[])))))))))))))))))))))

(** val all_disjoint_aligned_between :
    coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> coq_Z ->
    coq_Z -> wsize -> (Var.var * coq_Z) list -> unit cexec **)

let all_disjoint_aligned_between pd _ liparams lo hi al m =
  match foldM (fun a base ->
          match check_to_save_slot a with
          | Ok x ->
            let (ofs, ws) = x in
            if Z.leb base ofs
            then if cmp_le wsize_cmp ws al
                 then if is_align (GRing.ComRing.eqType (word (coq_Uptr pd)))
                           (coq_Pointer pd) (wrepr (coq_Uptr pd) ofs) ws
                      then if liparams.lip_check_ws ws
                           then Ok (Z.add ofs (wsize_size ws))
                           else let s =
                                  E.error
                                    ('t'::('o'::('-'::('s'::('a'::('v'::('e'::(':'::(' '::('b'::('a'::('d'::(' '::('w'::('s'::('i'::('z'::('e'::[]))))))))))))))))))
                                in
                                Error s
                      else let s =
                             E.error
                               ('t'::('o'::('-'::('s'::('a'::('v'::('e'::(':'::(' '::('b'::('a'::('d'::(' '::('s'::('l'::('o'::('t'::(' '::('a'::('l'::('i'::('g'::('n'::('e'::('m'::('e'::('n'::('t'::[]))))))))))))))))))))))))))))
                           in
                           Error s
                 else let s =
                        E.error
                          ('t'::('o'::('-'::('s'::('a'::('v'::('e'::(':'::(' '::('b'::('a'::('d'::(' '::('f'::('r'::('a'::('m'::('e'::(' '::('a'::('l'::('i'::('g'::('n'::('e'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))))))))
                      in
                      Error s
            else let s =
                   E.my_error
                     (pp_hov ((PPEstring
                       ('t'::('o'::('-'::('s'::('a'::('v'::('e'::(':'::(' '::('o'::('v'::('e'::('r'::('l'::('a'::('p'::[]))))))))))))))))) :: ((PPEexpr
                       (Pconst base)) :: ((PPEexpr (Pconst ofs)) :: []))))
                 in
                 Error s
          | Error s -> Error s) lo m with
  | Ok x ->
    if Z.leb x hi
    then Ok ()
    else Error
           (E.error
             ('t'::('o'::('-'::('s'::('a'::('v'::('e'::(':'::(' '::('o'::('v'::('e'::('r'::('f'::('l'::('o'::('w'::(' '::('i'::('n'::(' '::('t'::('h'::('e'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('f'::('r'::('a'::('m'::('e'::[])))))))))))))))))))))))))))))))))))))
  | Error s -> Error s

(** val check_to_save :
    coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> stk_fun_extra
    -> unit cexec **)

let check_to_save pd asmop liparams e =
  if is_RAnone e.sf_return_address
  then let stk_size = Z.add e.sf_stk_sz e.sf_stk_extra_sz in
       if match e.sf_save_stack with
          | SavedStackStk ofs ->
            Z.leb (Z.add ofs (wsize_size (coq_Uptr pd))) stk_size
          | _ -> true
       then all_disjoint_aligned_between pd asmop liparams e.sf_stk_sz
              (match e.sf_save_stack with
               | SavedStackStk ofs -> ofs
               | _ -> Z.add e.sf_stk_sz e.sf_stk_extra_sz) e.sf_align
              e.sf_to_save
       else let s =
              E.error
                ('s'::('t'::('a'::('c'::('k'::(' '::('s'::('i'::('z'::('e'::(' '::('t'::('o'::(' '::('s'::('m'::('a'::('l'::('l'::[])))))))))))))))))))
            in
            Error s
  else Ok ()

(** val linear_c :
    'a1 asmOp -> ('a1 instr -> label -> 'a1 lcmd -> label * 'a1 lcmd) -> 'a1
    instr list -> label -> 'a1 lcmd -> label * 'a1 lcmd **)

let rec linear_c asmop linear_i0 c lbl lc =
  match c with
  | [] -> (lbl, lc)
  | i :: c0 ->
    let (lbl0, lc0) = linear_c asmop linear_i0 c0 lbl lc in
    linear_i0 i lbl0 lc0

(** val add_align :
    'a1 asmOp -> instr_info -> align -> 'a1 lcmd -> 'a1 linstr list **)

let add_align _ ii a lc =
  match a with
  | Align -> { li_ii = ii; li_i = Lalign } :: lc
  | NoAlign -> lc

(** val align :
    'a1 asmOp -> instr_info -> align -> (label * 'a1 lcmd) -> label * 'a1 lcmd **)

let align asmop ii a p =
  ((fst p), (add_align asmop ii a (snd p)))

(** val ov_type_ptr : coq_PointerData -> Var.var option -> bool **)

let ov_type_ptr pd = function
| Some r ->
  eq_op stype_eqType (Obj.magic Var.vtype r)
    (Obj.magic (Coq_sword (coq_Uptr pd)))
| None -> true

(** val check_fd :
    coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
    funname -> 'a1 sfundef -> (pp_error_loc, unit) result **)

let check_fd pd asmop liparams p =
  let check_stack_ofs = fun e ofs ws ->
    (&&) (Z.leb e.sf_stk_sz ofs)
      ((&&)
        (Z.leb (Z.add ofs (wsize_size ws))
          (Z.add e.sf_stk_sz e.sf_stk_extra_sz))
        ((&&) (cmp_le wsize_cmp ws e.sf_align)
          (is_align (GRing.ComRing.eqType (word (coq_Uptr pd)))
            (coq_Pointer pd) (wrepr (coq_Uptr pd) ofs) ws)))
  in
  let check_stack_ofs_internal_call = fun e ofs ws ->
    (&&) (eq_op coq_Z_eqType ofs (Obj.magic Z0))
      ((&&)
        (eq_op coq_Z_eqType (Obj.magic wsize_size ws)
          (Obj.magic e.sf_stk_ioff)) (cmp_le wsize_cmp ws e.sf_align))
  in
  (fun fn fd ->
  let e = fd.f_extra in
  (match check_c asmop (check_i pd asmop p fn (Obj.magic e)) fd.f_body with
   | Ok _ ->
     (match check_to_save pd asmop liparams (Obj.magic e) with
      | Ok _ ->
        if (&&) (Z.leb Z0 (Obj.magic e).sf_stk_sz)
             ((&&) (Z.leb Z0 (Obj.magic e).sf_stk_extra_sz)
               ((&&)
                 (Z.ltb (stack_frame_allocation_size (Obj.magic e))
                   (wbase (coq_Uptr pd)))
                 (Z.leb (frame_size (Obj.magic e)) (Obj.magic e).sf_stk_max)))
        then if match (Obj.magic e).sf_return_address with
                | RAnone ->
                  negb
                    (in_mem
                      (Obj.magic { Var.vtype = (Coq_sword (coq_Uptr pd));
                        Var.vname = liparams.lip_tmp2 })
                      (mem (seq_predType Var.var_eqType)
                        (Obj.magic map (fun v -> v.v_var) fd.f_res)))
                | RAreg (ra, tmp) ->
                  (&&)
                    (eq_op stype_eqType (Obj.magic Var.vtype ra)
                      (Obj.magic (Coq_sword (coq_Uptr pd))))
                    (ov_type_ptr pd tmp)
                | RAstack (ora, ofs, tmp) ->
                  (&&) (ov_type_ptr pd tmp)
                    ((&&)
                      (match ora with
                       | Some ra ->
                         eq_op stype_eqType (Obj.magic Var.vtype ra)
                           (Obj.magic (Coq_sword (coq_Uptr pd)))
                       | None -> true)
                      (Obj.magic check_stack_ofs_internal_call e ofs
                        (coq_Uptr pd)))
             then let ok_save_stack =
                    match (Obj.magic e).sf_save_stack with
                    | SavedStackNone ->
                      (&&)
                        (eq_op
                          (seq_eqType
                            (prod_eqType Var.var_eqType coq_Z_eqType))
                          (Obj.magic (Obj.magic e).sf_to_save) (Obj.magic []))
                        ((&&)
                          (eq_op wsize_eqType
                            (Obj.magic (Obj.magic e).sf_align) (Obj.magic U8))
                          ((&&)
                            (eq_op coq_Z_eqType
                              (Obj.magic (Obj.magic e).sf_stk_sz)
                              (Obj.magic int_to_Z (Posz O)))
                            (eq_op coq_Z_eqType
                              (Obj.magic (Obj.magic e).sf_stk_extra_sz)
                              (Obj.magic int_to_Z (Posz O)))))
                    | SavedStackReg x ->
                      (&&)
                        (eq_op stype_eqType (Obj.magic Var.vtype x)
                          (Obj.magic (Coq_sword (coq_Uptr pd))))
                        ((&&)
                          (eq_op
                            (seq_eqType
                              (prod_eqType Var.var_eqType coq_Z_eqType))
                            (Obj.magic (Obj.magic e).sf_to_save)
                            (Obj.magic []))
                          (negb
                            (eq_op Ident.ident_eqType (Obj.magic Var.vname x)
                              (Obj.magic liparams.lip_tmp))))
                    | SavedStackStk ofs ->
                      (&&) (Obj.magic check_stack_ofs e ofs (coq_Uptr pd))
                        ((&&)
                          (negb
                            (SvExtra.Sv.mem
                              (Obj.magic { Var.vtype = (Coq_sword
                                (coq_Uptr pd)); Var.vname =
                                liparams.lip_tmp })
                              (SvExtra.sv_of_list (Obj.magic fst)
                                (Obj.magic e).sf_to_save)))
                          ((&&)
                            (negb
                              (SvExtra.Sv.mem
                                (Obj.magic { Var.vtype = (Coq_sword
                                  (coq_Uptr pd)); Var.vname =
                                  liparams.lip_tmp2 })
                                (SvExtra.sv_of_list (Obj.magic fst)
                                  (Obj.magic e).sf_to_save)))
                            (negb
                              (SvExtra.Sv.mem
                                (Obj.magic { Var.vtype = (Coq_sword
                                  (coq_Uptr pd)); Var.vname =
                                  (Obj.magic p).p_extra.sp_rsp })
                                (SvExtra.sv_of_list (Obj.magic fst)
                                  (Obj.magic e).sf_to_save)))))
                  in
                  if (||) (negb (is_RAnone (Obj.magic e).sf_return_address))
                       ok_save_stack
                  then Ok ()
                  else let s =
                         E.error
                           ('b'::('a'::('d'::(' '::('s'::('a'::('v'::('e'::('-'::('s'::('t'::('a'::('c'::('k'::[]))))))))))))))
                       in
                       Error s
             else let s =
                    E.error
                      ('b'::('a'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::('-'::('a'::('d'::('d'::('r'::('e'::('s'::('s'::[]))))))))))))))))))
                  in
                  Error s
        else let s =
               E.error
                 ('b'::('a'::('d'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('s'::('i'::('z'::('e'::[]))))))))))))))
             in
             Error s
      | Error s -> Error s)
   | Error s -> Error s))

(** val check_prog :
    coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
    (pp_error_loc, unit) result **)

let check_prog pd asmop liparams p =
  match map_cfprog_name_gen (fun x -> x.f_info)
          (check_fd pd asmop liparams p) p.p_funcs with
  | Ok _ -> Ok ()
  | Error s -> Error s

(** val allocate_stack_frame :
    coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
    bool -> instr_info -> coq_Z -> var_i option -> bool -> 'a1 lcmd **)

let allocate_stack_frame pd asmop liparams p free ii sz tmp rastack =
  let sz0 = if rastack then Z.sub sz (wsize_size (coq_Uptr pd)) else sz in
  if eq_op coq_Z_eqType (Obj.magic sz0) (Obj.magic Z0)
  then []
  else let args =
         if free
         then liparams.lip_free_stack_frame
                (mk_var_i { Var.vtype = (Coq_sword (coq_Uptr pd));
                  Var.vname = (Obj.magic p).p_extra.sp_rsp }) tmp sz0
         else liparams.lip_allocate_stack_frame
                (mk_var_i { Var.vtype = (Coq_sword (coq_Uptr pd));
                  Var.vname = (Obj.magic p).p_extra.sp_rsp }) tmp sz0
       in
       map (li_of_fopn_args asmop ii) args

(** val linear_i :
    coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
    funname -> 'a1 instr -> label -> 'a1 lcmd -> label * 'a1 lcmd **)

let linear_i pd asmop liparams p fn =
  let returnTarget = fun x -> Llabel (ExternalLabel, x) in
  let llabel = fun x -> Llabel (InternalLabel, x) in
  let rec linear_i0 i lbl lc =
    let MkI (ii, ir) = i in
    (match ir with
     | Copn (xs, _, o, es) ->
       (match omap lexpr_of_lval xs with
        | Some xs0 ->
          (match omap rexpr_of_pexpr es with
           | Some es0 ->
             (lbl, ({ li_ii = ii; li_i = (Lopn (xs0, o, es0)) } :: lc))
           | None -> (lbl, lc))
        | None -> (lbl, lc))
     | Csyscall (_, o, _) ->
       (lbl, ({ li_ii = ii; li_i = (Lsyscall o) } :: lc))
     | Cif (e, c1, c2) ->
       (match c1 with
        | [] ->
          let lbl0 = next_lbl lbl in
          let (lbl1, lc0) =
            linear_c asmop linear_i0 c2 lbl0 ({ li_ii = ii; li_i =
              (llabel lbl) } :: lc)
          in
          (lbl1, ({ li_ii = ii; li_i = (Lcond ((to_fexpr e), lbl)) } :: lc0))
        | _ :: _ ->
          (match c2 with
           | [] ->
             let lbl0 = next_lbl lbl in
             let (lbl1, lc0) =
               linear_c asmop linear_i0 c1 lbl0 ({ li_ii = ii; li_i =
                 (llabel lbl) } :: lc)
             in
             (lbl1, ({ li_ii = ii; li_i = (Lcond ((to_fexpr (snot e)),
             lbl)) } :: lc0))
           | _ :: _ ->
             let l2 = next_lbl lbl in
             let lbl0 = next_lbl l2 in
             let (lbl1, lc0) =
               let (lbl1, lc0) =
                 let (lbl1, lc0) =
                   linear_c asmop linear_i0 c1 lbl0 ({ li_ii = ii; li_i =
                     (llabel l2) } :: lc)
                 in
                 let lc1 = { li_ii = ii; li_i = (llabel lbl) } :: lc0 in
                 (lbl1, ({ li_ii = ii; li_i = (Lgoto (fn, l2)) } :: lc1))
               in
               linear_c asmop linear_i0 c2 lbl1 lc0
             in
             (lbl1, ({ li_ii = ii; li_i = (Lcond ((to_fexpr e),
             lbl)) } :: lc0))))
     | Cwhile (a, c, e, c') ->
       (match is_bool e with
        | Some b ->
          if b
          then let lbl0 = next_lbl lbl in
               align asmop ii a
                 (let (lbl1, lc0) =
                    let (lbl1, lc0) =
                      linear_c asmop linear_i0 c' lbl0 ({ li_ii = ii; li_i =
                        (Lgoto (fn, lbl)) } :: lc)
                    in
                    linear_c asmop linear_i0 c lbl1 lc0
                  in
                  (lbl1, ({ li_ii = ii; li_i = (llabel lbl) } :: lc0)))
          else linear_c asmop linear_i0 c lbl lc
        | None ->
          (match c' with
           | [] ->
             let lbl0 = next_lbl lbl in
             align asmop ii a
               (let (lbl1, lc0) =
                  linear_c asmop linear_i0 c lbl0 ({ li_ii = ii; li_i =
                    (Lcond ((to_fexpr e), lbl)) } :: lc)
                in
                (lbl1, ({ li_ii = ii; li_i = (llabel lbl) } :: lc0)))
           | _ :: _ ->
             let l2 = next_lbl lbl in
             let lbl0 = next_lbl l2 in
             let (lbl1, lc0) =
               align asmop ii a
                 (let (lbl1, lc0) =
                    let (lbl1, lc0) =
                      linear_c asmop linear_i0 c lbl0 ({ li_ii = ii; li_i =
                        (Lcond ((to_fexpr e), l2)) } :: lc)
                    in
                    let lc1 = { li_ii = ii; li_i = (llabel lbl) } :: lc0 in
                    linear_c asmop linear_i0 c' lbl1 lc1
                  in
                  (lbl1, ({ li_ii = ii; li_i = (llabel l2) } :: lc0)))
             in
             (lbl1, ({ li_ii = ii; li_i = (Lgoto (fn, lbl)) } :: lc0))))
     | Ccall (_, fn', _) ->
       (match get_fundef p.p_funcs fn' with
        | Some fd ->
          let e = fd.f_extra in
          let ra = (Obj.magic e).sf_return_address in
          if is_RAnone ra
          then (lbl, lc)
          else let sz = stack_frame_allocation_size (Obj.magic e) in
               let tmp = tmpi_of_ra ra in
               let before =
                 allocate_stack_frame pd asmop liparams p false ii sz tmp
                   (is_RAstack_None ra)
               in
               let after =
                 allocate_stack_frame pd asmop liparams p true ii sz tmp
                   (is_RAstack ra)
               in
               let lbl0 = next_lbl lbl in
               let lcall = (fn',
                 (if eq_op funname_eqType (Obj.magic fn') (Obj.magic fn)
                  then lbl
                  else Coq_xH))
               in
               (lbl0,
               (cat before ({ li_ii = ii; li_i = (Lcall ((ovari_of_ra ra),
                 lcall)) } :: ({ li_ii = ii; li_i =
                 (returnTarget lbl) } :: (cat after lc)))))
        | None -> (lbl, lc))
     | _ -> (lbl, lc))
  in linear_i0

(** val linear_body :
    coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
    funname -> stk_fun_extra -> 'a1 instr list -> label * 'a1 lcmd **)

let linear_body pd asmop liparams p fn =
  let llabel = fun x -> Llabel (InternalLabel, x) in
  (fun e body ->
  let (p0, lbl) =
    match e.sf_return_address with
    | RAnone ->
      let sf_sz = Z.add e.sf_stk_sz e.sf_stk_extra_sz in
      (match e.sf_save_stack with
       | SavedStackNone -> (([], []), Coq_xH)
       | SavedStackReg x ->
         let r = mk_var_i x in
         ((((lmove asmop liparams
              (mk_var_i { Var.vtype = (Coq_sword (coq_Uptr pd)); Var.vname =
                (Obj.magic p).p_extra.sp_rsp }) r) :: []),
         (set_up_sp_register asmop liparams
           (mk_var_i { Var.vtype = (Coq_sword (coq_Uptr pd)); Var.vname =
             (Obj.magic p).p_extra.sp_rsp }) sf_sz e.sf_align r
           (mk_var_i { Var.vtype = (Coq_sword (coq_Uptr pd)); Var.vname =
             liparams.lip_tmp }))), Coq_xH)
       | SavedStackStk ofs ->
         let r =
           mk_var_i { Var.vtype = (Coq_sword (coq_Uptr pd)); Var.vname =
             liparams.lip_tmp }
         in
         (((pop_to_save pd asmop liparams p e.sf_to_save ofs),
         (cat
           (set_up_sp_register asmop liparams
             (mk_var_i { Var.vtype = (Coq_sword (coq_Uptr pd)); Var.vname =
               (Obj.magic p).p_extra.sp_rsp }) sf_sz e.sf_align r
             (mk_var_i { Var.vtype = (Coq_sword (coq_Uptr pd)); Var.vname =
               liparams.lip_tmp2 }))
           (push_to_save pd asmop liparams p e.sf_to_save ({ Var.vtype =
             (Coq_sword (coq_Uptr pd)); Var.vname = liparams.lip_tmp }, ofs)))),
         Coq_xH))
    | RAreg (r, _) ->
      ((({ li_ii = dummy_instr_info; li_i = (Ligoto (Rexpr (Fvar
        (mk_var_i r)))) } :: []), ({ li_ii = dummy_instr_info; li_i =
        (llabel Coq_xH) } :: [])), (Coq_xO Coq_xH))
    | RAstack (ra, z, _) ->
      ((({ li_ii = dummy_instr_info; li_i = Lret } :: []), ({ li_ii =
        dummy_instr_info; li_i =
        (llabel Coq_xH) } :: (match ra with
                              | Some ra0 ->
                                (lstore asmop liparams
                                  (mk_var_i { Var.vtype = (Coq_sword
                                    (coq_Uptr pd)); Var.vname =
                                    (Obj.magic p).p_extra.sp_rsp }) z
                                  (mk_var_i ra0)) :: []
                              | None -> []))), (Coq_xO Coq_xH))
  in
  let (tail, head0) = p0 in
  let fd' = linear_c asmop (linear_i pd asmop liparams p fn) body lbl tail in
  ((fst fd'), (cat head0 (snd fd'))))

(** val linear_fd :
    coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
    funname -> 'a1 sfundef -> label * 'a1 lfundef **)

let linear_fd pd asmop liparams p fn fd =
  let e = fd.f_extra in
  let is_export = is_RAnone (Obj.magic e).sf_return_address in
  let res = if is_export then fd.f_res else [] in
  let body = linear_body pd asmop liparams p fn (Obj.magic e) fd.f_body in
  ((fst body), { lfd_info = fd.f_info; lfd_align = (Obj.magic e).sf_align;
  lfd_tyin = fd.f_tyin; lfd_arg = fd.f_params; lfd_body = (snd body);
  lfd_tyout = fd.f_tyout; lfd_res = res; lfd_export = is_export;
  lfd_callee_saved =
  (if is_export then map fst (Obj.magic e).sf_to_save else []); lfd_stk_max =
  (Obj.magic e).sf_stk_max; lfd_frame_size = (frame_size (Obj.magic e)) })

(** val linear_prog :
    coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
    'a1 lprog cexec **)

let linear_prog pd asmop liparams p =
  match check_prog pd asmop liparams p with
  | Ok _ ->
    if eq_op nat_eqType (Obj.magic size p.p_globs) (Obj.magic O)
    then let funcs =
           fmap (fun nb_lbl pat ->
             let (f, fd) = pat in
             let fd0 = linear_fd pd asmop liparams p f fd in
             ((Pos.add nb_lbl (fst fd0)), (f, (snd fd0)))) Coq_xH p.p_funcs
         in
         if Z.leb (Zpos (fst funcs)) (wbase (coq_Uptr pd))
         then Ok { lp_rip = (Obj.magic p).p_extra.sp_rip; lp_rsp =
                (Obj.magic p).p_extra.sp_rsp; lp_globs =
                (Obj.magic p).p_extra.sp_globs; lp_funcs = (snd funcs) }
         else let s =
                E.internal_error
                  ('t'::('o'::('o'::(' '::('m'::('a'::('n'::('y'::(' '::('l'::('a'::('b'::('e'::('l'::('s'::[])))))))))))))))
              in
              Error s
    else let s =
           E.internal_error
             ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('p'::('_'::('g'::('l'::('o'::('b'::('s'::[])))))))))))))))
         in
         Error s
  | Error s -> Error s
