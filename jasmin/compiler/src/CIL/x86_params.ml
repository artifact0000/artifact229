open BinInt
open BinNums
open Datatypes
open Arch_decl
open Arch_extra
open Arch_params
open Asm_gen
open Compiler_util
open Eqtype
open Expr
open Fexpr
open Linearization
open Protect_calls
open Seq
open Slh_lowering
open Slh_ops
open Sopn
open Ssrint
open Stack_alloc
open Stack_zeroization
open Type
open Utils0
open Var0
open Word0
open Word_ssrZ
open Wsize
open X86_decl
open X86_extra
open X86_instr_decl
open X86_lowering
open X86_stack_zeroization

(** val x86_op_align :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> wsize -> wsize -> (lexpr list * (register, register_ext,
    xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op
    sopn) * rexpr list **)

let x86_op_align atoI x ws al =
  let f_to_lvar = fun x0 -> LLvar
    (mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f x0))
  in
  let eflags = map f_to_lvar (OF :: (CF :: (SF :: (PF :: (ZF :: []))))) in
  let ex = Rexpr (Fvar x) in
  let emask = fconst ws (Z.opp (wsize_size al)) in
  (((cat eflags ((LLvar x) :: [])), (coq_Ox86 atoI (AND ws))), (ex :: ((Rexpr
  emask) :: [])))

(** val lea_ptr :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> lval
    -> pexpr -> assgn_tag -> coq_Z -> (register, register_ext, xmm_register,
    rflag, condt, x86_op, x86_extra_op) extended_op instr_r **)

let lea_ptr atoI x y tag ofs =
  Copn ((x :: []), tag, (coq_Ox86 atoI (LEA (coq_Uptr (arch_pd x86_decl)))),
    ((add (arch_pd x86_decl) y (cast_const (arch_pd x86_decl) ofs)) :: []))

(** val x86_mov_ofs :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> lval
    -> assgn_tag -> vptr_kind -> pexpr -> coq_Z -> (register, register_ext,
    xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op instr_r
    option **)

let x86_mov_ofs atoI x tag vpk y ofs =
  let addr =
    match mk_mov vpk with
    | MK_LEA -> lea_ptr atoI x y tag ofs
    | MK_MOV ->
      if eq_op coq_Z_eqType (Obj.magic ofs) (Obj.magic Z0)
      then mov_ws atoI (coq_Uptr (arch_pd x86_decl)) x y tag
      else lea_ptr atoI x y tag ofs
  in
  Some addr

(** val x86_immediate :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> coq_Z -> x86_extended_op instr_r **)

let x86_immediate atoI x z =
  mov_ws atoI (coq_Uptr (arch_pd x86_decl)) (Lvar x)
    (cast_const (arch_pd x86_decl) z) AT_none

(** val x86_swap :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    assgn_tag -> var_i -> var_i -> var_i -> var_i -> x86_extended_op instr_r **)

let x86_swap atoI t x y z w =
  Copn (((Lvar x) :: ((Lvar y) :: [])), t,
    (coq_Ox86 atoI (XCHG x86_decl.reg_size)),
    ((coq_Plvar z) :: ((coq_Plvar w) :: [])))

(** val x86_saparams :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op stack_alloc_params **)

let x86_saparams atoI =
  { sap_mov_ofs = (x86_mov_ofs atoI); sap_immediate = (x86_immediate atoI);
    sap_swap = (x86_swap atoI) }

(** val x86_allocate_stack_frame :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> var_i option -> coq_Z -> ((lexpr list * x86_extended_op
    sopn) * rexpr list) list **)

let x86_allocate_stack_frame atoI rspi _ sz =
  let p = Fapp2 ((Osub (Op_w (coq_Uptr (arch_pd x86_decl)))), (Fvar rspi),
    (fconst (coq_Uptr (arch_pd x86_decl)) sz))
  in
  ((((LLvar rspi) :: []),
  (coq_Ox86 atoI (LEA (coq_Uptr (arch_pd x86_decl))))), ((Rexpr
  p) :: [])) :: []

(** val x86_free_stack_frame :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> var_i option -> coq_Z -> ((lexpr list * x86_extended_op
    sopn) * rexpr list) list **)

let x86_free_stack_frame atoI rspi _ sz =
  let p = Fapp2 ((Oadd (Op_w (coq_Uptr (arch_pd x86_decl)))), (Fvar rspi),
    (fconst (coq_Uptr (arch_pd x86_decl)) sz))
  in
  ((((LLvar rspi) :: []),
  (coq_Ox86 atoI (LEA (coq_Uptr (arch_pd x86_decl))))), ((Rexpr
  p) :: [])) :: []

(** val x86_lassign :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    lexpr -> wsize -> rexpr -> (lexpr list * x86_extended_op sopn) * rexpr
    list **)

let x86_lassign atoI x ws e =
  let op = if cmp_le wsize_cmp ws U64 then MOV ws else VMOVDQU ws in
  (((x :: []), (coq_Ox86 atoI op)), (e :: []))

(** val x86_set_up_sp_register :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> coq_Z -> wsize -> var_i -> var_i -> ((lexpr list * (register,
    register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
    extended_op sopn) * rexpr list) list **)

let x86_set_up_sp_register atoI rspi sf_sz al r _ =
  let i0 =
    x86_lassign atoI (LLvar r) (coq_Uptr (arch_pd x86_decl)) (Rexpr (Fvar
      rspi))
  in
  let i2 = x86_op_align atoI rspi (coq_Uptr (arch_pd x86_decl)) al in
  i0 :: (rcons
          (if negb
                (eq_op coq_Z_eqType (Obj.magic sf_sz)
                  (Obj.magic int_to_Z (Posz O)))
           then x86_allocate_stack_frame atoI rspi None sf_sz
           else []) i2)

(** val x86_lmove :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> var_i -> (lexpr list * x86_extended_op sopn) * rexpr list **)

let x86_lmove atoI xd xs =
  x86_lassign atoI (LLvar xd) (wsize_of_stype (Var.vtype xd.v_var)) (Rexpr
    (Fvar xs))

(** val x86_check_ws : wsize -> bool **)

let x86_check_ws _ =
  true

(** val x86_lstore :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> coq_Z -> var_i -> (lexpr list * x86_extended_op sopn) * rexpr
    list **)

let x86_lstore atoI xd ofs xs =
  let ws = wsize_of_stype (Var.vtype xs.v_var) in
  x86_lassign atoI (Store (ws, xd,
    (fconst (coq_Uptr (arch_pd x86_decl)) ofs))) ws (Rexpr (Fvar xs))

(** val x86_lload :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> var_i -> coq_Z -> (lexpr list * x86_extended_op sopn) * rexpr
    list **)

let x86_lload atoI xd xs ofs =
  let ws = wsize_of_stype (Var.vtype xd.v_var) in
  x86_lassign atoI (LLvar xd) ws (Load (ws, xs,
    (fconst (coq_Uptr (arch_pd x86_decl)) ofs)))

(** val x86_liparams :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op linearization_params **)

let x86_liparams atoI =
  { lip_tmp =
    (Var.vname
      (mk_var_i
        (to_var (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RAX)).v_var);
    lip_tmp2 =
    (Var.vname
      (mk_var_i
        (to_var (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r R10)).v_var);
    lip_not_saved_stack = []; lip_allocate_stack_frame =
    (x86_allocate_stack_frame atoI); lip_free_stack_frame =
    (x86_free_stack_frame atoI); lip_set_up_sp_register =
    (x86_set_up_sp_register atoI); lip_lmove = (x86_lmove atoI);
    lip_check_ws = x86_check_ws; lip_lstore = (x86_lstore atoI);
    lip_lstores = (lstores_dfl (asm_opI (x86_extra atoI)) (x86_lstore atoI));
    lip_lloads = (lloads_dfl (asm_opI (x86_extra atoI)) (x86_lload atoI)) }

(** val x86_loparams :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    ((register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op, lowering_options) lowering_params **)

let x86_loparams atoI =
  { lop_lower_i = (lower_i atoI); lop_fvars_correct = (fvars_correct atoI) }

(** val lv_none_flags : lval list **)

let lv_none_flags =
  nseq (S (S (S (S (S O))))) (Lnone (dummy_var_info, Coq_sbool))

(** val x86_sh_lower :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> lval
    list -> slh_op -> pexpr list -> ((lval list * (register, register_ext,
    xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op
    sopn) * pexpr list) option **)

let x86_sh_lower _ lvs slho es =
  let o = fun x -> Oasm (ExtOp x) in
  (match slho with
   | SLHinit -> Some ((lvs, (o Ox86SLHinit)), es)
   | SLHupdate ->
     Some ((((Lnone (dummy_var_info, (Coq_sword
       (msf_size (arch_msfsz x86_decl))))) :: lvs), (o Ox86SLHupdate)), es)
   | SLHmove -> Some ((lvs, (o Ox86SLHmove)), es)
   | SLHprotect ws ->
     let extra =
       if cmp_le wsize_cmp ws U64
       then lv_none_flags
       else (Lnone (dummy_var_info, (Coq_sword ws))) :: []
     in
     Some (((cat extra lvs), (o (Ox86SLHprotect ws))), es)
   | _ -> None)

(** val x86_update_after_call :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> (lval list * (register, register_ext, xmm_register, rflag,
    condt, x86_op, x86_extra_op) extended_op sopn) * pexpr list **)

let x86_update_after_call _ msf =
  let lvs = (Lnone (dummy_var_info, (sreg x86_decl))) :: ((Lvar msf) :: []) in
  let es = (Pvar (mk_lvar msf)) :: [] in
  ((lvs, (Oasm (ExtOp Ox86SLHupdate_after_call))), es)

(** val x86_shparams :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op sh_params **)

let x86_shparams atoI =
  { shp_lower = (x86_sh_lower atoI); shp_update_after_call = (fun _ msf -> Ok
    (x86_update_after_call atoI msf)) }

(** val lexpr_flags :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    lexpr list **)

let lexpr_flags atoI =
  map (fun f -> LLvar
    (mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f f)))
    (OF :: (CF :: (SF :: (PF :: (ZF :: [])))))

(** val x86_fop_movi :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> coq_Z -> (lexpr list * (register, register_ext, xmm_register,
    rflag, condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list **)

let x86_fop_movi atoI x imm =
  ((((LLvar x) :: []), (coq_Ox86 atoI (MOV x86_decl.reg_size))),
    ((let ws = x86_decl.reg_size in Rexpr (fconst ws imm)) :: []))

(** val x86_fop_movx :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> var_i -> (lexpr list * (register, register_ext, xmm_register,
    rflag, condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list **)

let x86_fop_movx atoI x y =
  ((((LLvar x) :: []), (coq_Ox86 atoI (MOVX x86_decl.reg_size))), ((Rexpr
    (Fvar y)) :: []))

(** val x86_fop_cmpi :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> coq_Z -> (lexpr list * (register, register_ext, xmm_register,
    rflag, condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list **)

let x86_fop_cmpi atoI x imm =
  let res = (Rexpr (Fvar
    x)) :: ((let ws = x86_decl.reg_size in Rexpr (fconst ws imm)) :: [])
  in
  (((lexpr_flags atoI), (coq_Ox86 atoI (CMP x86_decl.reg_size))), res)

(** val x86_fop_protect_64 :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> var_i -> (lexpr list * (register, register_ext, xmm_register,
    rflag, condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list **)

let x86_fop_protect_64 atoI x msf =
  let les = cat (lexpr_flags atoI) ((LLvar x) :: []) in
  ((les, (Oasm (ExtOp (Ox86SLHprotect U64)))), ((Rexpr (Fvar x)) :: ((Rexpr
  (Fvar msf)) :: [])))

(** val x86_lcmd_pop :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> var_i -> ((lexpr list * (register, register_ext, xmm_register,
    rflag, condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list) list **)

let x86_lcmd_pop atoI rsp x =
  let addr = Load (x86_decl.reg_size, rsp, (fconst x86_decl.reg_size Z0)) in
  let rsp' = Rexpr (Fapp2 ((Oadd (Op_w x86_decl.reg_size)), (Fvar
    (mk_var_i rsp.v_var)),
    (fconst x86_decl.reg_size (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))
  in
  ((((LLvar x) :: []), (coq_Ox86 atoI (MOV x86_decl.reg_size))),
  (addr :: [])) :: (((((LLvar rsp) :: []),
  (coq_Ox86 atoI (LEA x86_decl.reg_size))), (rsp' :: [])) :: [])

(** val x86_lcmd_pushi :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    var_i -> coq_Z -> ((lexpr list * (register, register_ext, xmm_register,
    rflag, condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list) list **)

let x86_lcmd_pushi atoI rsp z =
  let addr = Store (x86_decl.reg_size, rsp, (fconst x86_decl.reg_size Z0)) in
  let rsp' = Rexpr (Fapp2 ((Osub (Op_w x86_decl.reg_size)), (Fvar
    (mk_var_i rsp.v_var)),
    (fconst x86_decl.reg_size (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))
  in
  ((((LLvar rsp) :: []), (coq_Ox86 atoI (LEA x86_decl.reg_size))),
  (rsp' :: [])) :: ((((addr :: []), (coq_Ox86 atoI (MOV x86_decl.reg_size))),
  ((let ws = x86_decl.reg_size in Rexpr (fconst ws z)) :: [])) :: [])

(** val r_uncons : 'a2 -> 'a1 list -> ('a2, 'a1 * 'a1 list) result **)

let r_uncons err = function
| [] -> Error err
| a :: s' -> Ok (a, s')

(** val fcond_eq :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> fexpr **)

let fcond_eq atoI =
  Fvar (mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f ZF))

(** val fcond_ne :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> fexpr **)

let fcond_ne atoI =
  Fapp1 (Onot, (Fvar
    (mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f ZF))))

(** val fcond_lt :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> fexpr **)

let fcond_lt atoI =
  Fvar (mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f CF))

(** val fcond_gt :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> fexpr **)

let fcond_gt atoI =
  Fapp2 (Oand, (Fapp1 (Onot, (Fvar
    (mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f CF))))), (Fapp1
    (Onot, (Fvar
    (mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f ZF))))))

(** val x86_is_update_after_call :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op sopn -> bool **)

let x86_is_update_after_call _ = function
| Oasm a ->
  (match a with
   | BaseOp _ -> false
   | ExtOp e -> (match e with
                 | Ox86SLHupdate_after_call -> true
                 | _ -> false))
| _ -> false

type btree_position =
| BTPleft
| BTPright
| BTPmiddle

(** val go_left : btree_position -> btree_position **)

let go_left = function
| BTPleft -> BTPleft
| _ -> BTPmiddle

(** val go_right : btree_position -> btree_position **)

let go_right = function
| BTPleft -> BTPmiddle
| x -> x

(** val update_after_call_cond :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    (char list option -> pp_error_loc) -> coq_Z -> var_i -> btree_position ->
    cs_info bintree -> (((lexpr list * (register, register_ext, xmm_register,
    rflag, condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list)
    list * fexpr) cexec **)

let update_after_call_cond atoI err =
  let err_invalid_return_tree =
    err (Some
      ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('t'::('r'::('e'::('e'::[]))))))))))))))))))))
  in
  (fun tag ra ->
  let rec update_after_call_cond0 pos = function
  | BTleaf -> Error err_invalid_return_tree
  | BTnode (c, t0, t1) ->
    let (_, tag') = c in
    (match t0 with
     | BTleaf ->
       (match t1 with
        | BTleaf ->
          if eq_op coq_Z_eqType (Obj.magic tag) (Obj.magic tag')
          then (match pos with
                | BTPleft -> Ok ([], (fcond_lt atoI))
                | BTPright -> Ok ([], (fcond_gt atoI))
                | BTPmiddle ->
                  Ok (((x86_fop_cmpi atoI ra tag) :: []), (fcond_eq atoI)))
          else Error err_invalid_return_tree
        | BTnode (_, _, _) ->
          (match Z.compare tag tag' with
           | Eq -> Ok ([], (fcond_eq atoI))
           | Lt -> update_after_call_cond0 (go_left pos) t0
           | Gt -> update_after_call_cond0 (go_right pos) t1))
     | BTnode (_, _, _) ->
       (match Z.compare tag tag' with
        | Eq -> Ok ([], (fcond_eq atoI))
        | Lt -> update_after_call_cond0 (go_left pos) t0
        | Gt -> update_after_call_cond0 (go_right pos) t1))
  in update_after_call_cond0)

(** val lower_update_after_call :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    (char list option -> pp_error_loc) -> coq_Z -> var_i -> cs_info bintree
    -> lexpr list -> rexpr list -> ((lexpr list * (register, register_ext,
    xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op
    sopn) * rexpr list) list cexec **)

let lower_update_after_call atoI err =
  let err_empty_return_tree =
    err (Some
      ('e'::('m'::('p'::('t'::('y'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('t'::('r'::('e'::('e'::[]))))))))))))))))))
  in
  (fun tag ra t les res ->
  match t with
  | BTleaf -> Error err_empty_return_tree
  | BTnode (_, b, b0) ->
    (match b with
     | BTleaf ->
       (match b0 with
        | BTleaf -> Ok []
        | BTnode (_, _, _) ->
          (match update_after_call_cond atoI err tag ra BTPleft t with
           | Ok x ->
             let (pre, cond) = x in
             let update = ((les, (Oasm (ExtOp Ox86SLHupdate))), ((Rexpr
               cond) :: res))
             in
             Ok (rcons pre update)
           | Error s -> Error s))
     | BTnode (_, _, _) ->
       (match update_after_call_cond atoI err tag ra BTPleft t with
        | Ok x ->
          let (pre, cond) = x in
          let update = ((les, (Oasm (ExtOp Ox86SLHupdate))), ((Rexpr
            cond) :: res))
          in
          Ok (rcons pre update)
        | Error s -> Error s)))

(** val load_tag :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    load_tag_args -> var_i * ((lexpr list * (register, register_ext,
    xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op
    sopn) * rexpr list) list **)

let load_tag atoI = function
| LTAstack (rsp, r, msf) ->
  let args =
    cat (x86_lcmd_pop atoI rsp r) ((x86_fop_protect_64 atoI r msf) :: [])
  in
  (r, args)
| LTAregister ra -> let args = [] in (ra, args)
| LTAextra_register (rx, r) ->
  let args = (x86_fop_movx atoI r rx) :: [] in (r, args)

(** val save_ra :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    (char list option -> pp_error_loc) -> save_tag_args -> coq_Z -> ((lexpr
    list * (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op sopn) * rexpr list) list cexec **)

let save_ra atoI _ sral tag =
  let c =
    match sral with
    | STAstack rspi -> x86_lcmd_pushi atoI rspi tag
    | STAregister r -> (x86_fop_movi atoI r tag) :: []
    | STAextra_register (rx, r) ->
      (x86_fop_movi atoI r tag) :: ((x86_fop_movx atoI rx r) :: [])
  in
  Ok c

(** val x86_pcparams :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op protect_calls_params **)

let x86_pcparams atoI =
  { pcp_is_update_after_call = (x86_is_update_after_call atoI);
    pcp_lower_update_after_call = (lower_update_after_call atoI);
    pcp_load_tag = (fun _ lta -> Ok (load_tag atoI lta)); pcp_cmpi =
    (fun _ r tag -> Ok (x86_fop_cmpi atoI r tag)); pcp_cond_ne =
    (fcond_ne atoI); pcp_cond_gt = (fcond_gt atoI); pcp_save_ra =
    (save_ra atoI) }

(** val not_condt : condt -> condt **)

let not_condt = function
| O_ct -> NO_ct
| NO_ct -> O_ct
| B_ct -> NB_ct
| NB_ct -> B_ct
| E_ct -> NE_ct
| NE_ct -> E_ct
| BE_ct -> NBE_ct
| NBE_ct -> BE_ct
| S_ct -> NS_ct
| NS_ct -> S_ct
| P_ct -> NP_ct
| NP_ct -> P_ct
| L_ct -> NL_ct
| NL_ct -> L_ct
| LE_ct -> NLE_ct
| NLE_ct -> LE_ct

(** val or_condt : instr_info -> fexpr -> condt -> condt -> condt cexec **)

let or_condt ii e c1 c2 =
  match c1 with
  | B_ct ->
    (match c2 with
     | E_ct -> Ok BE_ct
     | _ ->
       Error
         (Asm_gen.E.berror ii e
           ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('('::('O'::('R'::(')'::[]))))))))))))))))))))))))
  | E_ct ->
    (match c2 with
     | B_ct -> Ok BE_ct
     | L_ct -> Ok LE_ct
     | _ ->
       Error
         (Asm_gen.E.berror ii e
           ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('('::('O'::('R'::(')'::[]))))))))))))))))))))))))
  | L_ct ->
    (match c2 with
     | E_ct -> Ok LE_ct
     | _ ->
       Error
         (Asm_gen.E.berror ii e
           ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('('::('O'::('R'::(')'::[]))))))))))))))))))))))))
  | _ ->
    Error
      (Asm_gen.E.berror ii e
        ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('('::('O'::('R'::(')'::[])))))))))))))))))))))))

(** val and_condt :
    instr_info -> fexpr -> condt -> condt -> (pp_error_loc, condt) result **)

let and_condt ii e c1 c2 =
  match c1 with
  | NB_ct ->
    (match c2 with
     | NE_ct -> Ok NBE_ct
     | _ ->
       Error
         (Asm_gen.E.berror ii e
           ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('('::('A'::('N'::('D'::(')'::[])))))))))))))))))))))))))
  | NE_ct ->
    (match c2 with
     | NB_ct -> Ok NBE_ct
     | NL_ct -> Ok NLE_ct
     | _ ->
       Error
         (Asm_gen.E.berror ii e
           ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('('::('A'::('N'::('D'::(')'::[])))))))))))))))))))))))))
  | NL_ct ->
    (match c2 with
     | NE_ct -> Ok NLE_ct
     | _ ->
       Error
         (Asm_gen.E.berror ii e
           ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('('::('A'::('N'::('D'::(')'::[])))))))))))))))))))))))))
  | _ ->
    Error
      (Asm_gen.E.berror ii e
        ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('('::('A'::('N'::('D'::(')'::[]))))))))))))))))))))))))

(** val of_var_e_bool :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    instr_info -> var_i -> rflag cexec **)

let of_var_e_bool atoI ii v =
  match of_var Coq_sbool x86_decl.toS_f atoI.toI_f v.v_var with
  | Some r -> Ok r
  | None -> Error (Asm_gen.E.invalid_flag ii v)

(** val assemble_cond_r :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    instr_info -> fexpr -> condt cexec **)

let rec assemble_cond_r atoI ii e = match e with
| Fvar v ->
  (match of_var_e_bool atoI ii v with
   | Ok x ->
     (match x with
      | CF -> Ok B_ct
      | PF -> Ok P_ct
      | ZF -> Ok E_ct
      | SF -> Ok S_ct
      | OF -> Ok O_ct)
   | Error s -> Error s)
| Fapp1 (s, e0) ->
  (match s with
   | Onot ->
     (match assemble_cond_r atoI ii e0 with
      | Ok x -> Ok (not_condt x)
      | Error s0 -> Error s0)
   | _ ->
     Error
       (Asm_gen.E.berror ii e
         ('d'::('o'::('n'::('\''::('t'::(' '::('k'::('n'::('o'::('w'::('n'::(' '::('h'::('o'::('w'::(' '::('t'::('o'::(' '::('c'::('o'::('m'::('p'::('i'::('l'::('e'::(' '::('t'::('h'::('e'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))))))))))))))))
| Fapp2 (s, e1, e2) ->
  (match s with
   | Obeq ->
     (match e1 with
      | Fvar x1 ->
        (match e2 with
         | Fvar x2 ->
           (match of_var_e_bool atoI ii x1 with
            | Ok x ->
              (match of_var_e_bool atoI ii x2 with
               | Ok x0 ->
                 if (||)
                      ((&&) (eq_op rflag_eqType (Obj.magic x) (Obj.magic SF))
                        (eq_op rflag_eqType (Obj.magic x0) (Obj.magic OF)))
                      ((&&) (eq_op rflag_eqType (Obj.magic x) (Obj.magic OF))
                        (eq_op rflag_eqType (Obj.magic x0) (Obj.magic SF)))
                 then Ok NL_ct
                 else Error
                        (Asm_gen.E.berror ii e
                          ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::(' '::('('::('N'::('L'::(')'::[])))))))))))))))))))))))
               | Error s0 -> Error s0)
            | Error s0 -> Error s0)
         | _ ->
           Error
             (Asm_gen.E.berror ii e
               ('d'::('o'::('n'::('\''::('t'::(' '::('k'::('n'::('o'::('w'::('n'::(' '::('h'::('o'::('w'::(' '::('t'::('o'::(' '::('c'::('o'::('m'::('p'::('i'::('l'::('e'::(' '::('t'::('h'::('e'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))))))))))))))))
      | _ ->
        Error
          (Asm_gen.E.berror ii e
            ('d'::('o'::('n'::('\''::('t'::(' '::('k'::('n'::('o'::('w'::('n'::(' '::('h'::('o'::('w'::(' '::('t'::('o'::(' '::('c'::('o'::('m'::('p'::('i'::('l'::('e'::(' '::('t'::('h'::('e'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))))))))))))))))
   | Oand ->
     (match assemble_cond_r atoI ii e1 with
      | Ok x ->
        (match assemble_cond_r atoI ii e2 with
         | Ok x0 -> and_condt ii e x x0
         | Error s0 -> Error s0)
      | Error s0 -> Error s0)
   | Oor ->
     (match assemble_cond_r atoI ii e1 with
      | Ok x ->
        (match assemble_cond_r atoI ii e2 with
         | Ok x0 -> or_condt ii e x x0
         | Error s0 -> Error s0)
      | Error s0 -> Error s0)
   | _ ->
     Error
       (Asm_gen.E.berror ii e
         ('d'::('o'::('n'::('\''::('t'::(' '::('k'::('n'::('o'::('w'::('n'::(' '::('h'::('o'::('w'::(' '::('t'::('o'::(' '::('c'::('o'::('m'::('p'::('i'::('l'::('e'::(' '::('t'::('h'::('e'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))))))))))))))))
| _ ->
  Error
    (Asm_gen.E.berror ii e
      ('d'::('o'::('n'::('\''::('t'::(' '::('k'::('n'::('o'::('w'::('n'::(' '::('h'::('o'::('w'::(' '::('t'::('o'::(' '::('c'::('o'::('m'::('p'::('i'::('l'::('e'::(' '::('t'::('h'::('e'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))))))))))))))))

(** val assemble_cond :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    instr_info -> fexpr -> condt cexec **)

let assemble_cond =
  assemble_cond_r

(** val x86_agparams :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) asm_gen_params **)

let x86_agparams =
  assemble_cond

(** val x86_szparams :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op stack_zeroization_params **)

let x86_szparams =
  x86_stack_zero_cmd

(** val x86_is_move_op :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op asm_op_t -> bool **)

let x86_is_move_op _ = function
| BaseOp a ->
  let (o0, x) = a in
  (match o0 with
   | Some _ -> false
   | None ->
     (match x with
      | MOV _ -> true
      | VMOVDQA _ -> true
      | VMOVDQU _ -> true
      | _ -> false))
| ExtOp e -> (match e with
              | Ox86SLHmove -> true
              | _ -> false)

(** val x86_params :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    (register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op, lowering_options) architecture_params **)

let x86_params atoI =
  { ap_sap = (x86_saparams atoI); ap_lip = (x86_liparams atoI); ap_lop =
    (x86_loparams atoI); ap_shp = (x86_shparams atoI); ap_pcp =
    (x86_pcparams atoI); ap_agp = (x86_agparams atoI); ap_szp =
    (x86_szparams atoI); ap_is_move_op = (x86_is_move_op atoI) }
