open BinInt
open BinNums
open Arch_decl
open Arch_extra
open Compiler_util
open Expr
open Fexpr
open Label
open Linear
open Seq
open Sopn
open Stack_zero_strategy
open Type
open Utils0
open Var0
open Word0
open Wsize
open X86_decl
open X86_extra
open X86_instr_decl

(** val loop_small_cmd :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    Ident.Ident.ident -> label -> wsize -> wsize -> coq_Z -> (register,
    register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
    extended_op lcmd **)

let loop_small_cmd atoI =
  let vflags =
    map (fun f -> mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f f))
      (OF :: (CF :: (SF :: (PF :: (ZF :: [])))))
  in
  let flags_lexprs = map (fun x -> LLvar x) vflags in
  (fun rspn ->
  let rspi =
    mk_var_i { Var.vtype = (Coq_sword (coq_Uptr (arch_pd x86_decl)));
      Var.vname = rspn }
  in
  let vlocal = fun t0 x x0 x1 -> mk_lvar (mk_var_i (to_var t0 x x0 x1)) in
  let tmp = vlocal (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RSI
  in
  let off = vlocal (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RDI
  in
  let zf = vlocal Coq_sbool x86_decl.toS_f atoI.toI_f ZF in
  let tmpi = tmp.gv in
  let offi = off.gv in
  let zfi = zf.gv in
  (fun lbl ws_align ws stk_max ->
  let i0 = Lopn (((LLvar tmpi) :: []), (coq_Ox86 atoI (MOV U64)), ((Rexpr
    (Fvar rspi)) :: []))
  in
  let i1 = Lopn ((cat flags_lexprs ((LLvar rspi) :: [])),
    (coq_Ox86 atoI (AND U64)), ((Rexpr (Fvar rspi)) :: ((Rexpr
    (fconst U64 (Z.opp (wsize_size ws_align)))) :: [])))
  in
  let i2 = Lopn ((cat flags_lexprs ((LLvar rspi) :: [])),
    (coq_Ox86 atoI (SUB U64)), ((Rexpr (Fvar rspi)) :: ((Rexpr
    (fconst U64 stk_max)) :: [])))
  in
  let i3 = Lopn (((LLvar offi) :: []), (coq_Ox86 atoI (MOV U64)), ((Rexpr
    (fconst U64 stk_max)) :: []))
  in
  let i4 = Llabel (InternalLabel, lbl) in
  let i5 = Lopn ((cat flags_lexprs ((LLvar offi) :: [])),
    (coq_Ox86 atoI (SUB U64)), ((Rexpr (Fvar offi)) :: ((Rexpr
    (fconst U64 (wsize_size ws))) :: [])))
  in
  let i6 = Lopn (((Store (ws, rspi, (Fvar offi))) :: []),
    (coq_Ox86 atoI (MOV ws)), ((Rexpr (fconst ws Z0)) :: []))
  in
  let i7 = Lcond ((Fapp1 (Onot, (Fvar zfi))), lbl) in
  let i8 = Lopn (((LLvar rspi) :: []), (coq_Ox86 atoI (MOV U64)), ((Rexpr
    (Fvar tmpi)) :: []))
  in
  map (fun x -> { li_ii = dummy_instr_info; li_i = x })
    (i0 :: (i1 :: (i2 :: (i3 :: (i4 :: (i5 :: (i6 :: (i7 :: (i8 :: [])))))))))))

(** val loop_small_vars :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    SvExtra.Sv.t **)

let loop_small_vars atoI =
  let vflags =
    map (fun f -> mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f f))
      (OF :: (CF :: (SF :: (PF :: (ZF :: [])))))
  in
  let vlocal = fun t0 x x0 x1 -> mk_lvar (mk_var_i (to_var t0 x x0 x1)) in
  let tmp = vlocal (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RSI
  in
  let off = vlocal (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RDI
  in
  let tmpi = tmp.gv in
  let offi = off.gv in
  SvExtra.sv_of_list (Obj.magic (fun v -> v.v_var)) (tmpi :: (offi :: vflags))

(** val loop_large_cmd :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    Ident.Ident.ident -> label -> wsize -> wsize -> coq_Z -> (register,
    register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
    extended_op lcmd **)

let loop_large_cmd atoI =
  let vflags =
    map (fun f -> mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f f))
      (OF :: (CF :: (SF :: (PF :: (ZF :: [])))))
  in
  let flags_lexprs = map (fun x -> LLvar x) vflags in
  (fun rspn ->
  let rspi =
    mk_var_i { Var.vtype = (Coq_sword (coq_Uptr (arch_pd x86_decl)));
      Var.vname = rspn }
  in
  let vlocal = fun t0 x x0 x1 -> mk_lvar (mk_var_i (to_var t0 x x0 x1)) in
  let tmp = vlocal (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RSI
  in
  let off = vlocal (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RDI
  in
  let vlr =
    vlocal (Coq_sword x86_decl.xreg_size) x86_decl.toS_x atoI.toI_x XMM2
  in
  let zf = vlocal Coq_sbool x86_decl.toS_f atoI.toI_f ZF in
  let tmpi = tmp.gv in
  let offi = off.gv in
  let vlri = vlr.gv in
  let zfi = zf.gv in
  (fun lbl ws_align ws stk_max ->
  let i0 = Lopn (((LLvar tmpi) :: []), (coq_Ox86 atoI (MOV U64)), ((Rexpr
    (Fvar rspi)) :: []))
  in
  let i1 = Lopn (((LLvar vlri) :: []), (Oasm (ExtOp (Oset0 ws))), []) in
  let i2 = Lopn ((cat flags_lexprs ((LLvar rspi) :: [])),
    (coq_Ox86 atoI (AND U64)), ((Rexpr (Fvar rspi)) :: ((Rexpr
    (fconst U64 (Z.opp (wsize_size ws_align)))) :: [])))
  in
  let i3 = Lopn ((cat flags_lexprs ((LLvar rspi) :: [])),
    (coq_Ox86 atoI (SUB U64)), ((Rexpr (Fvar rspi)) :: ((Rexpr
    (fconst U64 stk_max)) :: [])))
  in
  let i4 = Lopn (((LLvar offi) :: []), (coq_Ox86 atoI (MOV U64)), ((Rexpr
    (fconst U64 stk_max)) :: []))
  in
  let i5 = Llabel (InternalLabel, lbl) in
  let i6 = Lopn ((cat flags_lexprs ((LLvar offi) :: [])),
    (coq_Ox86 atoI (SUB U64)), ((Rexpr (Fvar offi)) :: ((Rexpr
    (fconst U64 (wsize_size ws))) :: [])))
  in
  let i7 = Lopn (((Store (ws, rspi, (Fvar offi))) :: []),
    (coq_Ox86 atoI (VMOVDQU ws)), ((Rexpr (Fvar vlri)) :: []))
  in
  let i8 = Lcond ((Fapp1 (Onot, (Fvar zfi))), lbl) in
  let i9 = Lopn (((LLvar rspi) :: []), (coq_Ox86 atoI (MOV U64)), ((Rexpr
    (Fvar tmpi)) :: []))
  in
  map (fun x -> { li_ii = dummy_instr_info; li_i = x })
    (i0 :: (i1 :: (i2 :: (i3 :: (i4 :: (i5 :: (i6 :: (i7 :: (i8 :: (i9 :: []))))))))))))

(** val loop_large_vars :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    SvExtra.Sv.t **)

let loop_large_vars atoI =
  let vflags =
    map (fun f -> mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f f))
      (OF :: (CF :: (SF :: (PF :: (ZF :: [])))))
  in
  let vlocal = fun t0 x x0 x1 -> mk_lvar (mk_var_i (to_var t0 x x0 x1)) in
  let tmp = vlocal (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RSI
  in
  let off = vlocal (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RDI
  in
  let vlr =
    vlocal (Coq_sword x86_decl.xreg_size) x86_decl.toS_x atoI.toI_x XMM2
  in
  let tmpi = tmp.gv in
  let offi = off.gv in
  let vlri = vlr.gv in
  SvExtra.sv_of_list (Obj.magic (fun v -> v.v_var))
    (vlri :: (tmpi :: (offi :: vflags)))

(** val x86_stack_zero_loop :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    Ident.Ident.ident -> label -> wsize -> wsize -> coq_Z -> (register,
    register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
    extended_op lcmd * SvExtra.Sv.t **)

let x86_stack_zero_loop atoI rspn lbl ws_align ws stk_max =
  if cmp_le wsize_cmp ws U64
  then ((loop_small_cmd atoI rspn lbl ws_align ws stk_max),
         (loop_small_vars atoI))
  else ((loop_large_cmd atoI rspn lbl ws_align ws stk_max),
         (loop_large_vars atoI))

(** val x86_stack_zero_loopSCT :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    Ident.Ident.ident -> label -> wsize -> wsize -> coq_Z -> (register,
    register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
    extended_op linstr list * SvExtra.Sv.t **)

let x86_stack_zero_loopSCT atoI rspn lbl ws_align ws stk_max =
  let (cmd, vars) = x86_stack_zero_loop atoI rspn lbl ws_align ws stk_max in
  ((cat cmd ({ li_ii = dummy_instr_info; li_i = (Lopn ([],
     (coq_Ox86 atoI LFENCE), [])) } :: [])), vars)

(** val unrolled_small_cmd :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    Ident.Ident.ident -> wsize -> wsize -> coq_Z -> (register, register_ext,
    xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op lcmd **)

let unrolled_small_cmd atoI =
  let vflags =
    map (fun f -> mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f f))
      (OF :: (CF :: (SF :: (PF :: (ZF :: [])))))
  in
  let flags_lexprs = map (fun x -> LLvar x) vflags in
  (fun rspn ->
  let rspi =
    mk_var_i { Var.vtype = (Coq_sword (coq_Uptr (arch_pd x86_decl)));
      Var.vname = rspn }
  in
  let vlocal = fun t0 x x0 x1 -> mk_lvar (mk_var_i (to_var t0 x x0 x1)) in
  let tmp = vlocal (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RSI
  in
  let tmpi = tmp.gv in
  (fun ws_align ws stk_max ->
  let i0 = Lopn (((LLvar tmpi) :: []), (coq_Ox86 atoI (MOV U64)), ((Rexpr
    (Fvar rspi)) :: []))
  in
  let i1 = Lopn ((cat flags_lexprs ((LLvar rspi) :: [])),
    (coq_Ox86 atoI (AND U64)), ((Rexpr (Fvar rspi)) :: ((Rexpr
    (fconst U64 (Z.opp (wsize_size ws_align)))) :: [])))
  in
  let i2 = Lopn ((cat flags_lexprs ((LLvar rspi) :: [])),
    (coq_Ox86 atoI (SUB U64)), ((Rexpr (Fvar rspi)) :: ((Rexpr
    (fconst U64 stk_max)) :: [])))
  in
  let f = fun off -> Lopn (((Store (ws, rspi, (fconst U64 off))) :: []),
    (coq_Ox86 atoI (MOV ws)), ((Rexpr (fconst ws Z0)) :: []))
  in
  let offs =
    map (fun x -> Z.mul x (wsize_size ws))
      (rev (ziota Z0 (Z.div stk_max (wsize_size ws))))
  in
  let i3 = Lopn (((LLvar rspi) :: []), (coq_Ox86 atoI (MOV U64)), ((Rexpr
    (Fvar tmpi)) :: []))
  in
  map (fun x -> { li_ii = dummy_instr_info; li_i = x })
    (i0 :: (i1 :: (i2 :: (cat (map f offs) (i3 :: [])))))))

(** val unrolled_small_vars :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    SvExtra.Sv.t **)

let unrolled_small_vars atoI =
  let vflags =
    map (fun f -> mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f f))
      (OF :: (CF :: (SF :: (PF :: (ZF :: [])))))
  in
  let vlocal = fun t0 x x0 x1 -> mk_lvar (mk_var_i (to_var t0 x x0 x1)) in
  let tmp = vlocal (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RSI
  in
  let tmpi = tmp.gv in
  SvExtra.sv_of_list (Obj.magic (fun v -> v.v_var)) (tmpi :: vflags)

(** val unrolled_large_cmd :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    Ident.Ident.ident -> wsize -> wsize -> coq_Z -> (register, register_ext,
    xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op lcmd **)

let unrolled_large_cmd atoI =
  let vflags =
    map (fun f -> mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f f))
      (OF :: (CF :: (SF :: (PF :: (ZF :: [])))))
  in
  let flags_lexprs = map (fun x -> LLvar x) vflags in
  (fun rspn ->
  let rspi =
    mk_var_i { Var.vtype = (Coq_sword (coq_Uptr (arch_pd x86_decl)));
      Var.vname = rspn }
  in
  let vlocal = fun t0 x x0 x1 -> mk_lvar (mk_var_i (to_var t0 x x0 x1)) in
  let tmp = vlocal (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RSI
  in
  let vlr =
    vlocal (Coq_sword x86_decl.xreg_size) x86_decl.toS_x atoI.toI_x XMM2
  in
  let tmpi = tmp.gv in
  let vlri = vlr.gv in
  (fun ws_align ws stk_max ->
  let i0 = Lopn (((LLvar tmpi) :: []), (coq_Ox86 atoI (MOV U64)), ((Rexpr
    (Fvar rspi)) :: []))
  in
  let i1 = Lopn (((LLvar vlri) :: []), (Oasm (ExtOp (Oset0 ws))), []) in
  let i2 = Lopn ((cat flags_lexprs ((LLvar rspi) :: [])),
    (coq_Ox86 atoI (AND U64)), ((Rexpr (Fvar rspi)) :: ((Rexpr
    (fconst U64 (Z.opp (wsize_size ws_align)))) :: [])))
  in
  let i3 = Lopn ((cat flags_lexprs ((LLvar rspi) :: [])),
    (coq_Ox86 atoI (SUB U64)), ((Rexpr (Fvar rspi)) :: ((Rexpr
    (fconst U64 stk_max)) :: [])))
  in
  let f = fun off -> Lopn (((Store (ws, rspi, (fconst U64 off))) :: []),
    (coq_Ox86 atoI (VMOVDQU ws)), ((Rexpr (Fvar vlri)) :: []))
  in
  let offs =
    map (fun x -> Z.mul x (wsize_size ws))
      (rev (ziota Z0 (Z.div stk_max (wsize_size ws))))
  in
  let i4 = Lopn (((LLvar rspi) :: []), (coq_Ox86 atoI (MOV U64)), ((Rexpr
    (Fvar tmpi)) :: []))
  in
  map (fun x -> { li_ii = dummy_instr_info; li_i = x })
    (i0 :: (i1 :: (i2 :: (i3 :: (cat (map f offs) (i4 :: []))))))))

(** val unrolled_large_vars :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    SvExtra.Sv.t **)

let unrolled_large_vars atoI =
  let vflags =
    map (fun f -> mk_var_i (to_var Coq_sbool x86_decl.toS_f atoI.toI_f f))
      (OF :: (CF :: (SF :: (PF :: (ZF :: [])))))
  in
  let vlocal = fun t0 x x0 x1 -> mk_lvar (mk_var_i (to_var t0 x x0 x1)) in
  let tmp = vlocal (Coq_sword x86_decl.reg_size) x86_decl.toS_r atoI.toI_r RSI
  in
  let vlr =
    vlocal (Coq_sword x86_decl.xreg_size) x86_decl.toS_x atoI.toI_x XMM2
  in
  let tmpi = tmp.gv in
  let vlri = vlr.gv in
  SvExtra.sv_of_list (Obj.magic (fun v -> v.v_var)) (vlri :: (tmpi :: vflags))

(** val x86_stack_zero_unrolled :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    Ident.Ident.ident -> wsize -> wsize -> coq_Z -> (register, register_ext,
    xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op
    lcmd * SvExtra.Sv.t **)

let x86_stack_zero_unrolled atoI rspn ws_align ws stk_max =
  if cmp_le wsize_cmp ws U64
  then ((unrolled_small_cmd atoI rspn ws_align ws stk_max),
         (unrolled_small_vars atoI))
  else ((unrolled_large_cmd atoI rspn ws_align ws stk_max),
         (unrolled_large_vars atoI))

(** val x86_stack_zero_cmd :
    (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
    stack_zero_strategy -> Ident.Ident.ident -> label -> wsize -> wsize ->
    coq_Z -> ((register, register_ext, xmm_register, rflag, condt, x86_op,
    x86_extra_op) extended_op lcmd * SvExtra.Sv.t) cexec **)

let x86_stack_zero_cmd atoI szs rspn lbl ws_align ws stk_max =
  match szs with
  | SZSloop -> Ok (x86_stack_zero_loop atoI rspn lbl ws_align ws stk_max)
  | SZSloopSCT ->
    Ok (x86_stack_zero_loopSCT atoI rspn lbl ws_align ws stk_max)
  | SZSunrolled -> Ok (x86_stack_zero_unrolled atoI rspn ws_align ws stk_max)
