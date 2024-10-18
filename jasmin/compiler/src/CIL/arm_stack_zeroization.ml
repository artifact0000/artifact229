open BinInt
open BinNums
open Arch_decl
open Arch_extra
open Arm_decl
open Arm_extra
open Arm_instr_decl
open Arm_params_common
open Compiler_util
open Expr
open Fexpr
open Label
open Linear
open Seq
open Stack_zero_strategy
open Type
open Utils0
open Var0
open Word0
open Wsize

type __ = Obj.t

(** val sz_init :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> wsize -> coq_Z
    -> (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op
    lcmd **)

let sz_init atoI vrsp alignment stk_max =
  let vsaved_sp =
    mk_var_i
      (to_var (Coq_sword arm_decl.reg_size) arm_decl.toS_r atoI.toI_r R02)
  in
  let voff =
    mk_var_i
      (to_var (Coq_sword arm_decl.reg_size) arm_decl.toS_r atoI.toI_r R03)
  in
  let vzero =
    mk_var_i
      (to_var (Coq_sword arm_decl.reg_size) arm_decl.toS_r atoI.toI_r R12)
  in
  let args =
    (ARMFopn.mov atoI vsaved_sp vrsp) :: (cat (ARMFopn.li atoI voff stk_max)
                                           ((ARMFopn.align atoI vzero
                                              vsaved_sp alignment) :: (
                                           (ARMFopn.mov atoI vrsp vzero) :: (
                                           (ARMFopn.sub atoI vrsp vrsp voff) :: (
                                           (ARMFopn.movi atoI vzero Z0) :: [])))))
  in
  map (li_of_fopn_args (asm_opI (arm_extra atoI)) dummy_instr_info) args

(** val store_zero :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> wsize -> fexpr
    -> (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op
    linstr_r **)

let store_zero atoI vrsp ws =
  let vzero =
    mk_var_i
      (to_var (Coq_sword arm_decl.reg_size) arm_decl.toS_r atoI.toI_r R12)
  in
  (fun off ->
  match store_mn_of_wsize ws with
  | Some mn ->
    let current = Store (ws, vrsp, off) in
    let op = ARM_op (mn, default_opts) in
    Lopn ((current :: []), (coq_Oarm atoI op), ((Rexpr (Fvar vzero)) :: []))
  | None -> Lalign)

(** val sz_loop :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> label -> wsize
    -> (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op lcmd **)

let sz_loop atoI vrsp lbl ws =
  let voff =
    mk_var_i
      (to_var (Coq_sword arm_decl.reg_size) arm_decl.toS_r atoI.toI_r R03)
  in
  let vzf = mk_var_i (to_var Coq_sbool arm_decl.toS_f atoI.toI_f ZF) in
  let vflags =
    map (fun f -> mk_var_i (to_var Coq_sbool arm_decl.toS_f atoI.toI_f f))
      (Arch_decl.rflags arm_decl)
  in
  let leflags = map (fun f -> LLvar f) vflags in
  let dec_off =
    let opts = { set_flags = true; is_conditional = false; has_shift = None }
    in
    let op = ARM_op (SUB, opts) in
    let dec =
      let ws0 = U32 in let imm = wsize_size ws in Rexpr (fconst ws0 imm)
    in
    Lopn ((cat leflags ((LLvar voff) :: [])), (coq_Oarm atoI op), ((Rexpr
    (Fvar voff)) :: (dec :: [])))
  in
  let irs = (Llabel (InternalLabel,
    lbl)) :: (dec_off :: ((store_zero atoI vrsp ws (Fvar voff)) :: ((Lcond
    ((Fapp1 (Onot, (Fvar vzf))), lbl)) :: [])))
  in
  map (fun x -> { li_ii = dummy_instr_info; li_i = x }) irs

(** val restore_sp :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> arm_extended_op
    linstr list **)

let restore_sp atoI vrsp =
  let vsaved_sp =
    mk_var_i
      (to_var (Coq_sword arm_decl.reg_size) arm_decl.toS_r atoI.toI_r R02)
  in
  (li_of_fopn_args (asm_opI (arm_extra atoI)) dummy_instr_info
    (ARMFopn.mov atoI vrsp vsaved_sp)) :: []

(** val stack_zero_loop :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> label -> wsize
    -> wsize -> coq_Z -> (register, __, __, rflag, condt, arm_op,
    arm_extra_op) extended_op lcmd **)

let stack_zero_loop atoI vrsp lbl alignment ws stk_max =
  cat (sz_init atoI vrsp alignment stk_max)
    (cat (sz_loop atoI vrsp lbl ws) (restore_sp atoI vrsp))

(** val stack_zero_loop_vars :
    (register, __, __, rflag, condt) arch_toIdent -> SvExtra.Sv.t **)

let stack_zero_loop_vars atoI =
  let vsaved_sp =
    mk_var_i
      (to_var (Coq_sword arm_decl.reg_size) arm_decl.toS_r atoI.toI_r R02)
  in
  let voff =
    mk_var_i
      (to_var (Coq_sword arm_decl.reg_size) arm_decl.toS_r atoI.toI_r R03)
  in
  let vzero =
    mk_var_i
      (to_var (Coq_sword arm_decl.reg_size) arm_decl.toS_r atoI.toI_r R12)
  in
  let vflags =
    map (fun f -> mk_var_i (to_var Coq_sbool arm_decl.toS_f atoI.toI_f f))
      (Arch_decl.rflags arm_decl)
  in
  SvExtra.sv_of_list (Obj.magic (fun v -> v.v_var))
    (vsaved_sp :: (voff :: (vzero :: vflags)))

(** val sz_unrolled :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> wsize -> coq_Z
    -> (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op lcmd **)

let sz_unrolled atoI vrsp ws stk_max =
  let rn = rev (ziota Z0 (Z.div stk_max (wsize_size ws))) in
  map (fun off -> { li_ii = dummy_instr_info; li_i =
    (store_zero atoI vrsp ws
      (fconst arm_decl.reg_size (Z.mul off (wsize_size ws)))) }) rn

(** val stack_zero_unrolled :
    (register, __, __, rflag, condt) arch_toIdent -> var_i -> wsize -> wsize
    -> coq_Z -> (register, __, __, rflag, condt, arm_op, arm_extra_op)
    extended_op lcmd **)

let stack_zero_unrolled atoI vrsp alignment ws stk_max =
  cat (sz_init atoI vrsp alignment stk_max)
    (cat (sz_unrolled atoI vrsp ws stk_max) (restore_sp atoI vrsp))

(** val stack_zero_unrolled_vars :
    (register, __, __, rflag, condt) arch_toIdent -> SvExtra.Sv.t **)

let stack_zero_unrolled_vars atoI =
  let vsaved_sp =
    mk_var_i
      (to_var (Coq_sword arm_decl.reg_size) arm_decl.toS_r atoI.toI_r R02)
  in
  let voff =
    mk_var_i
      (to_var (Coq_sword arm_decl.reg_size) arm_decl.toS_r atoI.toI_r R03)
  in
  let vzero =
    mk_var_i
      (to_var (Coq_sword arm_decl.reg_size) arm_decl.toS_r atoI.toI_r R12)
  in
  let vflags =
    map (fun f -> mk_var_i (to_var Coq_sbool arm_decl.toS_f atoI.toI_f f))
      (Arch_decl.rflags arm_decl)
  in
  SvExtra.sv_of_list (Obj.magic (fun v -> v.v_var))
    (vsaved_sp :: (voff :: (vzero :: vflags)))

(** val stack_zeroization_cmd :
    (register, __, __, rflag, condt) arch_toIdent -> stack_zero_strategy ->
    Ident.Ident.ident -> label -> wsize -> wsize -> coq_Z -> ((register, __,
    __, rflag, condt, arm_op, arm_extra_op) extended_op lcmd * SvExtra.Sv.t)
    cexec **)

let stack_zeroization_cmd atoI szs rspn lbl ws_align ws stk_max =
  let err = fun msg -> { pel_msg = (PPEstring msg); pel_fn = None; pel_fi =
    None; pel_ii = None; pel_vi = None; pel_pass = (Some
    ('s'::('t'::('a'::('c'::('k'::(' '::('z'::('e'::('r'::('o'::('i'::('z'::('a'::('t'::('i'::('o'::('n'::[]))))))))))))))))));
    pel_internal = false }
  in
  let err_size =
    err
      ('S'::('t'::('a'::('c'::('k'::(' '::('z'::('e'::('r'::('o'::('i'::('z'::('a'::('t'::('i'::('o'::('n'::(' '::('s'::('i'::('z'::('e'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::(' '::('i'::('n'::(' '::('A'::('R'::('M'::('v'::('7'::[])))))))))))))))))))))))))))))))))))))))))))))
  in
  if cmp_le wsize_cmp ws U32
  then let rsp =
         mk_var_i { Var.vtype = (Coq_sword (coq_Uptr (arch_pd arm_decl)));
           Var.vname = rspn }
       in
       (match szs with
        | SZSloop ->
          Ok ((stack_zero_loop atoI rsp lbl ws_align ws stk_max),
            (stack_zero_loop_vars atoI))
        | SZSloopSCT ->
          let err_sct =
            err
              ('S'::('t'::('r'::('a'::('t'::('e'::('g'::('y'::(' '::('"'::('l'::('o'::('o'::('p'::(' '::('w'::('i'::('t'::('h'::(' '::('S'::('C'::('T'::('"'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::(' '::('i'::('n'::(' '::('A'::('R'::('M'::('v'::('7'::[]))))))))))))))))))))))))))))))))))))))))))))))))))
          in
          Error err_sct
        | SZSunrolled ->
          Ok ((stack_zero_unrolled atoI rsp ws_align ws stk_max),
            (stack_zero_unrolled_vars atoI)))
  else Error err_size
