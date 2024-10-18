open BinNums
open Datatypes
open Allocation
open Arch_decl
open Arch_extra
open Arch_params
open Array_copy
open Array_expansion
open Array_init
open Asm_gen
open Compiler_util
open Constant_prop
open Dead_calls
open Dead_code
open Eqtype
open Expr
open Flag_combination
open Global
open Inline
open Linear
open Linearization
open Lower_spill
open Lowering
open MakeReferenceArguments
open Merge_varmaps
open Propagate_inline
open Protect_calls
open Remove_globals
open Sem_type
open Seq
open Slh_lowering
open Sopn
open Ssralg
open Stack_alloc
open Stack_zero_strategy
open Stack_zeroization
open Tunneling
open Type
open Unrolling
open Utils0
open Var0
open Wsize

(** val pp_s : char list -> pp_error **)

let pp_s x =
  PPEstring x

(** val unroll :
    coq_MSFsize -> 'a1 asmOp -> coq_FlagCombinationParams -> ('a1 asm_op_t ->
    bool) -> nat -> 'a1 uprog -> 'a1 uprog cexec **)

let unroll msfsz asmop fcp is_move_op =
  let postprocess = fun p ->
    let p0 = const_prop_prog fcp msfsz asmop progUnit p in
    dead_code_prog asmop is_move_op progUnit p0 false
  in
  let rec unroll0 n p =
    match n with
    | O ->
      Error
        (loop_iterator
          ('u'::('n'::('r'::('o'::('l'::('l'::('i'::('n'::('g'::[]))))))))))
    | S n' ->
      let (p', repeat) = unroll_prog asmop progUnit p in
      if repeat
      then (match postprocess p' with
            | Ok x -> unroll0 n' x
            | Error s -> Error s)
      else Ok p
  in unroll0

(** val unroll_loop :
    coq_MSFsize -> 'a1 asmOp -> coq_FlagCombinationParams -> ('a1 asm_op_t ->
    bool) -> 'a1 uprog -> (pp_error_loc, 'a1 uprog) result **)

let unroll_loop msfsz asmop fcp is_move_op =
  let postprocess = fun p ->
    let p0 = const_prop_prog fcp msfsz asmop progUnit p in
    dead_code_prog asmop is_move_op progUnit p0 false
  in
  (fun p ->
  match postprocess p with
  | Ok x -> unroll msfsz asmop fcp is_move_op Loop.nb x
  | Error s -> Error s)

type compiler_step =
| Typing
| ParamsExpansion
| ArrayCopy
| AddArrInit
| LowerSpill
| Inlining
| RemoveUnusedFunction
| Unrolling
| Splitting
| Renaming
| RemovePhiNodes
| DeadCode_Renaming
| RemoveArrInit
| MakeRefArguments
| RegArrayExpansion
| RemoveGlobal
| LowerInstruction
| SLHLowering
| PropagateInline
| StackAllocation
| RemoveReturn
| RegAllocation
| DeadCode_RegAllocation
| Linearization
| ProtectCalls
| StackZeroization
| Tunneling
| Assembly

(** val compiler_step_list : compiler_step list **)

let compiler_step_list =
  Typing :: (ParamsExpansion :: (ArrayCopy :: (AddArrInit :: (LowerSpill :: (Inlining :: (RemoveUnusedFunction :: (Unrolling :: (Splitting :: (Renaming :: (RemovePhiNodes :: (DeadCode_Renaming :: (RemoveArrInit :: (MakeRefArguments :: (RegArrayExpansion :: (RemoveGlobal :: (LowerInstruction :: (SLHLowering :: (PropagateInline :: (StackAllocation :: (RemoveReturn :: (RegAllocation :: (DeadCode_RegAllocation :: (Linearization :: (ProtectCalls :: (StackZeroization :: (Tunneling :: (Assembly :: [])))))))))))))))))))))))))))

(** val compiler_step_beq : compiler_step -> compiler_step -> bool **)

let compiler_step_beq x y =
  match x with
  | Typing -> (match y with
               | Typing -> true
               | _ -> false)
  | ParamsExpansion -> (match y with
                        | ParamsExpansion -> true
                        | _ -> false)
  | ArrayCopy -> (match y with
                  | ArrayCopy -> true
                  | _ -> false)
  | AddArrInit -> (match y with
                   | AddArrInit -> true
                   | _ -> false)
  | LowerSpill -> (match y with
                   | LowerSpill -> true
                   | _ -> false)
  | Inlining -> (match y with
                 | Inlining -> true
                 | _ -> false)
  | RemoveUnusedFunction ->
    (match y with
     | RemoveUnusedFunction -> true
     | _ -> false)
  | Unrolling -> (match y with
                  | Unrolling -> true
                  | _ -> false)
  | Splitting -> (match y with
                  | Splitting -> true
                  | _ -> false)
  | Renaming -> (match y with
                 | Renaming -> true
                 | _ -> false)
  | RemovePhiNodes -> (match y with
                       | RemovePhiNodes -> true
                       | _ -> false)
  | DeadCode_Renaming -> (match y with
                          | DeadCode_Renaming -> true
                          | _ -> false)
  | RemoveArrInit -> (match y with
                      | RemoveArrInit -> true
                      | _ -> false)
  | MakeRefArguments -> (match y with
                         | MakeRefArguments -> true
                         | _ -> false)
  | RegArrayExpansion -> (match y with
                          | RegArrayExpansion -> true
                          | _ -> false)
  | RemoveGlobal -> (match y with
                     | RemoveGlobal -> true
                     | _ -> false)
  | LowerInstruction -> (match y with
                         | LowerInstruction -> true
                         | _ -> false)
  | SLHLowering -> (match y with
                    | SLHLowering -> true
                    | _ -> false)
  | PropagateInline -> (match y with
                        | PropagateInline -> true
                        | _ -> false)
  | StackAllocation -> (match y with
                        | StackAllocation -> true
                        | _ -> false)
  | RemoveReturn -> (match y with
                     | RemoveReturn -> true
                     | _ -> false)
  | RegAllocation -> (match y with
                      | RegAllocation -> true
                      | _ -> false)
  | DeadCode_RegAllocation ->
    (match y with
     | DeadCode_RegAllocation -> true
     | _ -> false)
  | Linearization -> (match y with
                      | Linearization -> true
                      | _ -> false)
  | ProtectCalls -> (match y with
                     | ProtectCalls -> true
                     | _ -> false)
  | StackZeroization -> (match y with
                         | StackZeroization -> true
                         | _ -> false)
  | Tunneling -> (match y with
                  | Tunneling -> true
                  | _ -> false)
  | Assembly -> (match y with
                 | Assembly -> true
                 | _ -> false)

(** val compiler_step_eq_dec : compiler_step -> compiler_step -> bool **)

let compiler_step_eq_dec x y =
  let b = compiler_step_beq x y in if b then true else false

(** val compiler_step_eq_axiom : compiler_step Equality.axiom **)

let compiler_step_eq_axiom =
  eq_axiom_of_scheme compiler_step_beq

(** val compiler_step_eqMixin : compiler_step Equality.mixin_of **)

let compiler_step_eqMixin =
  { Equality.op = compiler_step_beq; Equality.mixin_of__1 =
    compiler_step_eq_axiom }

(** val compiler_step_eqType : Equality.coq_type **)

let compiler_step_eqType =
  Obj.magic compiler_step_eqMixin

type stack_alloc_oracles = { ao_globals : GRing.ComRing.sort list;
                             ao_global_alloc : ((Var.var * wsize) * coq_Z)
                                               list;
                             ao_stack_alloc : (funname -> stk_alloc_oracle_t) }

(** val ao_globals : stack_alloc_oracles -> GRing.ComRing.sort list **)

let ao_globals s =
  s.ao_globals

(** val ao_global_alloc :
    stack_alloc_oracles -> ((Var.var * wsize) * coq_Z) list **)

let ao_global_alloc s =
  s.ao_global_alloc

(** val ao_stack_alloc :
    stack_alloc_oracles -> funname -> stk_alloc_oracle_t **)

let ao_stack_alloc s =
  s.ao_stack_alloc

type ('asm_op, 'lowering_options) compiler_params = { rename_fd : (instr_info
                                                                  -> funname
                                                                  -> 'asm_op
                                                                  _ufundef ->
                                                                  'asm_op
                                                                  _ufundef);
                                                      expand_fd : (funname ->
                                                                  'asm_op
                                                                  _ufundef ->
                                                                  expand_info);
                                                      split_live_ranges_fd : 
                                                      (funname -> 'asm_op
                                                      _ufundef -> 'asm_op
                                                      _ufundef);
                                                      renaming_fd : (funname
                                                                    ->
                                                                    'asm_op
                                                                    _ufundef
                                                                    ->
                                                                    'asm_op
                                                                    _ufundef);
                                                      remove_phi_nodes_fd : 
                                                      (funname -> 'asm_op
                                                      _ufundef -> 'asm_op
                                                      _ufundef);
                                                      stack_register_symbol : 
                                                      Ident.Ident.ident;
                                                      global_static_data_symbol : 
                                                      Ident.Ident.ident;
                                                      stackalloc : ('asm_op
                                                                   _uprog ->
                                                                   stack_alloc_oracles);
                                                      removereturn : 
                                                      ('asm_op _sprog ->
                                                      funname -> bool list
                                                      option);
                                                      regalloc : ('asm_op
                                                                 _sfun_decl
                                                                 list ->
                                                                 'asm_op
                                                                 _sfun_decl
                                                                 list);
                                                      print_uprog : (compiler_step
                                                                    ->
                                                                    'asm_op
                                                                    _uprog ->
                                                                    'asm_op
                                                                    _uprog);
                                                      print_sprog : (compiler_step
                                                                    ->
                                                                    'asm_op
                                                                    _sprog ->
                                                                    'asm_op
                                                                    _sprog);
                                                      print_linear : 
                                                      (compiler_step ->
                                                      'asm_op lprog ->
                                                      'asm_op lprog);
                                                      refresh_instr_info : 
                                                      (funname -> 'asm_op
                                                      _ufundef -> 'asm_op
                                                      _ufundef);
                                                      warning : (instr_info
                                                                ->
                                                                warning_msg
                                                                -> instr_info);
                                                      lowering_opt : 
                                                      'lowering_options;
                                                      fresh_id : (glob_decl
                                                                 list ->
                                                                 Var.var ->
                                                                 Ident.Ident.ident);
                                                      fresh_var_ident : 
                                                      (v_kind -> instr_info
                                                      -> Ident.Ident.name ->
                                                      stype ->
                                                      Ident.Ident.ident);
                                                      slh_info : ('asm_op
                                                                 _uprog ->
                                                                 funname ->
                                                                 slh_function_info);
                                                      stack_zero_info : 
                                                      (funname ->
                                                      (stack_zero_strategy * wsize
                                                      option) option);
                                                      protect_calls : 
                                                      bool;
                                                      pc_return_tree : 
                                                      (funname -> cs_info
                                                      list -> cs_info bintree) }

(** val rename_fd :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> instr_info -> funname -> 'a1
    _ufundef -> 'a1 _ufundef **)

let rename_fd _ c =
  c.rename_fd

(** val expand_fd :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> funname -> 'a1 _ufundef ->
    expand_info **)

let expand_fd _ c =
  c.expand_fd

(** val split_live_ranges_fd :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> funname -> 'a1 _ufundef -> 'a1
    _ufundef **)

let split_live_ranges_fd _ c =
  c.split_live_ranges_fd

(** val renaming_fd :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> funname -> 'a1 _ufundef -> 'a1
    _ufundef **)

let renaming_fd _ c =
  c.renaming_fd

(** val remove_phi_nodes_fd :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> funname -> 'a1 _ufundef -> 'a1
    _ufundef **)

let remove_phi_nodes_fd _ c =
  c.remove_phi_nodes_fd

(** val stack_register_symbol :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> Ident.Ident.ident **)

let stack_register_symbol _ c =
  c.stack_register_symbol

(** val global_static_data_symbol :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> Ident.Ident.ident **)

let global_static_data_symbol _ c =
  c.global_static_data_symbol

(** val stackalloc :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> 'a1 _uprog ->
    stack_alloc_oracles **)

let stackalloc _ c =
  c.stackalloc

(** val removereturn :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> 'a1 _sprog -> funname -> bool
    list option **)

let removereturn _ c =
  c.removereturn

(** val regalloc :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> 'a1 _sfun_decl list -> 'a1
    _sfun_decl list **)

let regalloc _ c =
  c.regalloc

(** val print_uprog :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> compiler_step -> 'a1 _uprog ->
    'a1 _uprog **)

let print_uprog _ c =
  c.print_uprog

(** val print_sprog :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> compiler_step -> 'a1 _sprog ->
    'a1 _sprog **)

let print_sprog _ c =
  c.print_sprog

(** val print_linear :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> compiler_step -> 'a1 lprog ->
    'a1 lprog **)

let print_linear _ c =
  c.print_linear

(** val refresh_instr_info :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> funname -> 'a1 _ufundef -> 'a1
    _ufundef **)

let refresh_instr_info _ c =
  c.refresh_instr_info

(** val warning :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> instr_info -> warning_msg ->
    instr_info **)

let warning _ c =
  c.warning

(** val lowering_opt : 'a1 asmOp -> ('a1, 'a2) compiler_params -> 'a2 **)

let lowering_opt _ c =
  c.lowering_opt

(** val fresh_id :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> glob_decl list -> Var.var ->
    Ident.Ident.ident **)

let fresh_id _ c =
  c.fresh_id

(** val fresh_var_ident :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> v_kind -> instr_info ->
    Ident.Ident.name -> stype -> Ident.Ident.ident **)

let fresh_var_ident _ c =
  c.fresh_var_ident

(** val slh_info :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> 'a1 _uprog -> funname ->
    slh_function_info **)

let slh_info _ c =
  c.slh_info

(** val stack_zero_info :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> funname ->
    (stack_zero_strategy * wsize option) option **)

let stack_zero_info _ c =
  c.stack_zero_info

(** val protect_calls : 'a1 asmOp -> ('a1, 'a2) compiler_params -> bool **)

let protect_calls _ c =
  c.protect_calls

(** val pc_return_tree :
    'a1 asmOp -> ('a1, 'a2) compiler_params -> funname -> cs_info list ->
    cs_info bintree **)

let pc_return_tree _ c =
  c.pc_return_tree

(** val split_live_ranges_prog :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> (('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) extended_op, 'a8) compiler_params -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) extended_op _uprog -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
    extended_op _uprog **)

let split_live_ranges_prog asm_e cparams p =
  Obj.magic map_prog_name (asm_opI asm_e) progUnit
    cparams.split_live_ranges_fd p

(** val renaming_prog :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> (('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) extended_op, 'a8) compiler_params -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) extended_op _uprog -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
    extended_op _uprog **)

let renaming_prog asm_e cparams p =
  Obj.magic map_prog_name (asm_opI asm_e) progUnit cparams.renaming_fd p

(** val remove_phi_nodes_prog :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> (('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) extended_op, 'a8) compiler_params -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) extended_op _uprog -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
    extended_op _uprog **)

let remove_phi_nodes_prog asm_e cparams p =
  Obj.magic map_prog_name (asm_opI asm_e) progUnit
    cparams.remove_phi_nodes_fd p

(** val var_tmp :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7, 'a8) architecture_params -> Var.var **)

let var_tmp asm_e aparams =
  { Var.vtype = (Coq_sword (coq_Uptr (arch_pd asm_e._asm._arch_decl)));
    Var.vname = aparams.ap_lip.lip_tmp }

(** val var_tmp2 :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7, 'a8) architecture_params -> Var.var **)

let var_tmp2 asm_e aparams =
  { Var.vtype = (Coq_sword (coq_Uptr (arch_pd asm_e._asm._arch_decl)));
    Var.vname = aparams.ap_lip.lip_tmp2 }

(** val var_tmps :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7, 'a8) architecture_params -> SvExtra.Sv.t **)

let var_tmps asm_e aparams =
  SvExtra.Sv.add (Obj.magic var_tmp2 asm_e aparams)
    (SvExtra.Sv.singleton (Obj.magic var_tmp asm_e aparams))

(** val check_removereturn :
    funname list -> (funname -> bool list option) -> (pp_error_loc, unit)
    result **)

let check_removereturn entries remove_return =
  if eq_op (seq_eqType (seq_eqType bool_eqType))
       (Obj.magic pmap remove_return entries) (Obj.magic [])
  then Ok ()
  else Error
         (pp_internal_error_s
           ('r'::('e'::('m'::('o'::('v'::('e'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::[])))))))))))))
           ('S'::('i'::('g'::('n'::('a'::('t'::('u'::('r'::('e'::(' '::('o'::('f'::(' '::('s'::('o'::('m'::('e'::(' '::('e'::('x'::('p'::('o'::('r'::('t'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::('s'::(' '::('a'::('r'::('e'::(' '::('m'::('o'::('d'::('i'::('f'::('i'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))))

(** val allNone : 'a1 option list -> bool **)

let allNone m =
  all (fun a -> match a with
                | Some _ -> false
                | None -> true) m

(** val check_no_ptr :
    funname list -> (funname -> stk_alloc_oracle_t) -> unit cexec **)

let check_no_ptr entries ao =
  allM (fun fn ->
    if allNone (ao fn).sao_params
    then if allNone (ao fn).sao_return
         then Ok ()
         else Error
                (pp_at_fn fn
                  (Stack_alloc.E.stk_error_no_var
                    ('e'::('x'::('p'::('o'::('r'::('t'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::('s'::(' '::('d'::('o'::('n'::('\226'::('\128'::('\153'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::(' '::('\226'::('\128'::('\156'::('p'::('t'::('r'::('\226'::('\128'::('\157'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('v'::('a'::('l'::('u'::('e'::('s'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    else let s =
           pp_at_fn fn
             (Stack_alloc.E.stk_error_no_var
               ('e'::('x'::('p'::('o'::('r'::('t'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::('s'::(' '::('d'::('o'::('n'::('\226'::('\128'::('\153'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::(' '::('\226'::('\128'::('\156'::('p'::('t'::('r'::('\226'::('\128'::('\157'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))
         in
         Error s) entries

(** val live_range_splitting :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7, 'a8) architecture_params -> (('a1, 'a2, 'a3, 'a4, 'a5,
    'a6, 'a7) extended_op, 'a8) compiler_params -> ('a1, 'a2, 'a3, 'a4, 'a5,
    'a6, 'a7) extended_op uprog -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
    extended_op uprog cexec **)

let live_range_splitting asm_e aparams cparams p =
  let pv = split_live_ranges_prog asm_e cparams (Obj.magic p) in
  let pv0 = cparams.print_uprog Splitting pv in
  let pv1 = renaming_prog asm_e cparams pv0 in
  let pv2 = cparams.print_uprog Renaming pv1 in
  let pv3 = remove_phi_nodes_prog asm_e cparams pv2 in
  let pv4 = cparams.print_uprog RemovePhiNodes pv3 in
  let pv5 =
    map_prog_name (asm_opI asm_e) progUnit
      (Obj.magic cparams.refresh_instr_info) (Obj.magic pv4)
  in
  (match check_uprog withsubword (asm_opI asm_e) p.p_extra p.p_funcs
           pv5.p_extra pv5.p_funcs with
   | Ok _ ->
     (match dead_code_prog (asm_opI asm_e) aparams.ap_is_move_op progUnit pv5
              false with
      | Ok x ->
        let p0 = cparams.print_uprog DeadCode_Renaming (Obj.magic x) in
        Ok (Obj.magic p0)
      | Error s -> Error s)
   | Error s -> Error s)

(** val inlining :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> (('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) extended_op, 'a8) compiler_params -> funname list -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7) extended_op uprog -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) extended_op uprog cexec **)

let inlining asm_e cparams to_keep p =
  match inline_prog_err withsubword (asm_opI asm_e)
          (Obj.magic cparams.rename_fd) p with
  | Ok x ->
    let p0 = cparams.print_uprog Inlining (Obj.magic x) in
    (match dead_calls_err_seq (asm_opI asm_e) progUnit to_keep (Obj.magic p0) with
     | Ok x0 ->
       let p1 = cparams.print_uprog RemoveUnusedFunction (Obj.magic x0) in
       Ok (Obj.magic p1)
     | Error s -> Error s)
  | Error s -> Error s

(** val compiler_first_part :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7, 'a8) architecture_params -> (('a1, 'a2, 'a3, 'a4, 'a5,
    'a6, 'a7) extended_op, 'a8) compiler_params -> funname list -> ('a1, 'a2,
    'a3, 'a4, 'a5, 'a6, 'a7) extended_op prog -> ('a1, 'a2, 'a3, 'a4, 'a5,
    'a6, 'a7) extended_op uprog cexec **)

let compiler_first_part asm_e aparams cparams to_keep p =
  match array_copy_prog (asm_opI asm_e)
          (cparams.fresh_var_ident Inline dummy_instr_info
            (Ident.Ident.name_of_string
              ('i'::('_'::('_'::('c'::('o'::('p'::('y'::[])))))))) Coq_sint)
          (fun ws ->
          cparams.fresh_var_ident (Reg (Normal, Direct)) dummy_instr_info
            (Ident.Ident.name_of_string ('t'::('m'::('p'::[])))) (Coq_sword
            ws)) progUnit p with
  | Ok x ->
    let p0 = cparams.print_uprog ArrayCopy (Obj.magic x) in
    let p1 = add_init_prog (asm_opI asm_e) progUnit (Obj.magic p0) in
    let p2 = cparams.print_uprog AddArrInit (Obj.magic p1) in
    (match spill_prog (asm_opI asm_e) cparams.fresh_var_ident progUnit
             (Obj.magic p2) with
     | Ok x0 ->
       let p3 = cparams.print_uprog LowerSpill (Obj.magic x0) in
       (match inlining asm_e cparams to_keep (Obj.magic p3) with
        | Ok x1 ->
          (match unroll_loop (arch_msfsz asm_e._asm._arch_decl)
                   (asm_opI asm_e) asm_e._asm._arch_decl.ad_fcp
                   aparams.ap_is_move_op x1 with
           | Ok x2 ->
             let p4 = cparams.print_uprog Unrolling (Obj.magic x2) in
             (match dead_calls_err_seq (asm_opI asm_e) progUnit to_keep
                      (Obj.magic p4) with
              | Ok x3 ->
                let p5 =
                  cparams.print_uprog RemoveUnusedFunction (Obj.magic x3)
                in
                (match live_range_splitting asm_e aparams cparams
                         (Obj.magic p5) with
                 | Ok x4 ->
                   let pr =
                     remove_init_prog (asm_opI asm_e) is_reg_array progUnit x4
                   in
                   let pr0 = cparams.print_uprog RemoveArrInit (Obj.magic pr)
                   in
                   (match makereference_prog (asm_opI asm_e)
                            (cparams.fresh_var_ident (Reg (Normal, (Pointer
                              Writable)))) (Obj.magic pr0) with
                    | Ok x5 ->
                      let pa =
                        cparams.print_uprog MakeRefArguments (Obj.magic x5)
                      in
                      (match expand_prog (asm_opI asm_e)
                               (Obj.magic cparams.expand_fd) to_keep
                               (Obj.magic pa) with
                       | Ok x6 ->
                         let pe =
                           cparams.print_uprog RegArrayExpansion
                             (Obj.magic x6)
                         in
                         (match live_range_splitting asm_e aparams cparams
                                  (Obj.magic pe) with
                          | Ok x7 ->
                            (match remove_glob_prog (asm_opI asm_e)
                                     cparams.fresh_id x7 with
                             | Ok x8 ->
                               let pg =
                                 cparams.print_uprog RemoveGlobal
                                   (Obj.magic x8)
                               in
                               if aparams.ap_lop.lop_fvars_correct
                                    (cparams.fresh_var_ident (Reg (Normal,
                                      Direct)) dummy_instr_info) progUnit
                                    (Obj.magic pg).p_funcs
                               then let pl =
                                      lower_prog (asm_opI asm_e)
                                        aparams.ap_lop.lop_lower_i
                                        cparams.lowering_opt cparams.warning
                                        (cparams.fresh_var_ident (Reg
                                          (Normal, Direct)) dummy_instr_info)
                                        progUnit (Obj.magic pg)
                                    in
                                    let pl0 =
                                      cparams.print_uprog LowerInstruction
                                        (Obj.magic pl)
                                    in
                                    (match lower_slh_prog (asm_opI asm_e)
                                             (arch_pd asm_e._asm._arch_decl)
                                             (arch_msfsz
                                               asm_e._asm._arch_decl)
                                             progUnit
                                             asm_e._asm._arch_decl.ad_fcp
                                             aparams.ap_shp
                                             (cparams.slh_info pl0)
                                             cparams.protect_calls to_keep
                                             (Obj.magic pl0) with
                                     | Ok x9 ->
                                       let pl1 =
                                         cparams.print_uprog SLHLowering
                                           (Obj.magic x9)
                                       in
                                       (match pi_prog (asm_opI asm_e)
                                                asm_e._asm._arch_decl.ad_fcp
                                                progUnit (Obj.magic pl1) with
                                        | Ok x10 ->
                                          let pp =
                                            cparams.print_uprog
                                              PropagateInline (Obj.magic x10)
                                          in
                                          Ok (Obj.magic pp)
                                        | Error s -> Error s)
                                     | Error s -> Error s)
                               else let s =
                                      pp_internal_error_s
                                        ('l'::('o'::('w'::('e'::('r'::('i'::('n'::('g'::[]))))))))
                                        ('l'::('o'::('w'::('e'::('r'::('i'::('n'::('g'::(' '::('c'::('h'::('e'::('c'::('k'::(' '::('f'::('a'::('i'::('l'::('s'::[]))))))))))))))))))))
                                    in
                                    Error s
                             | Error s -> Error s)
                          | Error s -> Error s)
                       | Error s -> Error s)
                    | Error s -> Error s)
                 | Error s -> Error s)
              | Error s -> Error s)
           | Error s -> Error s)
        | Error s -> Error s)
     | Error s -> Error s)
  | Error s -> Error s

(** val compiler_third_part :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7, 'a8) architecture_params -> (('a1, 'a2, 'a3, 'a4, 'a5,
    'a6, 'a7) extended_op, 'a8) compiler_params -> funname list -> ('a1, 'a2,
    'a3, 'a4, 'a5, 'a6, 'a7) extended_op sprog -> ('a1, 'a2, 'a3, 'a4, 'a5,
    'a6, 'a7) extended_op sprog cexec **)

let compiler_third_part asm_e aparams cparams entries ps =
  let rminfo = cparams.removereturn (Obj.magic ps) in
  (match check_removereturn entries rminfo with
   | Ok _ ->
     (match dead_code_prog_tokeep (asm_opI asm_e) aparams.ap_is_move_op false
              rminfo (progStack (arch_pd asm_e._asm._arch_decl)) ps with
      | Ok x ->
        let pr = cparams.print_sprog RemoveReturn (Obj.magic x) in
        let pa = { p_funcs = (cparams.regalloc pr.p_funcs); p_globs =
          pr.p_globs; p_extra = pr.p_extra }
        in
        let pa0 = cparams.print_sprog RegAllocation pa in
        (match check_sprog withsubword (asm_opI asm_e)
                 (arch_pd asm_e._asm._arch_decl) (Obj.magic pr).p_extra
                 (Obj.magic pr).p_funcs (Obj.magic pa0).p_extra
                 (Obj.magic pa0).p_funcs with
         | Ok _ ->
           (match dead_code_prog (asm_opI asm_e) aparams.ap_is_move_op
                    (progStack (arch_pd asm_e._asm._arch_decl))
                    (Obj.magic pa0) true with
            | Ok x0 ->
              let pd =
                cparams.print_sprog DeadCode_RegAllocation (Obj.magic x0)
              in
              Ok (Obj.magic pd)
            | Error s -> Error s)
         | Error s -> Error s)
      | Error s -> Error s)
   | Error s -> Error s)

(** val compiler_front_end :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7, 'a8) architecture_params -> (('a1, 'a2, 'a3, 'a4, 'a5,
    'a6, 'a7) extended_op, 'a8) compiler_params -> funname list -> ('a1, 'a2,
    'a3, 'a4, 'a5, 'a6, 'a7) extended_op prog -> ('a1, 'a2, 'a3, 'a4, 'a5,
    'a6, 'a7) extended_op sprog cexec **)

let compiler_front_end asm_e aparams cparams entries p =
  match compiler_first_part asm_e aparams cparams entries p with
  | Ok x ->
    let ao = cparams.stackalloc (Obj.magic x) in
    (match check_no_ptr entries ao.ao_stack_alloc with
     | Ok _ ->
       (match alloc_prog (arch_pd asm_e._asm._arch_decl)
                (arch_msfsz asm_e._asm._arch_decl) (asm_opI asm_e) true
                aparams.ap_shp aparams.ap_sap
                (cparams.fresh_var_ident (Reg (Normal, Direct))
                  dummy_instr_info) cparams.global_static_data_symbol
                cparams.stack_register_symbol ao.ao_globals
                ao.ao_global_alloc ao.ao_stack_alloc (Obj.magic x) with
        | Ok x0 ->
          let ps = cparams.print_sprog StackAllocation x0 in
          (match compiler_third_part asm_e aparams cparams entries
                   (Obj.magic ps) with
           | Ok x1 -> Ok x1
           | Error s -> Error s)
        | Error s -> Error s)
     | Error s -> Error s)
  | Error s -> Error s

(** val check_export :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> funname list -> ('a1,
    'a2, 'a3, 'a4, 'a5, 'a6, 'a7) extended_op sprog -> unit cexec **)

let check_export _ entries p =
  allM (fun fn ->
    match get_fundef p.p_funcs fn with
    | Some fd ->
      if is_RAnone (Obj.magic fd).f_extra.sf_return_address
      then Ok ()
      else Error
             (pp_at_fn fn
               (Merge_varmaps.E.gen_error true None
                 (pp_s
                   ('e'::('x'::('p'::('o'::('r'::('t'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('s'::(' '::('a'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::[])))))))))))))))))))))))))))))))))))))))))))
    | None ->
      Error
        (pp_at_fn fn
          (Merge_varmaps.E.gen_error true None
            (pp_s
              ('u'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('e'::('x'::('p'::('o'::('r'::('t'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))
    entries

(** val compiler_back_end :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5) calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8)
    architecture_params -> (('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) extended_op,
    'a8) compiler_params -> funname list -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6,
    'a7) extended_op sprog -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5, 'a6,
    'a7) extended_op lprog) result **)

let compiler_back_end asm_e call_conv aparams cparams entries pd =
  match check_export asm_e entries pd with
  | Ok _ ->
    (match check (arch_pd asm_e._asm._arch_decl) (asm_opI asm_e)
             (ovm_i asm_e._asm._arch_decl asm_e._atoI call_conv) pd
             (var_tmps asm_e aparams) with
     | Ok _ ->
       (match linear_prog (arch_pd asm_e._asm._arch_decl) (asm_opI asm_e)
                aparams.ap_lip pd with
        | Ok x ->
          let pl = cparams.print_linear Linearization x in
          (match pc_lprog (arch_pd asm_e._asm._arch_decl) (asm_opI asm_e)
                   aparams.ap_pcp cparams.pc_return_tree entries
                   cparams.protect_calls pl with
           | Ok x0 ->
             let pl0 = cparams.print_linear ProtectCalls x0 in
             let szs_of_fn = fun fn ->
               match cparams.stack_zero_info fn with
               | Some p ->
                 let (szs, ows) = p in
                 let ws =
                   match ows with
                   | Some ws -> ws
                   | None ->
                     (match get_fundef pl0.lp_funcs fn with
                      | Some lfd -> lfd.lfd_align
                      | None -> U8)
                 in
                 Some (szs, ws)
               | None -> None
             in
             (match stack_zeroization_lprog (arch_pd asm_e._asm._arch_decl)
                      (asm_opI asm_e)
                      (ovm_i asm_e._asm._arch_decl asm_e._atoI call_conv)
                      aparams.ap_szp szs_of_fn pl0 with
              | Ok x1 ->
                let pl1 = cparams.print_linear StackZeroization x1 in
                (match tunnel_program (asm_opI asm_e) pl1 with
                 | Ok x2 ->
                   let pl2 = cparams.print_linear Tunneling x2 in Ok pl2
                 | Error s -> Error s)
              | Error s -> Error s)
           | Error s -> Error s)
        | Error s -> Error s)
     | Error s -> Error s)
  | Error s -> Error s

(** val compiler_back_end_to_asm :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5) calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8)
    architecture_params -> (('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) extended_op,
    'a8) compiler_params -> funname list -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6,
    'a7) extended_op sprog -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_prog) result **)

let compiler_back_end_to_asm asm_e call_conv aparams cparams entries p =
  match compiler_back_end asm_e call_conv aparams cparams entries p with
  | Ok x -> assemble_prog asm_e call_conv aparams.ap_agp x
  | Error s -> Error s

(** val compile_prog_to_asm :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5) calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8)
    architecture_params -> (('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) extended_op,
    'a8) compiler_params -> funname list -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6,
    'a7) extended_op prog -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_prog cexec **)

let compile_prog_to_asm asm_e call_conv aparams cparams entries p =
  match compiler_front_end asm_e aparams cparams entries p with
  | Ok x -> compiler_back_end_to_asm asm_e call_conv aparams cparams entries x
  | Error s -> Error s
