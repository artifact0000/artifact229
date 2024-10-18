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

val pp_s : char list -> pp_error

val unroll :
  coq_MSFsize -> 'a1 asmOp -> coq_FlagCombinationParams -> ('a1 asm_op_t ->
  bool) -> nat -> 'a1 uprog -> 'a1 uprog cexec

val unroll_loop :
  coq_MSFsize -> 'a1 asmOp -> coq_FlagCombinationParams -> ('a1 asm_op_t ->
  bool) -> 'a1 uprog -> (pp_error_loc, 'a1 uprog) result

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

val compiler_step_list : compiler_step list

val compiler_step_beq : compiler_step -> compiler_step -> bool

val compiler_step_eq_dec : compiler_step -> compiler_step -> bool

val compiler_step_eq_axiom : compiler_step Equality.axiom

val compiler_step_eqMixin : compiler_step Equality.mixin_of

val compiler_step_eqType : Equality.coq_type

type stack_alloc_oracles = { ao_globals : GRing.ComRing.sort list;
                             ao_global_alloc : ((Var.var * wsize) * coq_Z)
                                               list;
                             ao_stack_alloc : (funname -> stk_alloc_oracle_t) }

val ao_globals : stack_alloc_oracles -> GRing.ComRing.sort list

val ao_global_alloc : stack_alloc_oracles -> ((Var.var * wsize) * coq_Z) list

val ao_stack_alloc : stack_alloc_oracles -> funname -> stk_alloc_oracle_t

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

val rename_fd :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> instr_info -> funname -> 'a1
  _ufundef -> 'a1 _ufundef

val expand_fd :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> funname -> 'a1 _ufundef ->
  expand_info

val split_live_ranges_fd :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> funname -> 'a1 _ufundef -> 'a1
  _ufundef

val renaming_fd :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> funname -> 'a1 _ufundef -> 'a1
  _ufundef

val remove_phi_nodes_fd :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> funname -> 'a1 _ufundef -> 'a1
  _ufundef

val stack_register_symbol :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> Ident.Ident.ident

val global_static_data_symbol :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> Ident.Ident.ident

val stackalloc :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> 'a1 _uprog -> stack_alloc_oracles

val removereturn :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> 'a1 _sprog -> funname -> bool
  list option

val regalloc :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> 'a1 _sfun_decl list -> 'a1
  _sfun_decl list

val print_uprog :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> compiler_step -> 'a1 _uprog ->
  'a1 _uprog

val print_sprog :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> compiler_step -> 'a1 _sprog ->
  'a1 _sprog

val print_linear :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> compiler_step -> 'a1 lprog ->
  'a1 lprog

val refresh_instr_info :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> funname -> 'a1 _ufundef -> 'a1
  _ufundef

val warning :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> instr_info -> warning_msg ->
  instr_info

val lowering_opt : 'a1 asmOp -> ('a1, 'a2) compiler_params -> 'a2

val fresh_id :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> glob_decl list -> Var.var ->
  Ident.Ident.ident

val fresh_var_ident :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> v_kind -> instr_info ->
  Ident.Ident.name -> stype -> Ident.Ident.ident

val slh_info :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> 'a1 _uprog -> funname ->
  slh_function_info

val stack_zero_info :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> funname ->
  (stack_zero_strategy * wsize option) option

val protect_calls : 'a1 asmOp -> ('a1, 'a2) compiler_params -> bool

val pc_return_tree :
  'a1 asmOp -> ('a1, 'a2) compiler_params -> funname -> cs_info list ->
  cs_info bintree

val split_live_ranges_prog :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> (('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) extended_op, 'a8) compiler_params -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) extended_op _uprog -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op _uprog

val renaming_prog :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> (('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) extended_op, 'a8) compiler_params -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) extended_op _uprog -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op _uprog

val remove_phi_nodes_prog :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> (('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) extended_op, 'a8) compiler_params -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) extended_op _uprog -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op _uprog

val var_tmp :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7, 'a8) architecture_params -> Var.var

val var_tmp2 :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7, 'a8) architecture_params -> Var.var

val var_tmps :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7, 'a8) architecture_params -> SvExtra.Sv.t

val check_removereturn :
  funname list -> (funname -> bool list option) -> (pp_error_loc, unit) result

val allNone : 'a1 option list -> bool

val check_no_ptr :
  funname list -> (funname -> stk_alloc_oracle_t) -> unit cexec

val live_range_splitting :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7, 'a8) architecture_params -> (('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op, 'a8) compiler_params -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op uprog -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) extended_op uprog
  cexec

val inlining :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> (('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) extended_op, 'a8) compiler_params -> funname list -> ('a1, 'a2,
  'a3, 'a4, 'a5, 'a6, 'a7) extended_op uprog -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) extended_op uprog cexec

val compiler_first_part :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7, 'a8) architecture_params -> (('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op, 'a8) compiler_params -> funname list -> ('a1, 'a2, 'a3, 'a4,
  'a5, 'a6, 'a7) extended_op prog -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op uprog cexec

val compiler_third_part :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7, 'a8) architecture_params -> (('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op, 'a8) compiler_params -> funname list -> ('a1, 'a2, 'a3, 'a4,
  'a5, 'a6, 'a7) extended_op sprog -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op sprog cexec

val compiler_front_end :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7, 'a8) architecture_params -> (('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op, 'a8) compiler_params -> funname list -> ('a1, 'a2, 'a3, 'a4,
  'a5, 'a6, 'a7) extended_op prog -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op sprog cexec

val check_export :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> funname list -> ('a1, 'a2,
  'a3, 'a4, 'a5, 'a6, 'a7) extended_op sprog -> unit cexec

val compiler_back_end :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5)
  calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8)
  architecture_params -> (('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) extended_op,
  'a8) compiler_params -> funname list -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op sprog -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op lprog) result

val compiler_back_end_to_asm :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5)
  calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8)
  architecture_params -> (('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) extended_op,
  'a8) compiler_params -> funname list -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op sprog -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
  asm_prog) result

val compile_prog_to_asm :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5)
  calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7, 'a8)
  architecture_params -> (('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) extended_op,
  'a8) compiler_params -> funname list -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op prog -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_prog cexec
