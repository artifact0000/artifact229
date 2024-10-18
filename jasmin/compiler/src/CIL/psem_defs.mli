open BinInt
open BinNums
open Datatypes
open Eqtype
open Expr
open Flag_combination
open Global
open Low_memory
open Memory_model
open Sem_op_typed
open Sem_params
open Sem_type
open Sopn
open Ssralg
open Syscall
open Syscall_sem
open Type
open Utils0
open Values
open Var0
open Varmap
open Warray_
open Word0
open Wsize
open Xseq

val sem_sop1 : sop1 -> value -> value exec

val sem_sop2 : sop2 -> value -> value -> value exec

val sem_opN : coq_FlagCombinationParams -> opN -> values -> value exec

val get_global_value : glob_decl list -> Var.var -> glob_value option

val gv2val : glob_value -> value

val get_global : glob_decl list -> Var.var -> value exec

type 'syscall_state estate = { escs : 'syscall_state; emem : Memory.mem;
                               evm : Vm.t }

val escs : coq_WithSubWord -> 'a1 coq_EstateParams -> 'a1 estate -> 'a1

val emem : coq_WithSubWord -> 'a1 coq_EstateParams -> 'a1 estate -> Memory.mem

val evm : coq_WithSubWord -> 'a1 coq_EstateParams -> 'a1 estate -> Vm.t

val get_gvar :
  coq_WithSubWord -> bool -> glob_decl list -> Vm.t -> gvar -> (error, value)
  result

val get_var_is :
  coq_WithSubWord -> bool -> Vm.t -> var_i list -> (error, value list) result

val on_arr_var :
  value exec -> (positive -> WArray.array -> 'a1 exec) -> (error, 'a1) result

val with_vm :
  coq_WithSubWord -> 'a1 coq_EstateParams -> 'a1 estate -> Vm.t -> 'a1 estate

val with_mem :
  coq_WithSubWord -> 'a1 coq_EstateParams -> 'a1 estate -> Memory.mem -> 'a1
  estate

val with_scs :
  coq_WithSubWord -> 'a1 coq_EstateParams -> 'a1 estate -> 'a1 -> 'a1 estate

val sem_pexpr :
  coq_WithSubWord -> 'a1 coq_EstateParams -> coq_SemPexprParams -> bool ->
  glob_decl list -> 'a1 estate -> pexpr -> value exec

val sem_pexprs :
  coq_WithSubWord -> 'a1 coq_EstateParams -> coq_SemPexprParams -> bool ->
  glob_decl list -> 'a1 estate -> pexpr list -> (error, value list) result

val write_var :
  coq_WithSubWord -> 'a1 coq_EstateParams -> bool -> var_i -> value -> 'a1
  estate -> 'a1 estate exec

val write_vars :
  coq_WithSubWord -> 'a1 coq_EstateParams -> bool -> var_i list -> value list
  -> 'a1 estate -> (error, 'a1 estate) result

val write_none :
  coq_WithSubWord -> 'a1 coq_EstateParams -> bool -> 'a1 estate -> stype ->
  value -> (error, 'a1 estate) result

val write_lval :
  coq_WithSubWord -> 'a1 coq_EstateParams -> coq_SemPexprParams -> bool ->
  glob_decl list -> lval -> value -> 'a1 estate -> 'a1 estate exec

val write_lvals :
  coq_WithSubWord -> 'a1 coq_EstateParams -> coq_SemPexprParams -> bool ->
  glob_decl list -> 'a1 estate -> lval list -> value list -> (error, 'a1
  estate) result

val exec_sopn :
  'a2 coq_EstateParams -> 'a1 asmOp -> 'a1 sopn -> values -> values exec

val sem_sopn :
  coq_WithSubWord -> 'a2 coq_EstateParams -> coq_SemPexprParams -> 'a1 asmOp
  -> glob_decl list -> 'a1 sopn -> 'a2 estate -> lval list -> pexpr list ->
  (error, 'a2 estate) result

val syscall_sem__ :
  'a1 syscall_sem -> coq_PointerData -> 'a1 syscall_state_t -> Memory.mem ->
  BinNums.positive Syscall_t.syscall_t -> values -> (('a1
  syscall_state_t * Memory.mem) * values) exec
