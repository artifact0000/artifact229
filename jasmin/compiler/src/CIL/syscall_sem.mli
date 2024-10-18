open BinNums
open Datatypes
open Low_memory
open Syscall
open Utils0
open Values
open Warray_
open Wsize

val exec_getrandom_u :
  'a1 syscall_sem -> 'a1 -> positive -> value list -> (error, 'a1 * value
  list) result

val exec_syscall_u :
  'a1 syscall_sem -> coq_PointerData -> 'a1 syscall_state_t -> Memory.mem ->
  BinNums.positive Syscall_t.syscall_t -> values -> (('a1
  syscall_state_t * Memory.mem) * values) exec
