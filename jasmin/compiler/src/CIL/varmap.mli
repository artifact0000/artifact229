open Datatypes
open Eqtype
open Sem_type
open Ssrfun
open Type
open Utils0
open Values
open Var0
open Word0
open Wsize

type __ = Obj.t

val truncatable : coq_WithSubWord -> bool -> stype -> value -> bool

val vm_truncate_val : coq_WithSubWord -> stype -> value -> value

module type VM =
 sig
  type t

  val init : coq_WithSubWord -> t

  val get : coq_WithSubWord -> t -> Var.var -> value

  val set : coq_WithSubWord -> t -> Var.var -> value -> t
 end

module Vm :
 VM

val set_var :
  coq_WithSubWord -> bool -> Vm.t -> Var.var -> value -> (error, Vm.t) result

val get_var :
  coq_WithSubWord -> bool -> Vm.t -> Var.var -> (error, value) result
