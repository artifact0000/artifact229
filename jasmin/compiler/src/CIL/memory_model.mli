open BinInt
open BinNums
open Bool
open Eqtype
open Seq
open Ssralg
open Utils0
open Word0
open Word_ssrZ
open Wsize

module LE :
 sig
  val encode : wsize -> GRing.ComRing.sort -> GRing.ComRing.sort list

  val decode : wsize -> GRing.ComRing.sort list -> GRing.ComRing.sort

  val wread8 : wsize -> GRing.ComRing.sort -> coq_Z -> GRing.Zmodule.sort
 end

type pointer_op = { add : (Equality.sort -> coq_Z -> Equality.sort);
                    sub : (Equality.sort -> Equality.sort -> coq_Z);
                    p_to_z : (Equality.sort -> coq_Z) }

val is_align :
  Equality.coq_type -> pointer_op -> Equality.sort -> wsize -> bool

type 'core_mem coreMem = { get : ('core_mem -> Equality.sort ->
                                 GRing.ComRing.sort exec);
                           set : ('core_mem -> Equality.sort ->
                                 GRing.ComRing.sort -> 'core_mem exec);
                           valid8 : ('core_mem -> Equality.sort -> bool);
                           valid8P : ('core_mem -> Equality.sort ->
                                     GRing.ComRing.sort -> reflect) }

module CoreMem :
 sig
  val read :
    Equality.coq_type -> pointer_op -> 'a1 coreMem -> 'a1 -> Equality.sort ->
    wsize -> GRing.ComRing.sort exec

  val write :
    Equality.coq_type -> pointer_op -> 'a1 coreMem -> 'a1 -> Equality.sort ->
    wsize -> GRing.ComRing.sort -> 'a1 exec
 end

val coq_Pointer : coq_PointerData -> pointer_op

val round_ws : wsize -> coq_Z -> coq_Z

type 'mem memory = { stack_root : ('mem -> GRing.ComRing.sort);
                     stack_limit : ('mem -> GRing.ComRing.sort);
                     frames : ('mem -> GRing.ComRing.sort list);
                     alloc_stack : ('mem -> wsize -> coq_Z -> coq_Z -> coq_Z
                                   -> 'mem exec);
                     free_stack : ('mem -> 'mem);
                     init : ((GRing.ComRing.sort * coq_Z) list ->
                            GRing.ComRing.sort -> 'mem exec) }

module type MemoryT =
 sig
  type mem

  val coq_CM : coq_PointerData -> mem coreMem

  val coq_M : coq_PointerData -> mem memory
 end
