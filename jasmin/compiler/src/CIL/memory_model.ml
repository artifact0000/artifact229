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

module LE =
 struct
  (** val encode : wsize -> GRing.ComRing.sort -> GRing.ComRing.sort list **)

  let encode sz w =
    Obj.magic split_vec sz (nat_of_wsize U8) w

  (** val decode : wsize -> GRing.ComRing.sort list -> GRing.ComRing.sort **)

  let decode sz n =
    make_vec U8 sz n

  (** val wread8 :
      wsize -> GRing.ComRing.sort -> coq_Z -> GRing.Zmodule.sort **)

  let wread8 ws v k =
    nth (GRing.zero (GRing.ComRing.zmodType (word U8))) (encode ws v)
      (Z.to_nat k)
 end

type pointer_op = { add : (Equality.sort -> coq_Z -> Equality.sort);
                    sub : (Equality.sort -> Equality.sort -> coq_Z);
                    p_to_z : (Equality.sort -> coq_Z) }

(** val is_align :
    Equality.coq_type -> pointer_op -> Equality.sort -> wsize -> bool **)

let is_align _ pointer p sz =
  eq_op coq_Z_eqType (Obj.magic Z.modulo (pointer.p_to_z p) (wsize_size sz))
    (Obj.magic Z0)

type 'core_mem coreMem = { get : ('core_mem -> Equality.sort ->
                                 GRing.ComRing.sort exec);
                           set : ('core_mem -> Equality.sort ->
                                 GRing.ComRing.sort -> 'core_mem exec);
                           valid8 : ('core_mem -> Equality.sort -> bool);
                           valid8P : ('core_mem -> Equality.sort ->
                                     GRing.ComRing.sort -> reflect) }

module CoreMem =
 struct
  (** val read :
      Equality.coq_type -> pointer_op -> 'a1 coreMem -> 'a1 -> Equality.sort
      -> wsize -> GRing.ComRing.sort exec **)

  let read pointer pointer0 cM m ptr sz =
    if is_align pointer pointer0 ptr sz
    then (match mapM (fun k -> cM.get m (pointer0.add ptr k))
                  (ziota Z0 (wsize_size sz)) with
          | Ok x -> Ok (LE.decode sz x)
          | Error s -> Error s)
    else let s = ErrAddrInvalid in Error s

  (** val write :
      Equality.coq_type -> pointer_op -> 'a1 coreMem -> 'a1 -> Equality.sort
      -> wsize -> GRing.ComRing.sort -> 'a1 exec **)

  let write pointer pointer0 cM m ptr sz w =
    if is_align pointer pointer0 ptr sz
    then foldM (fun k m0 ->
           cM.set m0 (pointer0.add ptr k) (LE.wread8 sz w k)) m
           (ziota Z0 (wsize_size sz))
    else let s = ErrAddrInvalid in Error s
 end

(** val coq_Pointer : coq_PointerData -> pointer_op **)

let coq_Pointer pd =
  { add = (fun p k ->
    GRing.add (GRing.ComRing.zmodType (word (coq_Uptr pd))) p
      (wrepr (coq_Uptr pd) k)); sub = (fun p1 p2 ->
    wunsigned (coq_Uptr pd)
      (GRing.add (GRing.ComRing.zmodType (word (coq_Uptr pd))) p1
        (GRing.opp (GRing.ComRing.zmodType (word (coq_Uptr pd))) p2)));
    p_to_z = (fun p -> wunsigned (coq_Uptr pd) p) }

(** val round_ws : wsize -> coq_Z -> coq_Z **)

let round_ws ws sz =
  let d = wsize_size ws in
  let (q, r) = Z.div_eucl sz d in
  if eq_op coq_Z_eqType (Obj.magic r) (Obj.magic Z0)
  then sz
  else Z.mul (Z.add q (Zpos Coq_xH)) d

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
