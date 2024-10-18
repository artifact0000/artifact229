open BinInt
open BinNums
open Datatypes
open Div
open Eqtype
open Expr
open Flag_combination
open Sem_type
open Ssralg
open Type
open Utils0
open Word0
open Word_ssrZ
open Wsize

(** val sem_sop1_typed : sop1 -> sem_t -> sem_t **)

let sem_sop1_typed = function
| Oword_of_int sz -> Obj.magic wrepr sz
| Oint_of_word sz -> Obj.magic wunsigned sz
| Osignext (szo, szi) -> sign_extend szo szi
| Ozeroext (szo, szi) -> zero_extend szo szi
| Onot -> Obj.magic negb
| Olnot sz -> wnot sz
| Oneg o0 ->
  (match o0 with
   | Op_int -> Obj.magic Z.opp
   | Op_w sz -> GRing.opp (GRing.ComRing.zmodType (word sz)))

(** val zlsl : coq_Z -> coq_Z -> coq_Z **)

let zlsl x i =
  if Z.leb Z0 i
  then Z.mul x (Z.pow (Zpos (Coq_xO Coq_xH)) i)
  else Z.div x (Z.pow (Zpos (Coq_xO Coq_xH)) (Z.opp i))

(** val zasr : coq_Z -> coq_Z -> coq_Z **)

let zasr x i =
  zlsl x (Z.opp i)

(** val sem_shift :
    (wsize -> GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort) -> wsize ->
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let sem_shift shift s v i =
  let i0 = wunsigned U8 i in shift s v i0

(** val sem_shr :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let sem_shr s =
  sem_shift wshr s

(** val sem_sar :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let sem_sar s =
  sem_shift wsar s

(** val sem_shl :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let sem_shl s =
  sem_shift wshl s

(** val sem_ror :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let sem_ror s =
  sem_shift wror s

(** val sem_rol :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let sem_rol s =
  sem_shift wrol s

(** val sem_vadd :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let sem_vadd ve ws =
  lift2_vec (wsize_of_velem ve)
    (GRing.add (GRing.ComRing.zmodType (word (wsize_of_velem ve)))) ws

(** val sem_vsub :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let sem_vsub ve ws =
  lift2_vec (wsize_of_velem ve) (fun x y ->
    GRing.add (GRing.ComRing.zmodType (word (wsize_of_velem ve))) x
      (GRing.opp (GRing.ComRing.zmodType (word (wsize_of_velem ve))) y)) ws

(** val sem_vmul :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let sem_vmul ve ws =
  lift2_vec (wsize_of_velem ve)
    (GRing.mul (GRing.ComRing.ringType (word (wsize_of_velem ve)))) ws

(** val sem_vshr :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let sem_vshr ve ws v i =
  lift1_vec (wsize_of_velem ve) (fun x ->
    wshr (wsize_of_velem ve) x (wunsigned U8 i)) ws v

(** val sem_vsar :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let sem_vsar ve ws v i =
  lift1_vec (wsize_of_velem ve) (fun x ->
    wsar (wsize_of_velem ve) x (wunsigned U8 i)) ws v

(** val sem_vshl :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let sem_vshl ve ws v i =
  lift1_vec (wsize_of_velem ve) (fun x ->
    wshl (wsize_of_velem ve) x (wunsigned U8 i)) ws v

(** val signed : 'a1 -> 'a1 -> signedness -> 'a1 **)

let signed fu fs = function
| Signed -> fs
| Unsigned -> fu

(** val mk_sem_divmod :
    wsize -> (GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort)
    -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort exec **)

let mk_sem_divmod sz o w1 w2 =
  if (||)
       (eq_op (GRing.ComRing.eqType (word sz)) w2
         (GRing.zero (GRing.ComRing.zmodType (word sz))))
       ((&&)
         (eq_op coq_Z_eqType (Obj.magic wsigned sz w1)
           (Obj.magic wmin_signed sz))
         (eq_op (GRing.ComRing.eqType (word sz)) w2
           (GRing.opp
             (GRing.Ring.zmodType (GRing.ComRing.ringType (word sz)))
             (GRing.one (GRing.ComRing.ringType (word sz))))))
  then Error ErrArith
  else Ok (o w1 w2)

(** val mk_sem_sop2 : ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a2 -> 'a3 exec **)

let mk_sem_sop2 o v1 v2 =
  Ok (o v1 v2)

(** val sem_sop2_typed : sop2 -> sem_t -> sem_t -> sem_t exec **)

let sem_sop2_typed = function
| Obeq ->
  mk_sem_sop2
    (Obj.magic eq_op
      (Equality.clone bool_eqType (Obj.magic bool_eqMixin) (fun x -> x)))
| Oand -> mk_sem_sop2 (Obj.magic (&&))
| Oor -> mk_sem_sop2 (Obj.magic (||))
| Oadd o0 ->
  (match o0 with
   | Op_int -> mk_sem_sop2 (Obj.magic Z.add)
   | Op_w s -> mk_sem_sop2 (GRing.add (GRing.ComRing.zmodType (word s))))
| Omul o0 ->
  (match o0 with
   | Op_int -> mk_sem_sop2 (Obj.magic Z.mul)
   | Op_w s -> mk_sem_sop2 (GRing.mul (GRing.ComRing.ringType (word s))))
| Osub o0 ->
  (match o0 with
   | Op_int -> mk_sem_sop2 (Obj.magic Z.sub)
   | Op_w s ->
     mk_sem_sop2 (fun x y ->
       GRing.add (GRing.ComRing.zmodType (word s)) x
         (GRing.opp (GRing.ComRing.zmodType (word s)) y)))
| Odiv c ->
  (match c with
   | Cmp_int -> mk_sem_sop2 (Obj.magic Z.div)
   | Cmp_w (u, s) -> mk_sem_divmod s (signed (wdiv s) (wdivi s) u))
| Omod c ->
  (match c with
   | Cmp_int -> mk_sem_sop2 (Obj.magic Z.modulo)
   | Cmp_w (u, s) -> mk_sem_divmod s (signed (wmod s) (wmodi s) u))
| Oland s -> mk_sem_sop2 (wand s)
| Olor s -> mk_sem_sop2 (wor s)
| Olxor s -> mk_sem_sop2 (wxor s)
| Olsr s -> mk_sem_sop2 (sem_shr s)
| Olsl o0 ->
  (match o0 with
   | Op_int -> mk_sem_sop2 (Obj.magic zlsl)
   | Op_w s -> mk_sem_sop2 (sem_shl s))
| Oasr o0 ->
  (match o0 with
   | Op_int -> mk_sem_sop2 (Obj.magic zasr)
   | Op_w s -> mk_sem_sop2 (sem_sar s))
| Oror s -> mk_sem_sop2 (sem_ror s)
| Orol s -> mk_sem_sop2 (sem_rol s)
| Oeq o0 ->
  (match o0 with
   | Op_int -> mk_sem_sop2 (Obj.magic Z.eqb)
   | Op_w s -> mk_sem_sop2 (Obj.magic eq_op (GRing.ComRing.eqType (word s))))
| Oneq o0 ->
  (match o0 with
   | Op_int ->
     mk_sem_sop2 (fun x y ->
       Obj.magic negb (Z.eqb (Obj.magic x) (Obj.magic y)))
   | Op_w s ->
     mk_sem_sop2 (fun x y ->
       Obj.magic negb (eq_op (GRing.ComRing.eqType (word s)) x y)))
| Olt c ->
  (match c with
   | Cmp_int -> mk_sem_sop2 (Obj.magic Z.ltb)
   | Cmp_w (u, s) -> mk_sem_sop2 (Obj.magic wlt s u))
| Ole c ->
  (match c with
   | Cmp_int -> mk_sem_sop2 (Obj.magic Z.leb)
   | Cmp_w (u, s) -> mk_sem_sop2 (Obj.magic wle s u))
| Ogt c ->
  (match c with
   | Cmp_int -> mk_sem_sop2 (Obj.magic Z.gtb)
   | Cmp_w (u, s) -> mk_sem_sop2 (fun x y -> Obj.magic wlt s u y x))
| Oge c ->
  (match c with
   | Cmp_int -> mk_sem_sop2 (Obj.magic Z.geb)
   | Cmp_w (u, s) -> mk_sem_sop2 (fun x y -> Obj.magic wle s u y x))
| Ovadd (ve, ws) -> mk_sem_sop2 (sem_vadd ve ws)
| Ovsub (ve, ws) -> mk_sem_sop2 (sem_vsub ve ws)
| Ovmul (ve, ws) -> mk_sem_sop2 (sem_vmul ve ws)
| Ovlsr (ve, ws) -> mk_sem_sop2 (sem_vshr ve ws)
| Ovlsl (ve, ws) -> mk_sem_sop2 (sem_vshl ve ws)
| Ovasr (ve, ws) -> mk_sem_sop2 (sem_vsar ve ws)

(** val sem_combine_flags :
    coq_FlagCombinationParams -> combine_flags -> bool -> bool -> bool ->
    bool -> bool **)

let sem_combine_flags cfcd cf b0 b1 b2 b3 =
  cf_xsem cfcd negb (&&) (||) (fun x y ->
    eq_op bool_eqType (Obj.magic x) (Obj.magic y)) b0 b1 b2 b3 cf

(** val sem_opN_typed :
    coq_FlagCombinationParams -> opN -> sem_t exec sem_prod **)

let sem_opN_typed cfcd = function
| Opack (sz, pe) ->
  curry Coq_sint (divn (nat_of_wsize sz) (nat_of_pelem pe)) (fun vs -> Ok
    (wpack sz (nat_of_pelem pe) (Obj.magic vs)))
| Ocombine_flags cf ->
  Obj.magic (fun b0 b1 b2 b3 -> Ok (sem_combine_flags cfcd cf b0 b1 b2 b3))
