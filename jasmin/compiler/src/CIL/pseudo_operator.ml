open BinNums
open Bool
open Eqtype
open Seq
open Ssrbool
open Type
open Utils0
open Wsize

type spill_op =
| Spill
| Unspill

(** val spill_op_beq : spill_op -> spill_op -> bool **)

let spill_op_beq x y =
  match x with
  | Spill -> (match y with
              | Spill -> true
              | Unspill -> false)
  | Unspill -> (match y with
                | Spill -> false
                | Unspill -> true)

(** val spill_op_eq_axiom : spill_op Equality.axiom **)

let spill_op_eq_axiom =
  eq_axiom_of_scheme spill_op_beq

(** val eqTC_spill_op : spill_op eqTypeC **)

let eqTC_spill_op =
  { beq = spill_op_beq; ceqP = spill_op_eq_axiom }

(** val spill_op_eqType : Equality.coq_type **)

let spill_op_eqType =
  ceqT_eqType eqTC_spill_op

type pseudo_operator =
| Ospill of spill_op * stype list
| Ocopy of wsize * positive
| Onop
| Omulu of wsize
| Oaddcarry of wsize
| Osubcarry of wsize
| Oswap of stype

(** val pseudo_operator_beq : pseudo_operator -> pseudo_operator -> bool **)

let pseudo_operator_beq o1 o2 =
  match o1 with
  | Ospill (o3, l1) ->
    (match o2 with
     | Ospill (o4, l2) ->
       (&&) (eq_op spill_op_eqType (Obj.magic o3) (Obj.magic o4))
         (eq_op (seq_eqType stype_eqType) (Obj.magic l1) (Obj.magic l2))
     | _ -> false)
  | Ocopy (w1, p1) ->
    (match o2 with
     | Ocopy (w2, p2) ->
       (&&) (eq_op wsize_eqType (Obj.magic w1) (Obj.magic w2))
         (eq_op pos_eqType (Obj.magic p1) (Obj.magic p2))
     | _ -> false)
  | Onop -> (match o2 with
             | Onop -> true
             | _ -> false)
  | Omulu w1 ->
    (match o2 with
     | Omulu w2 -> eq_op wsize_eqType (Obj.magic w1) (Obj.magic w2)
     | _ -> false)
  | Oaddcarry w1 ->
    (match o2 with
     | Oaddcarry w2 -> eq_op wsize_eqType (Obj.magic w1) (Obj.magic w2)
     | _ -> false)
  | Osubcarry w1 ->
    (match o2 with
     | Osubcarry w2 -> eq_op wsize_eqType (Obj.magic w1) (Obj.magic w2)
     | _ -> false)
  | Oswap t1 ->
    (match o2 with
     | Oswap t2 -> eq_op stype_eqType (Obj.magic t1) (Obj.magic t2)
     | _ -> false)

(** val pseudo_operator_eq_axiom : pseudo_operator Equality.axiom **)

let pseudo_operator_eq_axiom _top_assumption_ =
  let _evar_0_ = fun o1 l1 _top_assumption_0 ->
    let _evar_0_ = fun o2 l2 ->
      equivP
        ((&&) (eq_op spill_op_eqType o1 o2)
          (eq_op (seq_eqType stype_eqType) l1 l2))
        (andP (eq_op spill_op_eqType o1 o2)
          (eq_op (seq_eqType stype_eqType) l1 l2))
    in
    let _evar_0_0 = fun _ _ -> ReflectF in
    let _evar_0_1 = ReflectF in
    let _evar_0_2 = fun _ -> ReflectF in
    let _evar_0_3 = fun _ -> ReflectF in
    let _evar_0_4 = fun _ -> ReflectF in
    let _evar_0_5 = fun _ -> ReflectF in
    (match _top_assumption_0 with
     | Ospill (s, l) -> Obj.magic _evar_0_ s l
     | Ocopy (w, p) -> _evar_0_0 w p
     | Onop -> _evar_0_1
     | Omulu w -> _evar_0_2 w
     | Oaddcarry w -> _evar_0_3 w
     | Osubcarry w -> _evar_0_4 w
     | Oswap s -> _evar_0_5 s)
  in
  let _evar_0_0 = fun w1 p1 _top_assumption_0 ->
    let _evar_0_0 = fun _ _ -> ReflectF in
    let _evar_0_1 = fun w2 p2 ->
      equivP ((&&) (eq_op wsize_eqType w1 w2) (eq_op pos_eqType p1 p2))
        (andP (eq_op wsize_eqType w1 w2) (eq_op pos_eqType p1 p2))
    in
    let _evar_0_2 = ReflectF in
    let _evar_0_3 = fun _ -> ReflectF in
    let _evar_0_4 = fun _ -> ReflectF in
    let _evar_0_5 = fun _ -> ReflectF in
    let _evar_0_6 = fun _ -> ReflectF in
    (match _top_assumption_0 with
     | Ospill (s, l) -> _evar_0_0 s l
     | Ocopy (w, p) -> Obj.magic _evar_0_1 w p
     | Onop -> _evar_0_2
     | Omulu w -> _evar_0_3 w
     | Oaddcarry w -> _evar_0_4 w
     | Osubcarry w -> _evar_0_5 w
     | Oswap s -> _evar_0_6 s)
  in
  let _evar_0_1 = fun _top_assumption_0 ->
    let _evar_0_1 = fun _ _ -> ReflectF in
    let _evar_0_2 = fun _ _ -> ReflectF in
    let _evar_0_3 = ReflectT in
    let _evar_0_4 = fun _ -> ReflectF in
    let _evar_0_5 = fun _ -> ReflectF in
    let _evar_0_6 = fun _ -> ReflectF in
    let _evar_0_7 = fun _ -> ReflectF in
    (match _top_assumption_0 with
     | Ospill (s, l) -> _evar_0_1 s l
     | Ocopy (w, p) -> _evar_0_2 w p
     | Onop -> _evar_0_3
     | Omulu w -> _evar_0_4 w
     | Oaddcarry w -> _evar_0_5 w
     | Osubcarry w -> _evar_0_6 w
     | Oswap s -> _evar_0_7 s)
  in
  let _evar_0_2 = fun w1 _top_assumption_0 ->
    let _evar_0_2 = fun _ _ -> ReflectF in
    let _evar_0_3 = fun _ _ -> ReflectF in
    let _evar_0_4 = ReflectF in
    let _evar_0_5 = fun w2 ->
      equivP (eq_op wsize_eqType w1 w2) (eqP wsize_eqType w1 w2)
    in
    let _evar_0_6 = fun _ -> ReflectF in
    let _evar_0_7 = fun _ -> ReflectF in
    let _evar_0_8 = fun _ -> ReflectF in
    (match _top_assumption_0 with
     | Ospill (s, l) -> _evar_0_2 s l
     | Ocopy (w, p) -> _evar_0_3 w p
     | Onop -> _evar_0_4
     | Omulu w -> Obj.magic _evar_0_5 w
     | Oaddcarry w -> _evar_0_6 w
     | Osubcarry w -> _evar_0_7 w
     | Oswap s -> _evar_0_8 s)
  in
  let _evar_0_3 = fun w1 _top_assumption_0 ->
    let _evar_0_3 = fun _ _ -> ReflectF in
    let _evar_0_4 = fun _ _ -> ReflectF in
    let _evar_0_5 = ReflectF in
    let _evar_0_6 = fun _ -> ReflectF in
    let _evar_0_7 = fun w2 ->
      equivP (eq_op wsize_eqType w1 w2) (eqP wsize_eqType w1 w2)
    in
    let _evar_0_8 = fun _ -> ReflectF in
    let _evar_0_9 = fun _ -> ReflectF in
    (match _top_assumption_0 with
     | Ospill (s, l) -> _evar_0_3 s l
     | Ocopy (w, p) -> _evar_0_4 w p
     | Onop -> _evar_0_5
     | Omulu w -> _evar_0_6 w
     | Oaddcarry w -> Obj.magic _evar_0_7 w
     | Osubcarry w -> _evar_0_8 w
     | Oswap s -> _evar_0_9 s)
  in
  let _evar_0_4 = fun w1 _top_assumption_0 ->
    let _evar_0_4 = fun _ _ -> ReflectF in
    let _evar_0_5 = fun _ _ -> ReflectF in
    let _evar_0_6 = ReflectF in
    let _evar_0_7 = fun _ -> ReflectF in
    let _evar_0_8 = fun _ -> ReflectF in
    let _evar_0_9 = fun w2 ->
      equivP (eq_op wsize_eqType w1 w2) (eqP wsize_eqType w1 w2)
    in
    let _evar_0_10 = fun _ -> ReflectF in
    (match _top_assumption_0 with
     | Ospill (s, l) -> _evar_0_4 s l
     | Ocopy (w, p) -> _evar_0_5 w p
     | Onop -> _evar_0_6
     | Omulu w -> _evar_0_7 w
     | Oaddcarry w -> _evar_0_8 w
     | Osubcarry w -> Obj.magic _evar_0_9 w
     | Oswap s -> _evar_0_10 s)
  in
  let _evar_0_5 = fun t1 _top_assumption_0 ->
    let _evar_0_5 = fun _ _ -> ReflectF in
    let _evar_0_6 = fun _ _ -> ReflectF in
    let _evar_0_7 = ReflectF in
    let _evar_0_8 = fun _ -> ReflectF in
    let _evar_0_9 = fun _ -> ReflectF in
    let _evar_0_10 = fun _ -> ReflectF in
    let _evar_0_11 = fun t2 ->
      equivP (eq_op stype_eqType t1 t2) (eqP stype_eqType t1 t2)
    in
    (match _top_assumption_0 with
     | Ospill (s, l) -> _evar_0_5 s l
     | Ocopy (w, p) -> _evar_0_6 w p
     | Onop -> _evar_0_7
     | Omulu w -> _evar_0_8 w
     | Oaddcarry w -> _evar_0_9 w
     | Osubcarry w -> _evar_0_10 w
     | Oswap s -> Obj.magic _evar_0_11 s)
  in
  (match _top_assumption_ with
   | Ospill (s, l) -> Obj.magic _evar_0_ s l
   | Ocopy (w, p) -> Obj.magic _evar_0_0 w p
   | Onop -> _evar_0_1
   | Omulu w -> Obj.magic _evar_0_2 w
   | Oaddcarry w -> Obj.magic _evar_0_3 w
   | Osubcarry w -> Obj.magic _evar_0_4 w
   | Oswap s -> Obj.magic _evar_0_5 s)

(** val eqTC_pseudo_operator : pseudo_operator eqTypeC **)

let eqTC_pseudo_operator =
  { beq = pseudo_operator_beq; ceqP = pseudo_operator_eq_axiom }

(** val pseudo_operator_eqType : Equality.coq_type **)

let pseudo_operator_eqType =
  ceqT_eqType eqTC_pseudo_operator

(** val string_of_pseudo_operator : pseudo_operator -> char list **)

let string_of_pseudo_operator = function
| Ospill (s, _) ->
  (match s with
   | Spill -> 's'::('p'::('i'::('l'::('l'::[]))))
   | Unspill -> 'u'::('n'::('s'::('p'::('i'::('l'::('l'::[])))))))
| Ocopy (ws, _) -> pp_sz ('c'::('o'::('p'::('y'::[])))) ws ()
| Onop -> 'n'::('o'::('p'::[]))
| Omulu ws -> pp_sz ('m'::('u'::('l'::('u'::[])))) ws ()
| Oaddcarry ws -> pp_sz ('a'::('d'::('c'::[]))) ws ()
| Osubcarry ws -> pp_sz ('s'::('b'::('b'::[]))) ws ()
| Oswap _ -> 's'::('w'::('a'::('p'::[])))
