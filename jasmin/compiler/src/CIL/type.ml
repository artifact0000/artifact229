open BinNums
open BinPos
open Datatypes
open Eqtype
open Utils0
open Wsize

type stype =
| Coq_sbool
| Coq_sint
| Coq_sarr of positive
| Coq_sword of wsize

(** val internal_positive_beq : positive -> positive -> bool **)

let rec internal_positive_beq x y =
  match x with
  | Coq_xI x0 ->
    (match y with
     | Coq_xI x1 -> internal_positive_beq x0 x1
     | _ -> false)
  | Coq_xO x0 ->
    (match y with
     | Coq_xO x1 -> internal_positive_beq x0 x1
     | _ -> false)
  | Coq_xH -> (match y with
               | Coq_xH -> true
               | _ -> false)

(** val stype_beq : stype -> stype -> bool **)

let stype_beq x y =
  match x with
  | Coq_sbool -> (match y with
                  | Coq_sbool -> true
                  | _ -> false)
  | Coq_sint -> (match y with
                 | Coq_sint -> true
                 | _ -> false)
  | Coq_sarr x0 ->
    (match y with
     | Coq_sarr x1 -> internal_positive_beq x0 x1
     | _ -> false)
  | Coq_sword x0 ->
    (match y with
     | Coq_sword x1 -> wsize_beq x0 x1
     | _ -> false)

(** val stype_axiom : stype Equality.axiom **)

let stype_axiom =
  eq_axiom_of_scheme stype_beq

(** val stype_eqMixin : stype Equality.mixin_of **)

let stype_eqMixin =
  { Equality.op = stype_beq; Equality.mixin_of__1 = stype_axiom }

(** val stype_eqType : Equality.coq_type **)

let stype_eqType =
  Obj.magic stype_eqMixin

(** val stype_cmp : stype -> stype -> comparison **)

let stype_cmp t t' =
  match t with
  | Coq_sbool -> (match t' with
                  | Coq_sbool -> Eq
                  | _ -> Lt)
  | Coq_sint -> (match t' with
                 | Coq_sbool -> Gt
                 | Coq_sint -> Eq
                 | _ -> Lt)
  | Coq_sarr n -> (match t' with
                   | Coq_sarr n' -> Pos.compare n n'
                   | _ -> Gt)
  | Coq_sword w ->
    (match t' with
     | Coq_sarr _ -> Lt
     | Coq_sword w' -> wsize_cmp w w'
     | _ -> Gt)

(** val is_sword : stype -> bool **)

let is_sword = function
| Coq_sword _ -> true
| _ -> false

(** val is_sarr : stype -> bool **)

let is_sarr = function
| Coq_sarr _ -> true
| _ -> false

(** val is_word_type : stype -> wsize option **)

let is_word_type = function
| Coq_sword sz -> Some sz
| _ -> None

(** val subtype : stype -> stype -> bool **)

let subtype t t' =
  match t with
  | Coq_sword w ->
    (match t' with
     | Coq_sword w' -> cmp_le wsize_cmp w w'
     | _ -> false)
  | _ -> eq_op stype_eqType (Obj.magic t) (Obj.magic t')
