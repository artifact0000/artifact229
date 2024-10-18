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

val internal_positive_beq : positive -> positive -> bool

val stype_beq : stype -> stype -> bool

val stype_axiom : stype Equality.axiom

val stype_eqMixin : stype Equality.mixin_of

val stype_eqType : Equality.coq_type

val stype_cmp : stype -> stype -> comparison

val is_sword : stype -> bool

val is_sarr : stype -> bool

val is_word_type : stype -> wsize option

val subtype : stype -> stype -> bool
