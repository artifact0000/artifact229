(* -------------------------------------------------------------------------- *)
(* Variables. *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import
  MSets
  Structures.Equalities
  ZArith
.
From mathcomp Require Import all_ssreflect.

Require Import utils.

Open Scope Z.


Module Type VarT.
  Parameter t : eqType.
End VarT.

Module VS(V : VarT).
  Module VarT_as_DT <: DecidableType.
    Definition t := Equality.sort V.t.
    Definition eq (x y : t) : Prop := x = y.
    Lemma eq_equiv : Equivalence eq.
    Proof. split; congruence. Qed.
    Definition eq_dec : forall x y, {eq x y} + {~ eq x y}.
    Proof. move=> x y. case: (x =P y); by econstructor. Defined.
  End VarT_as_DT.

  Module VS := MSetWeakList.Make(VarT_as_DT).
  Include VS.
  Include MSetProperties.WProperties(VS).
  Include MSetDecide.Decide(VS).

  Lemma eqP x y : reflect (x = y) (F.eqb x y).
  Proof. rewrite /F.eqb /F.eq_dec. case: eqP; by constructor. Qed.

  Lemma eqbP x y : (F.eqb x y) = (x == y).
  Proof. rewrite /F.eqb /F.eq_dec. by case: eqtype.eqP. Qed.
End VS.

Module DefaultVar : VarT.
  Definition t : eqType := nat_eqType.
End DefaultVar.
