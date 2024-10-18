From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "x |> f" := (f x) (only parsing, at level 25).

Notation "'let%opt' x ':=' ox 'in' body" :=
  (obind (fun x => body) ox)
  (x strict pattern, at level 25).
Notation "'let%opt '_' ':=' ox 'in' body" :=
  (obind (fun 'tt => body) ox)
  (at level 25).

Definition Z_eqMixin := EqMixin Z.eqb_spec.
Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.

Definition oassert (b : bool) : option unit :=
  if b then Some tt else None.

Lemma eq_axiom_of_scheme X (beq : X -> X -> bool) :
  (forall x y : X, beq x y -> x = y) ->
  (forall x y : X, x = y -> beq x y) ->
  Equality.axiom beq.
Proof. move=> hbl hlb x y. apply: (iffP idP); first exact: hbl. exact: hlb. Qed.

Definition incl (X : eqType) (xs ys : seq X) : bool :=
  all (fun x => x \in ys) xs.

Definition flat_map (X Y : Type) (f : X -> seq Y) (xs : seq X) : seq Y :=
  flatten (map f xs).
