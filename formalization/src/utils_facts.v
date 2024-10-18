From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import utils.


Create HintDb local.

Ltac eeauto :=
  subst;
  do 10 (done || congruence || eauto with local || econstructor).

Section CONJUNCTION.

Context (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : Prop).

Variant and6 : Prop :=
  And6 of P1 & P2 & P3 & P4 & P5 & P6.

Lemma proj6_1 : and6 -> P1.
Proof. by case. Qed.

Lemma proj6_2 : and6 -> P2.
Proof. by case. Qed.

Lemma proj6_3 : and6 -> P3.
Proof. by case. Qed.

Lemma proj6_4 : and6 -> P4.
Proof. by case. Qed.

Lemma proj6_5 : and6 -> P5.
Proof. by case. Qed.

Lemma proj6_6 : and6 -> P6.
Proof. by case. Qed.

Variant and7 : Prop :=
  And7 of P1 & P2 & P3 & P4 & P5 & P6 & P7.
Variant and8 : Prop :=
  And8 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8.
Variant and9 : Prop :=
  And9 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9.
Variant and10 : Prop :=
  And10 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10.

End CONJUNCTION.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" :=
  (and6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" :=
  (and6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" :=
  (and7 P1 P2 P3 P4 P5 P6 P7) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" :=
  (and8 P1 P2 P3 P4 P5 P6 P7 P8) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" :=
  (and9 P1 P2 P3 P4 P5 P6 P7 P8 P9) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" :=
  (and10 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10) : type_scope.

Lemma obindP {aT bT oa} {f : aT -> option bT} {a} (P : Type) :
  (forall z, oa = Some z -> f z = Some a -> P) ->
  (let%opt a' := oa in f a') = Some a ->
  P.
Proof. case: oa => // a' h h'. exact: (h _ _ h'). Qed.

Lemma oassertP {A b a} {oa : option A} :
  (let%opt _ := oassert b in oa) = Some a ->
  b /\ oa = Some a.
Proof. by case: b. Qed.

Lemma oassertP_isSome {A b} {oa : option A} :
  isSome (let%opt _ := oassert b in oa) ->
  b /\ isSome oa.
Proof. by case: b. Qed.

Ltac t_obindP :=
  match goal with
  | [ |- Option.bind _ _ = Some _ -> _ ] => apply: obindP; t_obindP
  | [ |- Option.map _ _ = Some _ -> _ ] => rewrite /Option.map; t_obindP
  | [ |- oassert _ = Some _ -> _ ] => move=> /oassertP; t_obindP
  | [ |- unit -> _ ] => case; t_obindP
  | [ |- Some _ = Some _ -> _ ] => case; t_obindP
  | [ |- forall h, _ ] => let hh := fresh h in move=> hh; t_obindP; move: hh
  | _ => idtac
  end.

Lemma map_in {A B} {f : A -> B} {l y} :
  List.In y (map f l) ->
  (exists x : A, f x = y /\ List.In x l).
Proof. move=> *. by apply List.in_map_iff. Qed.

Lemma inP (T: eqType) (s : seq T) m :
  reflect (List.In m s) (m \in s).
Proof.
  elim: s. by constructor.
  move => a s ih. rewrite in_cons.
  case: (@eqP _ m a). by constructor; left.
  case ih; constructor. by right. simpl; intuition.
Qed.

Lemma or_dec (b : bool) (P : Prop) :
  b \/ P <-> (~~ b -> P).
Proof.
  split.
  - case: b; first done. by case.
  case: b; by auto.
Qed.

Lemma orb_implP (b b' : bool) :
  (b -> b') -> ~~ b || b'.
Proof. move=> ?. rewrite -implybE. by apply/implyP. Qed.

Lemma inclP (X : eqType) (xs ys : seq X) :
  reflect (List.incl xs ys) (incl xs ys).
Proof.
  apply: (iffP idP).
  - move=> /allP h.
    by apply/List.incl_Forall_in_iff/List.Forall_forall => x /inP /h /inP.
  move=> /List.incl_Forall_in_iff/List.Forall_forall h.
  by apply/allP => x /inP /h /inP.
Qed.

Lemma perm_eq_nil (X : eqType) (s : seq X) :
  perm_eq s [::] = (s == [::]).
Proof.
  case h: perm_eq; move: h => /perm_nilP /eqP //. by rewrite eq_sym => /negPf.
Qed.

Lemma isSome_exists T (ox : option T) :
  reflect (exists x, ox = Some x) (isSome ox).
Proof. case: ox => [?|]; first by eeauto. constructor. by move=> []. Qed.

Lemma lfindP (X:eqType) (f: X -> bool) (l : seq X) : 
  reflect (exists x, List.find f l = Some x) (has f l).
Proof.
  apply: (equivP hasP); split.
  + move=> [x /inP hin hf].
    case heq: (List.find f l); eauto.
    by rewrite (List.find_none _ _ heq x hin) in hf.
  by move=> [] x hfi; have [/inP ??]:= List.find_some f _ hfi; exists x.
Qed.
