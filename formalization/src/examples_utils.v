From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  syntax
  syntax_facts
  typesystem
  typesystem_facts
  utils
  utils_facts
.

Open Scope Z.

Lemma sty_surj t :
  {| sty_n := sty_n t; sty_s := sty_s t; |} = t.
Proof. by move: t => []. Qed.

Lemma sty_le_ty_le is_n gamma gamma' x :
  let: proj := fun x => if is_n then sty_n x else ty_of_lvl (sty_s x) in
  ctx_le gamma gamma'
  -> ty_le (proj (ctx_reg gamma x)) (proj (ctx_reg gamma' x)).
Proof. move=> [] /(_ x) /andP []. case: is_n => //; by eeauto. Qed.

Lemma eq_ctx_ctx_update_reg_ctx_update_reg gamma x t t' :
  let: gamma' := ctx_update_reg (ctx_update_reg gamma x t) x t' in
  eq_ctx gamma' (ctx_update_reg gamma x t').
Proof. split=> ? //=. by case: eqP. Qed.

Lemma ctx_le_ctx_update_reg gamma gamma' x t t' :
  ctx_le gamma gamma'
  -> sty_le t t'
  -> ctx_le (ctx_update_reg gamma x t) (ctx_update_reg gamma' x t').
Proof. move=> [??] ht. split=> ? //=. by case: eqP. Qed.

Lemma ty_max_lift t0 t1 t0' t1' :
  ty_le t0 t0'
  -> ty_le t1 t1'
  -> ty_le (ty_max t0 t1) (ty_max t0' t1').
Proof. move=> *. apply: ty_max_least; by eeauto. Qed.

Lemma sty_max_lift t0 t1 t0' t1' :
  sty_le t0 t0'
  -> sty_le t1 t1'
  -> sty_le (sty_max t0 t1) (sty_max t0' t1').
Proof. move=> *. apply: sty_max_least; by eeauto. Qed.

Lemma ctx_le_typede_typede gamma gamma' e t t' :
  ctx_le gamma gamma'
  -> typede gamma e t
  -> typede gamma' e t'
  -> sty_le t t'.
Proof.
  move=> hle.
  elim: e t t' =>
    [z | b | x | op e hind | op e0 hind0 e1 hind1] t t' /typedeI h /typedeI h'.
  - by subst.
  - by subst.
  - subst. exact: (ctx_le_reg hle).
  - by auto.
  move: h => [t0 [t1 [h0 h1 ?]]]; subst t.
  move: h' => [t0' [t1' [h0' h1' ?]]]; subst t'.
  have hle0 := hind0 _ _ h0 h0'.
  have hle1 := hind1 _ _ h1 h1'.
  by eauto using sty_max_lift.
Qed.
