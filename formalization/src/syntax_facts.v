From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  syntax
  utils
  utils_facts
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CODE_RECT.

Context
  (Pi : instruction -> Type)
  (Pc : code -> Type)
  (hassign : forall x e, Pi (Iassign x e))
  (hload : forall x a e, Pi (Iload x a e))
  (hstore : forall a e x, Pi (Istore a e x))
  (hinit_msf : forall msf, Pi (Iinit_msf msf))
  (hupdate_msf : forall msf' msf e, Pi (Iupdate_msf msf' msf e))
  (hprotect : forall x y msf, Pi (Iprotect x y msf))
  (hif : forall e c1 c0, Pc c1 -> Pc c0 -> Pi (Iif e c1 c0))
  (hwhile : forall e c1, Pc c1 -> Pi (Iwhile e c1))
  (hcall : forall l xi f, Pi (Icall l xi f))
  (hnil : Pc [::])
  (hcons : forall i c, Pi i -> Pc c -> Pc (i :: c))
.

Section CODE_RECT_AUX.
  Context (instruction_rect : forall i, Pi i).

  Fixpoint code_rect_aux (c : code) : Pc c :=
    match c return Pc c with
    | [::] => hnil
    | i :: c => hcons (instruction_rect i) (code_rect_aux c)
    end.

End CODE_RECT_AUX.

Fixpoint instruction_rect (i : instruction) : Pi i :=
  match i return Pi i with
  | Iassign x e => hassign x e
  | Iload x a e => hload x a e
  | Istore a e x => hstore a e x
  | Iinit_msf msf => hinit_msf msf
  | Iupdate_msf msf' msf e => hupdate_msf msf' msf e
  | Iprotect x y msf => hprotect x y msf
  | Iif e c1 c0 =>
      let h1 := code_rect_aux instruction_rect c1 in
      let h0 := code_rect_aux instruction_rect c0 in
      hif e h1 h0
  | Iwhile e c1 =>
      let h := code_rect_aux instruction_rect c1 in
      hwhile e h
  | Icall l xi f => hcall l xi f
  end.

Definition code_rect := code_rect_aux instruction_rect.

End CODE_RECT.

Lemma in_contpI p f g l xi cont :
  List.In (f, l, xi, cont) (contp g p)
  -> List.In (l, xi, cont) (contc g (p f)).
Proof.
  move=> /inP /mapP [] /= x hxin hx; apply /inP/mapP => /=.
  exists (g, (l, xi, cont)) => //.
  move: hxin hx; rewrite !mem_filter => /andP [] /eqP ? /flatten_mapP [caller] ? /mapP /=
    [] [] f1 [] [] l1 xi1 cont1 hin ?; subst x g => /= -[-> -> -> ->].
  by rewrite eqxx.
Qed.

Lemma label_lookupP p caller xi cont lr :
  uniq_labels p ->
  reflect
    (exists callee, (caller, lr, xi, cont) \in (contp callee p))
    (label_lookup lr p == Some (caller, lr, xi, cont)).
Proof.
  move=> huni; apply: (iffP idP); rewrite -(rwP eqP).
  + rewrite /label_lookup.
    case heq : filter => [ | [callee C1] l] //= [?]; subst C1; exists callee.
    apply/mapP; exists (callee, (caller, lr, xi, cont)) => //.
    have : (callee, (caller, lr, xi, cont)) \in [seq C <- all_conts p | label_of_cont C.2 == lr].
    + by rewrite heq in_cons eqxx.
    rewrite mem_filter => /andP [] _ hin1.
    by rewrite mem_filter eqxx.
  move=> [callee ] /mapP /= [[callee' C] ]; rewrite mem_filter; case: eqP => //= ?.
  move=> hin' ?; subst C; rewrite /label_lookup.
  have := has_filter (fun C => label_of_cont C.2 == lr) (all_conts p).
  have -> : has (fun C => label_of_cont C.2 == lr) (all_conts p).
  + by apply/hasP; eexists; eauto => //=.
  case heq : ([seq C <- all_conts p | label_of_cont C.2 == lr]) => [ | a l] //= _.
  have [/eqP h1 h2]: label_of_cont a.2 == lr /\ a \in all_conts p.
  + by apply /andP; rewrite -(mem_filter (fun C => label_of_cont C.2 == lr)) heq in_cons eqxx.
  move: hin' h2 => /(nthP a) /= [i hlti heq1] /(nthP a) /= [j hltj heq2].
  have /nth_uniq /= := huni.
  move /(_ (label_of_cont a.2) i j); rewrite !size_map => -/(_ hlti hltj).
  rewrite !(nth_map a) // heq1 heq2 /= h1 eqxx => /esym/eqP ?; subst i.
  by rewrite heq1 in heq2; rewrite -heq2.
Qed.

Lemma map_filter_oplus callee L c :
  [seq i.2 | i <- oplus L c & callee == i.1] =
  [seq (l, xi, x ++ c) | '(l, xi, x) <- [seq i.2 | i <- L & callee == i.1]].
Proof.
  rewrite !filter_map -!map_comp.
  set l1 := (l in map _ l = map _ _).
  set l2 := (l in map _ _ = map _ l).
  have -> : l1 = l2.
  + by rewrite /l1 /l2; apply eq_filter => -[] z [] [] /=.
  by apply eq_map => -[] ? [] [].
Qed.

Lemma contc_cons callee i c :
  contc callee (i :: c) = [seq (l, xi, x ++ c) |  '(l,xi,x) <- conti callee i] ++ contc callee c.
Proof. by rewrite /contc /= /= filter_cat map_cat map_filter_oplus. Qed.

Lemma conti_if callee e c1 c0 :
  conti callee (Iif e c1 c0) = contc callee c1 ++ contc callee c0.
Proof. by rewrite /conti /= filter_cat map_cat. Qed.

Lemma conti_while callee e c :
  conti callee (Iwhile e c) = [seq (l, xi, x ++ [:: Iwhile e c]) | '(l,xi,x) <- contc callee c].
Proof. by rewrite /conti /= -/all_contc map_filter_oplus. Qed.

Lemma conti_call callee l xi g :
  conti callee (Icall l xi g) =
    if callee == g then [:: (l, xi, [::]) ] else [::].
Proof. by rewrite /conti /=; case: ifP. Qed.

Lemma label_lookup_l p callee caller xi cont lr :
  uniq_labels p ->
  List.In (caller, lr, xi, cont) (contp callee p) ->
  label_lookup lr p = Some (caller, lr, xi, cont).
Proof. by move=> ??; apply/eqP/label_lookupP => //; exists callee; apply/inP. Qed.

Lemma uniq_contp f p :
  uniq_labels p ->
  uniq (contp f p).
Proof.
  rewrite /uniq_labels /contp => huniq.
  rewrite map_inj_in_uniq.
  + by apply/filter_uniq/map_uniq/huniq.
  move=> [] /= f1 C1 [f2 C2]; rewrite !mem_filter /=.
  by move=> /andP [] /eqP <- _ /andP [] /eqP <- _ ->.
Qed.
