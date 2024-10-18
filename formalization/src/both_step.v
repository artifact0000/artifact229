From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  security
  security_facts
  semantics
  semantics_facts
  syntax
  typesystem
  typesystem_facts
  utils
  utils_facts
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

Lemma both_single_step p cert sigma gamma m1 m1' m2 d o1 :
  eq_m gamma m1 m2
  -> typedm cert sigma gamma m1
  -> step p m1 d o1 m1'
  -> exists m2' o2, step p m2 d o2 m2'.
Proof.
  move: m1 m2 => [c f cs [vm1 mem1 ms]] [c2 f2 cs2 [vm2 mem2 ms2]] /=
    [/= ??? [[/= hvm_s hmem_s] hst_n ?]];
    subst c2 f2 cs2 ms2.
  move=> [/= theta [htyc htycs]].
  case: d => [| b | b j | g l xi cont];
    case: c htyc =>
      [|[ x e
        | x a e
        | a e x
        | msf
        | msf' msf e
        | x y msf
        | e c0 c1
        | e c0
        | l' xi' h
        ] c] // htyc /stepI //= [].
  - move=> _ _. by eeauto.
  - move=> i [hi hin _ _].
    move: htyc => /typedcI [? [? [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [htye ??].
    eexists; eexists.
    apply: step_load_n => //=; last exact: hin.
    rewrite /= -(eq_vm_eval_e_public (t := spublic) hvm_s) //.
    by eauto using ctx_le_typede_Public.
  - move=> i [hi hin _ _].
    move: htyc => /typedcI [? [? [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [htye ??].
    eexists; eexists.
    apply: step_store_n => //=; last exact: hin.
    rewrite /= -(eq_vm_eval_e_public (t := spublic) hvm_s) //.
    by eauto using ctx_le_typede_Public.
  - by eeauto.
  - by eeauto.
  - by eeauto.
  - by eeauto.
  - move=> ? [? _ _].
    move: htyc => /typedcI [? [? [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [htye _ _].
    eexists; eexists.
    apply: step_if; first reflexivity.
    rewrite /= -(eq_vm_eval_e_public (t := spublic) hvm_s);
      by eauto using ctx_le_typede_Public.
  - move=> ? [? _ _].
    move: htyc => /typedcI [? [? [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [htye _ _ _].
    eexists; eexists.
    apply: step_while; first reflexivity.
    rewrite /= -(eq_vm_eval_e_public (t := spublic) hvm_s);
      by eauto using ctx_le_typede_Public.
  - move=> i [hi hnina hinb hms _ _].
    move: htyc => /typedcI [? [? [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [htye ??].
    eexists; eexists.
    apply: step_load_s => //=; last exact: hnina.
    rewrite /= -(eq_vm_eval_e_public (t := spublic) hvm_s) //.
    by eauto using ctx_le_typede_Public.
  - move=> i [hi hnina hin hms _].
    move: htyc => /typedcI [? [? [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [htye ??].
    eexists; eexists.
    apply: step_store_s => //=; last exact: hnina.
    rewrite /= -(eq_vm_eval_e_public (t := spublic) hvm_s) //.
    by eauto using ctx_le_typede_Public.
  move=> _.
  case h: is_speculative_ret.
  - move=> [? _].
    eexists; eexists.
    apply: step_ret => //=.
    by rewrite h.
  move=> _.
  eexists; eexists.
  apply: step_ret => //=.
  by rewrite h.
Qed.

Lemma both_multi_step p cert m1 m1' m2 ds os1 sigma gamma :
  typedp cert p
  -> typedm cert sigma gamma m1
  -> synced sigma (st_vm (m_st m1)) (st_ms (m_st m1))
  -> synced sigma (st_vm (m_st m2)) (st_ms (m_st m2))
  -> eq_m gamma m1 m2
  -> sem p m1 ds os1 m1'
  -> exists m2' os2, sem p m2 ds os2 m2'.
Proof.
  move=> htyp.
  elim: ds m1 m2 os1 sigma gamma
    => [|d ds hind] m1 m2 os1 sigma gamma htym hsync1 hsync2 heq /semI.
  - by eeauto.
  move=> [o1 [os1' [? [mi1 hstep1 hsem1]]]]; subst os1.
  have [mi2 [o2 hstep2]] := both_single_step heq htym hstep1.
  have [//|] :=
    single_step_soundness (sigma := sigma) (gamma := gamma) htyp hstep1 hstep2.
  move=> ? [? [? [htymi hsynci1 hsynci2 heqi]]]; subst o2.
  have [m2' [os2 hsem2]] := hind _ _ _ _ _ htymi hsynci1 hsynci2 heqi hsem1.
  by eeauto.
Qed.

Definition both_initial_machines_step p cert ds os1 m1 m1' m2 :
  let: c := cert (p_entry_fn p) in
  let: sigma := cert_mss c in
  let: gamma := cert_ctx c in
  let: phi := initial_phi p gamma in
  let: st1 := m_st m1 in
  let: st2 := m_st m2 in
  wfcert cert p
  -> typedp cert p
  -> phi m1 m2
  -> sem p m1 ds os1 m1'
  -> exists m2' os2, sem p m2 ds os2 m2'.
Proof.
  set c := cert (p_entry_fn p).
  set gamma := cert_ctx c.
  rewrite /wfcert.
  move=> /= hsigma htyp [hm1 hm2 hst] hsem1.
  have htym1 := typedm_initial_machine htyp hm1.
  have htym2 := typedm_initial_machine htyp hm2.
  have heqm := eqm_initial_machine (And3 hm1 hm2 hst).
  have [] := both_multi_step htyp htym1 _ _ heqm hsem1.
  1-2: by case: cert_mss hsigma.
  by eeauto.
Qed.
