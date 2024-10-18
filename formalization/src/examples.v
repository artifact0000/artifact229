(* -------------------------------------------------------------------------- *)
(* Example programs and their typability. *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  examples_utils
  notations
  syntax
  syntax_facts
  typesystem
  typesystem_facts
  utils
  utils_facts
  var
.
Import ExpressionNotations.
Import CodeNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

Definition leak x : instruction := code:(
  if $(x) == #0 then skip else skip end
).

Lemma typedi_leak cert sigma sigma' gamma gamma' x :
  sty_s (ctx_reg gamma x) = Secret
  -> ~ typedi cert sigma gamma (leak x) sigma' gamma'.
Proof.
  move=> hrsec /typediI [he _ _].
  move: he => /typedeI [_ [_ [/typedeI -> _ /esym /sty_max_spublicI [hx _]]]].
  by rewrite hx in hrsec.
Qed.

Definition assign_leak_secret x rsec := code:(
  x = $(rsec);
  coq:(leak x);
  skip
).

Lemma typed_assign_leak_secret cert sigma sigma' gamma gamma' x rsec :
  let: c := assign_leak_secret x rsec in
  sty_s (ctx_reg gamma rsec) = Secret
  -> ~ typedc cert sigma gamma c sigma' gamma'.
Proof.
  move=> hrsec /typedcI [? [? [? [? [? [? [hi hc ?? hgamma ?]]]]]]].
  move: hi => /typediI [? [? /typedeI ? ?]]; subst.
  move: hc => /typedc_typedi [? [? [? [? [hleak ?? hgamma' ?]]]]].
  apply: typedi_leak; last eassumption.
  have := ctx_le_reg hgamma' x.
  rewrite /= eqxx => /andP [] _.
  move: (ctx_le_reg hgamma rsec) => /andP [] _.
  by rewrite hrsec => /lvl_le_SecretI -> /lvl_le_SecretI.
Qed.

(* Figure 1a from "Typing High-Speed Cryptography Against Spectre v1". *)
Definition spec_load x i a b := code:(
  if $(i) < #10
  then x = load(a, $(i)); skip
  else x = #0; skip
  end;
  store(b, $(x)) = i;
  skip
).

Lemma typed_spec_load cert sigma gamma sigma' gamma' x i a b :
  let: c := spec_load x i a b in
  ~ typedc cert sigma gamma c sigma' gamma'.
Proof.
  move=> /typedcI [? [? [? [? [? [? [hi hc ????]]]]]]].

  move: hi => /typediI [_ hc0 _].
  move: hc0 => /typedcI [? [? [? [? [? [? [hi hc0 ????]]]]]]].
  move: hi => /typediI [_ _ ?]; subst.
  move: hc0 => /typedcI [? hload].
  move: (ctx_le_reg hload x) => /andP [] _.
  rewrite /= eqxx => /lvl_le_SecretI hsec.

  move: hc => /typedc_typedi [? [? [? [? [hi ????]]]]].
  move: hi => /typediI [/typedeI hstore _ _].
  move: hstore.
  rewrite -(sty_surj (ctx_reg _ _)) => -[] _ /= hpub.
  have : lvl_le Secret Public; last done.
  rewrite -hsec hpub.
  rewrite -ty_le_ty_of_lvl.
  apply: (sty_le_ty_le false).
  by eeauto.
Qed.

Definition fixed_spec_load msf x i a b := code:(
  msf = init_msf();
  if $(i) < #10
  then
    msf = update_msf(msf, $(i) < #10);
    x = load(a, $(i));
    skip
  else
    msf = update_msf(msf, ! ($(i) < #10));
    x = #0;
    skip
  end;
  x = protect(x, msf);
  store(b, $(x)) = i;
  skip
).

Lemma typed_fixed_spec_load cert sigma gamma msf x i a b :
  let: c := fixed_spec_load msf x i a b in
  sty_n (ctx_reg gamma i) = tpublic
  -> sty_n (ctx_arr gamma a) = tpublic
  -> x != msf
  -> exists sigma' gamma',
      typedc cert sigma gamma c sigma' gamma'.
Proof.
  move=> hi ha /negPf hx.
  set gamma0 := ctx_after_init_msf gamma msf.
  eexists; eexists.

  have hi0 : ctx_reg gamma0 i = spublic.
  - by rewrite /= /sty_after_init_msf hi if_same.

  have ha0 : ctx_arr gamma0 a = spublic.
  - by rewrite /= /sty_after_init_msf ha.

  econstructor;
    last econstructor;
    last econstructor.

  (* msf = init_msf(); *)
  - by constructor.

  (* if *)
  - econstructor.

    (* i < 10 is public *)
    + rewrite -sty_max_spublicE. rewrite -{1}hi0. econstructor; by eeauto.

    (* then *)
    + econstructor.

      (* msf = update_msf(msf, i < 10); *)
      * by constructor.

      (* x = load(a, i); *)
      * apply: typedi_typedc.
        constructor.
        rewrite -hi0.
        by constructor.

    (* else *)
    econstructor.

    (* msf = update_msf(msf, ! (i < 10)); *)
    + by constructor.

    (* x = 0; *)
    apply: typed_weak.
    + apply: typedi_typedc. by eeauto.
    + by eeauto.
    + by eeauto.
    + by eeauto.
    apply: ctx_le_ctx_update_reg; first exact: ctx_le_refl.
    exact: sty_le_spublic.

  (* x = protect(x, msf); *)
  - rewrite /mss_restrict /= Sr.F.singleton_b Sr.eqbP eq_sym hx. by constructor.

  rewrite /ctx_after_load ha0 /ctx_after_protect /= eqxx
    eq_ctx_ctx_update_reg_ctx_update_reg /sty_after_init_msf /= -/spublic.
  apply: typedi_typedc.

  (* store(b, x) = i; *)
  constructor.
  - set gamma' := (X in typede X _ _).
    have -> : spublic = ctx_reg gamma' x; last by constructor.
    by rewrite /gamma0 /= eqxx.
  split.
  - by eeauto.
  - by rewrite /= /sty_after_init_msf hi -/spublic !if_same sty_le_spublic.
  move=> a' _.
  by rewrite /= /sty_after_init_msf hi -/spublic !if_same lvl_le_Public.
Qed.

Definition rsb_basic l l' x f a i := code:(
  x = #0;
  i = #0;
  call(l, f);
  coq:(leak x);
  x = load(a, $(i));
  call(l', f);
  skip
).

Lemma typed_rsb_basic cert sigma gamma sigma' gamma' l l' x f a i :
  let: c := rsb_basic l l' x f a i in
  let: gammaf := cert_ctx (cert f) in
  let: gammaf' := cert_ctx' (cert f) in
  lvl_le (ctx_reg gammaf x |> sty_s) (ctx_reg gammaf' x |> sty_s)
  -> ~ typedc cert sigma gamma c sigma' gamma'.
Proof.
  move=> hx /typedcI [? [? [? [? [? [? [hi hc _ _ _ _]]]]]]].
  move: hi => /typediI [? [t /typedeI ??]]; subst.
  move: hc => /typedcI [? [? [? [? [? [? [hi hc _ _ _ _]]]]]]].
  move: hi => /typediI [? [t /typedeI ??]]; subst.
  move: hc => /typedcI [? [? [? [? [? [? [hi hc _ _ _ _]]]]]]].
  move: hi => /typediI [?? [theta0 [??]]]; subst.
  move: hc => /typedcI [? [? [? [? [? [? [hleak hc _ _ hafter _]]]]]]].
  move: hc => /typedcI [? [? [? [? [? [? [hi hc _ _ _ _]]]]]]].
  move: hi => /typediI [_ ??]; subst.
  move: hc => /typedc_typedi [? [? [? [? [hi _ _ hbefore _]]]]].
  move: hi => /typediI [?? [theta1 [??]]]; subst.
  apply: typedi_leak; last eassumption.
  apply: lvl_le_SecretI.
  move: (ctx_le_reg hafter x)  => /andP [/= _].
  apply: lvl_le_trans.
  apply: (lvl_le_trans _ hx).
  move: (ctx_le_reg hbefore x) => /andP [/= _].
  by rewrite eqxx => /lvl_le_SecretI ->.
Qed.

Section RSB_BASIC_FIXED.

Context
  (msf x i : regvar)
  (tx ti : typevar)
  (a : arrvar)
  (f : funname)
  (l l' : label)
.

(* This is Figure 1b from our paper. *)
Definition rsb_basic_fixed := code:(
  msf = init_msf();
  x = #0;
  i = #0;
  call(l, msf, f);
  x = protect(x, msf);
  store(a, $(x)) = i; (* Instead of leak(x), because it kills the msf. *)
  x = load(a, $(i));
  call(l', f);
  skip
).

Definition gammaf :=
  {|
    ctx_reg r :=
      if r == x
      then {| sty_n := tvar tx; sty_s := Secret; |}
      else
        if r == i
        then {| sty_n := tvar ti; sty_s := Public; |}
        else ssecret;
    ctx_arr _ := ssecret;
  |}.

Definition certf :=
  {|
    cert_mss := MSSupdated msf;
    cert_mss' := MSSupdated msf;
    cert_ctx := gammaf;
    cert_ctx' := gammaf;
  |}.

Definition theta0 t :=
  if (t == tx) || (t == ti)
  then Public
  else Secret.

End RSB_BASIC_FIXED.

Lemma typed_rsb_basic_fixed cert sigma gamma msf l l' x i tx ti a f :
  let: c := rsb_basic_fixed msf x i a f l l' in
  cert f = certf msf x i tx ti
  -> x != msf
  -> i != msf
  -> i != x
  -> exists sigma' gamma', typedc cert sigma gamma c sigma' gamma'.
Proof.
  move=> hcert /negPf hneq_x_msf /negPf hneq_i_msf /negPf hneq_i_x.
  eexists; eexists.

  econstructor.
  (* msf = init_msf(); *)
  - by constructor.

  econstructor.
  (* x = 0; *)
  - constructor. by constructor.

  rewrite /mss_restrict /= Sr.F.singleton_b Sr.eqbP eq_sym hneq_x_msf.
  econstructor.
  (* i = 0; *)
  - constructor. by constructor.

  rewrite /mss_restrict /= Sr.F.singleton_b Sr.eqbP eq_sym hneq_i_msf.
  apply: typed_weak;
    [|exact: mss_le_refl | exact: mss_le_refl | | exact: ctx_le_refl].
  econstructor.

  (* call msf f; *)
  - have -> : MSSupdated msf = cert_mss (cert f).
    + by rewrite hcert.
    apply: (typed_call (theta0 tx ti)).
    rewrite hcert /= eqxx.
    reflexivity.

  all: rewrite hcert /=.
  all: cycle 1.
  - split=> [y | ?] /=; last exact: sty_le_ssecret.
    case: (x =P y) => [_ | hy].
    + by rewrite if_same sty_le_spublic.
    move: hy => /nesym /eqP /negPf ->.
    rewrite eq_sym.
    case: (y =P i) => _; first exact: sty_le_spublic.
    by rewrite /sty_instantiate /= sty_le_ssecret.

  econstructor.

  (* x = protect(x, msf); *)
  - by constructor.

  rewrite /mss_restrict /= Sr.F.singleton_b Sr.eqbP eq_sym hneq_x_msf.
  econstructor.

  (* leak(x); *)
  - constructor.
    + set gamma0 := ctx_after_protect _ _ _.
      have -> : spublic = ctx_reg gamma0 x; last by constructor.
      by rewrite /= eqxx /sty_after_init_msf /theta0 /= eqxx.
    split.
    + exact: ctx_le_refl.
    + by rewrite /= !eqxx eq_sym hneq_i_x /sty_instantiate /theta0 /= eqxx orbT.
    by rewrite /= eqxx eq_sym hneq_i_x lvl_le_Secret.

  econstructor.

  (* x = load(a, i); *)
  - constructor.
    set gamma0 := ctx_after_protect _ _ _.
    have -> : spublic = ctx_reg gamma0 i; last by constructor.
    + by rewrite /= eqxx /sty_after_init_msf /theta0 /= !eqxx eq_sym hneq_i_x
        /sty_instantiate /= eqxx orbT.

  rewrite /mss_restrict /= Sr.F.singleton_b Sr.eqbP eq_sym hneq_x_msf.

  (* call f; *)
  apply: typed_weak;
    [|exact: mss_le_refl | exact: mss_le_refl | | exact: ctx_le_refl].
  - have -> : MSSupdated msf = cert_mss (cert f).
    + by rewrite hcert.
    apply: typedi_typedc.
    apply: (typed_call theta_Secret).
    rewrite hcert.
    reflexivity.

  rewrite hcert.
  split=> [y|] //=.
  rewrite !eqxx /sty_instantiate /theta0 /theta_Secret /=.
  case: (x =P y).
  + move=> ->. by rewrite /= !eqxx.
  move=> /nesym /eqP /negPf -> /=.
  case: (y =P i) => //=.
  by rewrite eqxx orbT.
Qed.

Definition is_MSSoutdated (sigma : mss) : bool :=
  if sigma is MSSoutdated _ _ then true else false.

Definition force_cond_misspeculation (sigma : mss) (c : code) : code :=
  let upd b :=
    let onot := if b then enot else id in
    let e := onot (Ebool false) in
    if sigma is MSSupdated msf
    then code:(msf = update_msf(msf, e); skip)
    else code:(skip)
  in
  let c1 := upd false ++ c in
  let c0 := upd true ++ c in
  code:(if ff then c1 else c0 end; skip).

Lemma speculative_polymorphism cert sigma gamma c sigma' gamma' :
  ~~ is_MSSoutdated sigma ->
  typedc cert sigma gamma c sigma' gamma' ->
  typedc cert sigma gamma (force_cond_misspeculation sigma c) sigma' gamma'.
Proof.
  move=> hsigma hc.
  apply: typedi_typedc.
  case: sigma hsigma hc => [|msf|//] _ hc; by eeauto.
Qed.
