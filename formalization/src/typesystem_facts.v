From Coq Require Import
  Classes.RelationClasses
  ZArith
.
From Coq Require Morphisms.
From mathcomp Require Import all_ssreflect.

Require Import
  syntax
  syntax_facts
  typesystem
  utils
  utils_facts
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.


(* -------------------------------------------------------------------------- *)
(* Variable contexts. *)

Lemma lvl_le_refl : reflexive lvl_le.
Proof. by move=> []. Qed.

Lemma lvl_le_Public l :
  lvl_le Public l.
Proof. done. Qed.

Lemma lvl_le_PublicI l :
  lvl_le l Public
  -> l = Public.
Proof. by case: l. Qed.

Lemma lvl_le_Secret l :
  lvl_le l Secret.
Proof. by rewrite /lvl_le orbT. Qed.

Lemma lvl_le_SecretI l :
  lvl_le Secret l
  -> l = Secret.
Proof. by case: l. Qed.

Lemma lvl_le_trans : transitive lvl_le.
Proof. by move=> [] // []. Qed.

Lemma lvl_max_comm : commutative lvl_max.
Proof. by move=> [] []. Qed.

Lemma lvl_max_assoc : associative lvl_max.
Proof. by move=> [] [] []. Qed.

Lemma lvl_max_bound l l' :
  let: lmax := lvl_max l l' in
  lvl_le l lmax /\ lvl_le l' lmax.
Proof. case: l; by case: l'. Qed.

Definition lvl_max_bound_l l l' := proj1 (lvl_max_bound l l').
Definition lvl_max_bound_r l l' := proj2 (lvl_max_bound l l').

Lemma lvl_max_least l0 l1 l :
  lvl_le l0 l
  -> lvl_le l1 l
  -> lvl_le (lvl_max l0 l1) l.
Proof. case: l0 => //; by case: l1. Qed.

Lemma lvl_max_Public l :
  lvl_max l Public = l.
Proof. by case: l. Qed.

Lemma lvl_max_PublicI l l' :
  lvl_max l l' = Public
  -> l = Public /\ l' = Public.
Proof. case: l => //; by case: l'. Qed.

Lemma lvl_max_Secret l :
  lvl_max Secret l = Secret.
Proof. by case: l. Qed.

Hint Resolve lvl_le_refl lvl_max_Public lvl_max_Secret | 1 : local.
Hint Resolve
  lvl_max_bound_l lvl_max_bound_r lvl_le_Public lvl_le_Secret | 2 : local.
Hint Resolve lvl_le_trans lvl_max_least | 3 : local.


Lemma ty_eqb_refl : reflexive ty_eqb.
Proof. by move=> [|?] //=. Qed.

Lemma ty_eqb_sym : symmetric ty_eqb.
Proof. move=> [|?] [|?] //=. exact: perm_sym. Qed.

Lemma ty_eqb_trans : transitive ty_eqb.
Proof. move=> [|?] [|?] [|?] //=. exact: perm_trans. Qed.

Lemma ty_eqb_tpublic t : reflect (t = tpublic) (ty_eqb t tpublic).
Proof.
  case: t => [|[|x s]].
  - by constructor.
  - by constructor.
  rewrite /= perm_eq_nil.
  by constructor.
Qed.

Lemma ty_eqb_tsecret t : reflect (t = tsecret) (ty_eqb t tsecret).
Proof. case: t; by constructor. Qed.

Hint Resolve ty_eqb_refl | 1 : local.
Hint Resolve ty_eqb_sym | 2 : local.
Hint Resolve ty_eqb_trans | 3 : local.


Lemma ty_le_refl : reflexive ty_le.
Proof. move=> [|?] //=. apply/inclP. exact: List.incl_refl. Qed.

Lemma ty_le_tpublic t :
  ty_le tpublic t.
Proof. by case: t. Qed.

Lemma ty_le_tpublicI t :
  ty_le t tpublic
  -> t = tpublic.
Proof. by case: t => [|[]]. Qed.

Lemma ty_le_tsecret t :
  ty_le t tsecret.
Proof. by case: t. Qed.

Lemma ty_le_tsecretI t :
  ty_le tsecret t
  -> t = tsecret.
Proof. by case: t. Qed.

Lemma ty_le_TmaxI s s' :
  ty_le (Tmax s) (Tmax s')
  -> incl s s'.
Proof. done. Qed.

Lemma ty_le_trans : transitive ty_le.
Proof.
  move=> [|?] [|?] // [|?] //= /inclP ? /inclP ?.
  apply/inclP.
  by eauto using List.incl_tran.
Qed.

Lemma ty_le_ty_of_lvl l l' :
  ty_le (ty_of_lvl l) (ty_of_lvl l') = lvl_le l l'.
Proof. case: l; by case: l'. Qed.

Lemma ty_le_lvl_of_ty_ty_of_lvl t :
  ty_le t (lvl_of_ty t |> ty_of_lvl).
Proof. by case: t => // -[]. Qed.

Lemma ty_max_comm t t' :
  ty_eqb (ty_max t t') (ty_max t' t).
Proof.
  case: t t' => [|?] [|?] //=.
  apply/permPl.
  exact: perm_catC.
Qed.

Lemma ty_max_bound t t' :
  ty_le t (ty_max t t') /\ ty_le t' (ty_max t t').
Proof.
  case: t t' => [|?] [|?] //=.
  split; apply/inclP.
  - exact: List.incl_appl.
  exact: List.incl_appr.
Qed.

Definition ty_max_bound_l t t' := proj1 (ty_max_bound t t').
Definition ty_max_bound_r t t' := proj2 (ty_max_bound t t').

Lemma ty_max_least t0 t1 t :
  ty_le t0 t
  -> ty_le t1 t
  -> ty_le (ty_max t0 t1) t.
Proof.
  case: t0 t1 t => [|?] // [|?] //= [|?] // /inclP ? /inclP ?.
  apply/inclP.
  exact: List.incl_app.
Qed.

Lemma ty_max_tpublic t' :
  ty_eqb (ty_max tpublic t') t'.
Proof. case: t' => [//|?]. exact: perm_refl. Qed.

Lemma ty_max_tpublicI t t' :
  ty_max t t' = tpublic
  -> t = tpublic /\ t' = tpublic.
Proof.
  move=> h.
  have [] := ty_max_bound t t'.
  by rewrite h => /ty_le_tpublicI -> /ty_le_tpublicI ->.
Qed.

Lemma ty_max_tsecret_l t :
  ty_max tsecret t = tsecret.
Proof. by case: t. Qed.

Lemma ty_max_tsecret_r t :
  ty_max t tsecret = tsecret.
Proof. by case: t. Qed.

Lemma ty_max_ty_of_lvl l l' :
  ty_max (ty_of_lvl l) (ty_of_lvl l') = ty_of_lvl (lvl_max l l').
Proof. case: l; by case: l'. Qed.

Lemma ty_of_lvl_tpublic l :
  ty_of_lvl l = tpublic
  -> l = Public.
Proof. by case: l. Qed.

Hint Resolve
  ty_le_refl ty_max_tsecret_l ty_max_tsecret_r
  ty_le_ty_of_lvl ty_max_ty_of_lvl
  | 1 : local.
Hint Resolve
  ty_max_bound_l ty_max_bound_r ty_le_tpublic ty_le_tsecret
  | 2 : local.
Hint Resolve ty_le_trans ty_max_least | 3 : local.


Lemma sty_le_refl : reflexive sty_le.
Proof. move=> ?. by rewrite /sty_le ty_le_refl lvl_le_refl. Qed.

Lemma sty_le_spublic t :
  sty_le spublic t.
Proof. by rewrite /sty_le !ty_le_tpublic. Qed.

Lemma sty_le_ssecret t :
  sty_le t ssecret.
Proof. by rewrite /sty_le ty_le_tsecret lvl_le_Secret. Qed.

Lemma sty_le_spublicI t :
  sty_le t spublic
  -> t = spublic.
Proof.
  by move: t => [??] /andP [] /= /ty_le_tpublicI -> /lvl_le_PublicI ->.
Qed.

Lemma sty_le_ssecretI t :
  sty_le ssecret t
  -> t = ssecret.
Proof.
  by move: t => [??] /andP [] /= /ty_le_tsecretI -> /lvl_le_SecretI ->.
Qed.

Lemma sty_le_trans : transitive sty_le.
Proof.
  move=> ??? /andP [??] /andP [??].
  apply/andP.
  by eauto using lvl_le_trans, ty_le_trans.
Qed.

Lemma sty_max_comm t t' :
  sty_eqb (sty_max t t') (sty_max t' t).
Proof. by rewrite /sty_eqb /sty_max /= ty_max_comm lvl_max_comm eqxx. Qed.

Lemma sty_max_bound t t' :
  sty_le t (sty_max t t') /\ sty_le t' (sty_max t t').
Proof.
  rewrite /sty_le /=.
  have [-> ->] := ty_max_bound (sty_n t) (sty_n t').
  by have [-> ->] := lvl_max_bound (sty_s t) (sty_s t').
Qed.

Definition sty_max_bound_l t t' := proj1 (sty_max_bound t t').
Definition sty_max_bound_r t t' := proj2 (sty_max_bound t t').

Lemma sty_max_least t0 t1 t :
  sty_le t0 t
  -> sty_le t1 t
  -> sty_le (sty_max t0 t1) t.
Proof.
  move=> /andP [??] /andP [??].
  by rewrite /sty_le /= ty_max_least // lvl_max_least.
Qed.

Lemma sty_max_spublic t :
  sty_max spublic t = t.
Proof. by move: t => [[|?] ?]. Qed.

Lemma sty_max_spublicE :
  sty_max spublic spublic = spublic.
Proof. done. Qed.

Lemma sty_max_spublicI t t' :
  sty_max t t' = spublic
  -> t = spublic /\ t' = spublic.
Proof.
  by move: t t' => [??] [??]
    [/ty_max_tpublicI [-> ->] /lvl_max_PublicI [-> ->]].
Qed.

Hint Resolve sty_le_refl sty_max_spublic | 1 : local.
Hint Resolve
  sty_max_bound_l sty_max_bound_r sty_le_spublic sty_le_ssecret | 2 : local.
Hint Resolve sty_le_trans sty_max_least | 3 : local.


Lemma ctx_le_refl gamma0 : ctx_le gamma0 gamma0.
Proof. split=> ?; exact: sty_le_refl. Qed.

Lemma ctx_le_trans gamma0 gamma1 gamma2 :
  ctx_le gamma0 gamma1
  -> ctx_le gamma1 gamma2
  -> ctx_le gamma0 gamma2.
Proof.
  move=> h0 h1.
  split=> [?|a]; by eauto using ctx_le_reg, ctx_le_arr, sty_le_trans.
Qed.

Hint Resolve ctx_le_refl | 1 : local.
Hint Resolve ctx_le_trans | 3 : local.


(* -------------------------------------------------------------------------- *)
(* Misspeculation state. *)

Lemma mss_callE sigma sigma_call xi :
  mss_call sigma xi = Some sigma_call
  <-> [\/ [/\ xi = None & sigma_call = MSSunknown ]
       | exists msf,
           [/\ xi = Some msf, sigma = MSSupdated msf & sigma_call = sigma ]
      ].
Proof.
  split.
  - case: xi => [?|] /=.
    + case: sigma => // ?. case: eqP => // -> [<-]. by eeauto.
    move=> [<-]. by auto.
  move=> [[-> ->] //| [? [-> -> ->]]] /=.
  by rewrite eqxx.
Qed.

Lemma mss_callI sigma sigma_call xi :
  mss_call sigma xi = Some sigma_call
  -> if xi is Some msf
     then [/\ sigma = MSSupdated msf & sigma_call = sigma ]
     else sigma_call = MSSunknown.
Proof. by case: xi => [?|] /mss_callE /= [] [] // ? [] // [->] -> ->. Qed.

Lemma mss_le_refl sigma : mss_le sigma sigma.
Proof. case: sigma => [//|?|??]; by econstructor. Qed.

Lemma mss_le_trans sigma0 sigma1 sigma2 :
   mss_le sigma0 sigma1
  -> mss_le sigma1 sigma2
  -> mss_le sigma0 sigma2.
Proof.
  case: sigma0 => [|?|??];
    case: sigma1 => [|?|??];
    by [econstructor | move=> []; congruence].
Qed.

Lemma mss_le_mss_cond_mono sigma0 sigma1 e :
  mss_le sigma0 sigma1
  -> mss_le (mss_cond sigma0 e) (mss_cond sigma1 e).
Proof. case=> ?; subst; by eeauto. Qed.

Lemma mss_le_mss_restrict_mono sigma sigma' x :
  mss_le sigma sigma'
  -> mss_le (mss_restrict sigma x) (mss_restrict sigma' x).
Proof. case=> ?; subst; by eeauto. Qed.

Lemma mss_restrict_le sigma x :
  mss_le (mss_restrict sigma x) sigma.
Proof. rewrite /mss_restrict. case: ifP => _; by eeauto. Qed.

Lemma mss_le_mss_call sigma sigma' xi :
  mss_call sigma xi = Some sigma'
  -> mss_le sigma' sigma.
Proof. move=> /mss_callE [[_ ->] | [? [_ -> ->]]]; by eeauto. Qed.

Lemma mss_le_MSSupdatedI x sigma :
  mss_le (MSSupdated x) sigma
  -> sigma = MSSupdated x.
Proof. by case. Qed.

Hint Resolve mss_le_refl | 1 : local.
Hint Resolve mss_restrict_le mss_le_mss_call | 2 : local.
Hint Resolve mss_le_trans | 3 : local.
Hint Resolve mss_le_mss_cond_mono mss_le_mss_restrict_mono | 4 : local.


(* -------------------------------------------------------------------------- *)
(* Certificate. *)

Lemma wfcertP cert p :
  wfcert cert p
  -> cert_mss (cert (p_entry_fn p)) = MSSunknown.
Proof. rewrite /wfcert. by case: cert_mss. Qed.


(* -------------------------------------------------------------------------- *)
(* Type system. *)

Section WITH_PARAMS.

Context (cert : certificate).

Notation typedi := (typedi cert).
Notation typedc := (typedc cert).

Lemma typedeI gamma e t :
  typede gamma e t
  -> match e with
     | Econst _ | Ebool _ => t = spublic
     | Evar x => t = ctx_reg gamma x
     | Eop1 _ e0 => typede gamma e0 t
     | Eop2 _ e0 e1 =>
       exists t0 t1,
         [/\ typede gamma e0 t0
           , typede gamma e1 t1
           & t = sty_max t0 t1
         ]
     end.
Proof. case=> //; by eeauto. Qed.

Lemma typede_free_variables gamma e t x :
  typede gamma e t
  -> Sr.mem x (free_variables e)
  -> sty_le (ctx_reg gamma x) t.
Proof.
  elim: e t => [// | // | y | op e hind | op e0 hind0 e1 hind1] t /typedeI /=.
  - rewrite Sr.F.singleton_b => -> /Sr.eqP ->. by eeauto.
  - exact: hind.
  move=> [t0 [t1 [hty0 hty1 ?]]]; subst t.
  rewrite Sr.F.union_b => /orP [] h; by eeauto.
Qed.

Lemma ctx_le_typede_Public gamma gamma' e :
  ctx_le gamma gamma'
  -> typede gamma' e spublic
  -> typede gamma e spublic.
Proof.
  move=> h.
  elim: e => [z | b | x | op e hind | op e0 hind0 e1 hind1] /typedeI.
  - by econstructor.
  - by econstructor.
  - move: (ctx_le_reg h x) => /[swap] <- /sty_le_spublicI <-. by constructor.
  - by eeauto.
  move=> [t0 [t1 [ht0 ht1 /esym /sty_max_spublicI [??]]]]; subst t0 t1.
  rewrite -sty_max_spublicE.
  by eeauto.
Qed.

Lemma typediI sigma sigma' gamma gamma' i :
  typedi sigma gamma i sigma' gamma'
  -> match i with
     | Iassign x e =>
         sigma' = mss_restrict sigma x
         /\ exists2 t,
              typede gamma e t
              & gamma' = ctx_update_reg gamma x t

     | Iload x a e =>
         [/\ typede gamma e spublic
           , sigma' = mss_restrict sigma x
           & gamma' = ctx_after_load gamma x a
         ]

     | Istore a e x =>
         [/\ typede gamma e spublic
           , sigma' = sigma
           & is_ctx_after_store gamma gamma' a (ctx_reg gamma x)
         ]

     | Iinit_msf msf =>
         [/\ sigma' = MSSupdated msf
           & gamma' = ctx_after_init_msf gamma msf
         ]

     | Iupdate_msf x y e =>
         [/\ sigma = MSSoutdated y e
           , sigma' = MSSupdated x
           & gamma' = gamma
         ]

     | Iprotect x y msf =>
         [/\ sigma = MSSupdated msf
           , sigma' = mss_restrict sigma x
           & gamma' = ctx_after_protect gamma x y
         ]

     | Iif e c0 c1 =>
         let: sigma_e := mss_cond sigma e in
         let: sigma_ne := mss_cond sigma (enot e) in
         [/\ typede gamma e spublic
           , typedc sigma_e gamma c0 sigma' gamma'
           & typedc sigma_ne gamma c1 sigma' gamma'
         ]

     | Iwhile e c =>
         let: sigma_e := mss_cond sigma e in
         let: sigma_ne := mss_cond sigma (enot e) in
         [/\ typede gamma e spublic
           , typedc sigma_e gamma c sigma gamma
           , sigma' = sigma_ne
           & gamma' = gamma
         ]

     | Icall _ xi f =>
         let: c := cert f in
         let: sigmaf := cert_mss c in
         let: sigmaf' := cert_mss' c in
         [/\ sigma = sigmaf
           , mss_call sigmaf' xi = Some sigma'
           & exists theta,
               let: gammaf := ctx_instantiate theta (cert_ctx c) in
               let: gammaf' := ctx_instantiate theta (cert_ctx' c) in
               [/\ gamma = gammaf
                 & gamma' = gammaf'
               ]
         ]
     end.
Proof. case=> //; by eeauto. Qed.

Lemma typedc_nil sigma sigma' gamma gamma' :
  typedc sigma gamma [::] sigma' gamma'
  -> mss_le sigma' sigma /\ ctx_le gamma gamma'.
Proof.
  remember [::] as c eqn:hc.
  move=> h.
  elim: h hc => // {sigma sigma' gamma gamma' c}.
  - move=> sigma gamma. by eeauto.
  move=> sigma sigma' sigma0 sigma0' gamma gamma' gamma0 gamma0' c hc hind
    hsigma hsigma' hgamma hgamma' ?; subst c.
  move: hind => /(_ erefl) [??].
  by eeauto.
Qed.

Lemma typedc_cons sigma sigma' gamma gamma' i c :
  typedc sigma gamma (i :: c) sigma' gamma'
  -> exists sigma0 gamma0 sigmai gammai sigma0' gamma0',
       [/\ typedi sigma0 gamma0 i sigmai gammai
         , typedc sigmai gammai c sigma0' gamma0'
         , mss_le sigma0 sigma
         , mss_le sigma' sigma0'
         , ctx_le gamma gamma0
         & ctx_le gamma0' gamma'
       ].
Proof.
  remember (_ :: _) as c' eqn:hc.
  move=> h.
  elim: h hc => // {sigma sigma' gamma gamma' c'}.
  - move=> ?????????? _ [??]. subst. by eeauto.
  move=> sigma sigma' sigma0 sigma0' gamma gamma' gamma0 gamma0' c' hc hind
    hsigma hsigma' hgamma hgamma' ?; subst c'.
  move: hind => /(_ erefl) [? [? [? [? [? [? []]]]]]] *.
  by eeauto.
Qed.

Lemma typedcI sigma sigma' gamma gamma' c :
  typedc sigma gamma c sigma' gamma'
  -> match c with
     | [::] => mss_le sigma' sigma /\ ctx_le gamma gamma'
     | i :: c' =>
         exists sigma0 gamma0 sigmai gammai sigma0' gamma0',
           [/\ typedi sigma0 gamma0 i sigmai gammai
             , typedc sigmai gammai c' sigma0' gamma0'
             , mss_le sigma0 sigma
             , mss_le sigma' sigma0'
             , ctx_le gamma gamma0
             & ctx_le gamma0' gamma'
           ]
     end.
Proof. case: c; [exact: typedc_nil | exact: typedc_cons]. Qed.

Lemma typedi_typedc sigma sigma' gamma gamma' i :
  typedi sigma gamma i sigma' gamma'
  -> typedc sigma gamma [:: i ] sigma' gamma'.
Proof. by eeauto. Qed.

Lemma typedc_typedi sigma sigma' gamma gamma' i :
  typedc sigma gamma [:: i ] sigma' gamma'
  -> exists sigma0 sigma0' gamma0 gamma0',
       [/\ typedi sigma0 gamma0 i sigma0' gamma0'
         , mss_le sigma0 sigma
         , mss_le sigma' sigma0'
         , ctx_le gamma gamma0
         & ctx_le gamma0' gamma'
       ].
Proof.
  move=> /typedcI [? [? [? [? [? [? [hi /typedcI [??] ????]]]]]]]. by eeauto.
Qed.

Lemma typed_capp sigma0 sigma1 sigma2 gamma0 gamma1 gamma2 c0 c1 :
  typedc sigma0 gamma0 c0 sigma1 gamma1
  -> typedc sigma1 gamma1 c1 sigma2 gamma2
  -> typedc sigma0 gamma0 (c0 ++ c1) sigma2 gamma2.
Proof.
  elim: c0 sigma0 gamma0 => [|i c hind] sigma0 gamma0 /typedcI.
  - move=> [??]. move=> /typed_weak. by eauto with local.
  move=>
    [sigma [gamma [sigmai [gammai [sigma' [gamma' [hi hc ????]]]]]]] /hind h /=.
  apply: typed_weak.
  - apply: (typed_cons hi). apply: h. by eeauto.
  all: by eeauto.
Qed.

Lemma typed_after_if sigma sigma' sigma'' gamma gamma' gamma'' b e c1 c0 c :
  typedc (mss_cond sigma e) gamma c1 sigma' gamma'
  -> typedc (mss_cond sigma (enot e)) gamma c0 sigma' gamma'
  -> typedc sigma' gamma' c sigma'' gamma''
  -> let: sigma_if := mss_cond sigma (if b then e else enot e) in
     let: c_if := if b then c1 else c0 in
     typedc sigma_if gamma (c_if ++ c) sigma'' gamma''.
Proof. move=> ???. case: b; apply: typed_capp; by eauto. Qed.

End WITH_PARAMS.

(* -------------------------------------------------------------------------- *)

Section EQ_CTX.

Import Morphisms.

Record eq_ctx (gamma gamma' : ctx) :=
  {
    eq_ctx_reg : ctx_reg gamma =1 ctx_reg gamma';
    eq_ctx_arr : ctx_arr gamma =1 ctx_arr gamma';
  }.

#[export]
Instance eq_ctx_Equivalence : Equivalence eq_ctx.
Proof.
  split.
  - move=> x. by split.
  - move=> x y [??]. by split.
  move=> x y z [??] [??]. split; congruence.
Qed.

Definition eq_ctx_Reflexive := Equivalence_Reflexive eq_ctx_Equivalence.
Definition eq_ctx_Symmetric := Equivalence_Symmetric eq_ctx_Equivalence.
Definition eq_ctx_Transitive := Equivalence_Transitive eq_ctx_Equivalence.

Hint Resolve eq_ctx_Reflexive eq_ctx_Symmetric | 1 : local.
Hint Resolve eq_ctx_Transitive | 3 : local.

Lemma ctx_update_reg_id gamma x :
  eq_ctx (ctx_update_reg gamma x (ctx_reg gamma x)) gamma.
Proof. split=> //= ?. by case: eqP => // ->. Qed.

Lemma eq_ctx_ctx_le gamma gamma' :
  eq_ctx gamma gamma'
  -> ctx_le gamma gamma'.
Proof. move=> [hreg harr]. split=> [x|a]; rewrite ?hreg ?harr; by eeauto. Qed.

#[local]
Lemma eq_ctx_typede : Proper (eq_ctx ==> eq ==> eq ==> Basics.impl) typede.
  rewrite /Basics.impl.
  move=> gamma gamma' [hreg _] e _ <- t _ <-.
  elim: e t => [z | b | x | op e hind | op e0 hind0 e1 hind1] t /typedeI.
  - move=> ->. by constructor.
  - move=> ->. by constructor.
  - move=> ->. rewrite hreg. by constructor.
  - by eeauto.
  move=> [? [? [???]]]; subst t.
  by eeauto.
Qed.

#[export]
Instance eq_ctx_typede_Proper :
  Morphisms.Proper (eq_ctx ==> eq ==> eq ==> iff) typede.
Proof.
  move=> gamma gamma' h e _ <- t _ <-.
  split; apply: eq_ctx_typede => //.
  by symmetry.
Qed.

#[export]
Instance eq_ctx_ctx_update_reg_Proper :
  Proper (eq_ctx ==> eq ==> eq ==> eq_ctx) ctx_update_reg.
Proof.
  move=> gamma gamma' hgamma x _ <- t _ <-.
  split=> ? /=; last by rewrite (eq_ctx_arr hgamma).
  by rewrite (eq_ctx_reg hgamma).
Qed.

#[export]
Instance eq_ctx_ctx_reg_Proper :
  Proper (eq_ctx ==> eq ==> eq) ctx_reg.
Proof. move=> gamma gamma' hgamma x _ <-. by rewrite (eq_ctx_reg hgamma). Qed.

#[export]
Instance eq_ctx_ctx_arr_Proper :
  Proper (eq_ctx ==> eq ==> eq) ctx_arr.
Proof. move=> gamma gamma' hgamma a _ <-. by rewrite (eq_ctx_arr hgamma). Qed.

#[local]
Lemma eq_ctx_eq_ctx_ctx_le :
  Proper (eq_ctx ==> eq_ctx ==> Basics.impl) ctx_le.
Proof. move=> ?? h0 ?? h1 [??]. split=> ? /=; by rewrite -h0 -h1. Qed.

#[export]
Instance eq_ctx_eq_ctx_ctx_le_Proper :
  Proper (eq_ctx ==> eq_ctx ==> iff) ctx_le.
Proof.
  move=> ?? h0 ?? h1. split=> /eq_ctx_eq_ctx_ctx_le; apply=> //; by symmetry.
Qed.

#[local]
Lemma eq_ctx_typedc cert :
  Proper (eq ==> eq_ctx ==> eq ==> eq ==> eq_ctx ==> Basics.impl) (typedc cert).
Proof.
  move=> ? _ <- gamma gamma' hgamma c _ <- ? _ <- gamma0 gamma0' hgamma0 h.
  apply: typed_weak; first eassumption.
  - by eeauto.
  - by eeauto.
  - apply: eq_ctx_ctx_le. by symmetry.
  exact: eq_ctx_ctx_le.
Qed.

#[export]
Instance eq_ctx_typedc_Proper cert :
  Proper (eq ==> eq_ctx ==> eq ==> eq ==> eq_ctx ==> iff) (typedc cert).
Proof.
  move=> ? _ <- ?? hgamma ? _ <- ? _ <- ?? hgamma'.
  split; apply: eq_ctx_typedc => //; by symmetry.
Qed.

End EQ_CTX.

Definition theta_Secret : instantiation := fun _ => Secret.

Lemma ty_instantiate_ty_of_lvl theta l :
  ty_instantiate theta (ty_of_lvl l) = ty_of_lvl l.
Proof. by case: l. Qed.

Lemma instantiate_lvl_max theta l s :
  List.fold_right (fun y => lvl_max (theta y)) l s
  = lvl_max l (instantiate theta s).
Proof.
  elim: s => [|x s hind] /=.
  - by rewrite lvl_max_Public.
  by rewrite hind !lvl_max_assoc (lvl_max_comm l).
Qed.

Lemma instantiate_bound theta s x :
  x \in s
  -> lvl_le (theta x) (instantiate theta s).
Proof.
  elim: s => [//|y s hind].
  rewrite in_cons => /orP [].
  - move=> /eqP ?; subst x. by rewrite /= lvl_max_bound_l.
  by move=> /hind /= /lvl_le_trans /(_ (lvl_max_bound_r _ _)).
Qed.

Lemma instantiate_cat theta s s' :
  instantiate theta (s ++ s') =
    lvl_max (instantiate theta s) (instantiate theta s').
Proof.
  by rewrite {1}/instantiate List.fold_right_app instantiate_lvl_max
    lvl_max_comm.
Qed.

Lemma instantiate_incl theta s s' :
  incl s s'
  -> lvl_le (instantiate theta s) (instantiate theta s').
Proof.
  elim: s => [//|x s hind] /inclP h.
  move: (List.incl_cons_inv h) => [] /inP /instantiate_bound ? /inclP /hind
    ?.
  exact: lvl_max_least.
Qed.

Lemma instantiate_theta_SecretP s :
  s = [::] \/ instantiate theta_Secret s = Secret.
Proof.
  case: s => [|x s]; first by left.
  right.
  by rewrite /= lvl_max_Secret.
Qed.

Lemma ty_instantiate_theta_Secret t :
  ty_le t (ty_instantiate theta_Secret t).
Proof.
  case: t => [//|s] /=.
  have := instantiate_theta_SecretP s.
  by case: instantiate => -[] //= ->.
Qed.

Lemma sty_instantiate_theta_Secret t :
  sty_le t (sty_instantiate theta_Secret t).
Proof.
  move: t => [??].
  by rewrite /sty_le /= ty_instantiate_theta_Secret lvl_le_refl.
Qed.

Lemma ctx_instantiate_theta_Secret gamma :
  ctx_le gamma (ctx_instantiate theta_Secret gamma).
Proof. split=> ?; by rewrite /= sty_instantiate_theta_Secret. Qed.

Lemma ty_instantiate_compose theta theta' t :
  ty_instantiate theta' (ty_instantiate theta t) = ty_instantiate theta t.
Proof. case: t => [//|s] /=. exact: ty_instantiate_ty_of_lvl. Qed.

Lemma sty_instantiate_compose theta theta' t :
  sty_instantiate theta' (sty_instantiate theta t) = sty_instantiate theta t.
Proof. by rewrite /sty_instantiate ty_instantiate_compose. Qed.

Lemma ctx_instantiate_compose theta theta' gamma :
  eq_ctx
    (ctx_instantiate theta' (ctx_instantiate theta gamma))
    (ctx_instantiate theta gamma).
Proof. split=> ?; by rewrite /= sty_instantiate_compose. Qed.

Lemma ty_instantiate_ty_max theta t0 t1 :
  let: t0' := ty_instantiate theta t0 in
  let: t1' := ty_instantiate theta t1 in
  let: tmax' := ty_instantiate theta (ty_max t0 t1) in
  tmax' = ty_max t0' t1'.
Proof.
  case: t0 => [//|?] /=.
  case: t1 => [|?] /=. by rewrite ty_max_tsecret_r.
  by rewrite instantiate_cat ty_max_ty_of_lvl.
Qed.

Lemma sty_instantiate_sty_max theta t0 t1 :
  let: t0' := sty_instantiate theta t0 in
  let: t1' := sty_instantiate theta t1 in
  let: tmax' := sty_instantiate theta (sty_max t0 t1) in
  tmax' = sty_max t0' t1'.
Proof. by rewrite /sty_max /= -ty_instantiate_ty_max. Qed.

Lemma ctx_instantiate_typede theta gamma e t :
  let: gamma0 := ctx_instantiate theta gamma in
  typede gamma e t
  -> typede gamma0 e (sty_instantiate theta t).
Proof.
  elim: e t => [z | b | x | op e hind | op e0 hind0 e1 hind1] t /typedeI.
  - move=> ->. by eeauto.
  - move=> ->. by eeauto.
  - move=> ->. by eeauto.
  - by eeauto.
  move=> [t0 [t1 [ht0 ht1 ?]]]; subst t.
  rewrite sty_instantiate_sty_max.
  by eeauto.
Qed.

Lemma ctx_instantiate_ctx_update_reg theta gamma x t :
  let: gamma' := ctx_instantiate theta (ctx_update_reg gamma x t) in
  let: t' := sty_instantiate theta t in
  eq_ctx gamma' (ctx_update_reg (ctx_instantiate theta gamma) x t').
Proof. split=> [? | //]; by rewrite /= (fun_if (sty_instantiate _)). Qed.

Lemma ty_le_ty_instantiate theta ty ty' :
  ty_le ty ty'
  -> ty_le (ty_instantiate theta ty) (ty_instantiate theta ty').
Proof.
  case: ty ty' => [|?] [|?] //= h; first exact: ty_le_tsecret.
  rewrite ty_le_ty_of_lvl.
  exact: instantiate_incl.
Qed.

Lemma sty_le_sty_instantiate theta t t' :
  sty_le t t'
  -> sty_le (sty_instantiate theta t) (sty_instantiate theta t').
Proof. move=> /andP [??]. by rewrite /sty_le !ty_le_ty_instantiate. Qed.

Lemma ctx_le_ctx_instantiate theta gamma gamma' :
  let: gamma0 := ctx_instantiate theta gamma in
  let: gamma0' := ctx_instantiate theta gamma' in
  ctx_le gamma gamma'
  -> ctx_le gamma0 gamma0'.
Proof. move=> [??]. split=> ?; exact: sty_le_sty_instantiate. Qed.

Lemma ctx_after_init_msfP gamma msf :
  let: gamma' := ctx_after_init_msf gamma msf in
  [/\ ctx_reg gamma' msf = spublic
    , forall x,
        let: t_n := sty_n (ctx_reg gamma x) in
        let: t_s := lvl_of_ty t_n in
        x != msf
        -> sty_n (ctx_reg gamma' x) = t_n /\ sty_s (ctx_reg gamma' x) = t_s
    & forall a,
        let: t_n := sty_n (ctx_arr gamma a) in
        let: t_s := lvl_of_ty t_n in
        sty_n (ctx_arr gamma' a) = t_n /\ sty_s (ctx_arr gamma' a) = t_s
  ].
Proof.
  split=> [|?|//] /=; first by rewrite eqxx.
  move=> /negPf h.
  by rewrite eq_sym h.
Qed.

Lemma ty_le_ty_instantiate_lvl_of_ty theta t :
  lvl_le
    (lvl_of_ty (ty_instantiate theta t))
    (lvl_of_ty t).
Proof. case: t => [// | [// | ??]]. by eeauto. Qed.

Lemma sty_le_sty_instantiate_sty_after_init_msf theta t :
  sty_le
    (sty_after_init_msf (sty_instantiate theta t))
    (sty_instantiate theta (sty_after_init_msf t)).
Proof. by rewrite /sty_le /= ty_le_refl ty_le_ty_instantiate_lvl_of_ty. Qed.

Lemma ctx_le_ctx_instantiate_ctx_after_init theta gamma msf :
  ctx_le
    (ctx_after_init_msf (ctx_instantiate theta gamma) msf)
    (ctx_instantiate theta (ctx_after_init_msf gamma msf)).
Proof.
  split=> ? /=.
  - case: eqP => [// | _].
  all: exact: sty_le_sty_instantiate_sty_after_init_msf.
Qed.

Lemma ctx_le_ctx_instantiate_ctx_after_protect theta gamma x y :
  let: t := ctx_reg gamma y in
  let: t' := sty_after_init_msf t in
  ctx_le
    (ctx_after_protect (ctx_instantiate theta gamma) x y)
    (ctx_update_reg (ctx_instantiate theta gamma) x (sty_instantiate theta t')).
Proof.
  split=> ? /=; last exact: sty_le_refl.
  case: eqP => _; last exact: sty_le_refl.
  exact: sty_le_sty_instantiate_sty_after_init_msf.
Qed.


Module __TypedInstantiation.

Section PROOF.

Context
  (cert : certificate)
  (theta : instantiation)
.

Notation typedi := (typedi cert).
Notation typedc := (typedc cert).

Let Pi i :=
  forall sigma sigma' gamma gamma',
    let: gamma0 := ctx_instantiate theta gamma in
    let: gamma0' := ctx_instantiate theta gamma' in
    typedi sigma gamma i sigma' gamma'
    -> typedc sigma gamma0 [:: i ] sigma' gamma0'.

Let Pc c :=
  forall sigma sigma' gamma gamma',
    let: gamma0 := ctx_instantiate theta gamma in
    let: gamma0' := ctx_instantiate theta gamma' in
    typedc sigma gamma c sigma' gamma'
    -> typedc sigma gamma0 c sigma' gamma0'.

#[local]
Lemma hassign x e : Pi (Iassign x e).
Proof.
  move=> > /typediI [-> [t /ctx_instantiate_typede ? ->]].
  rewrite ctx_instantiate_ctx_update_reg.
  by eeauto.
Qed.

#[local]
Lemma hload x a e : Pi (Iload x a e).
Proof.
  move=> > /typediI [/ctx_instantiate_typede ? -> ->].
  rewrite ctx_instantiate_ctx_update_reg.
  by eeauto.
Qed.

#[local]
Lemma hstore a e x : Pi (Istore a e x).
Proof.
  move=> > /typediI [/ctx_instantiate_typede he -> [hle ha ha']].
  apply: typedi_typedc.
  econstructor; first exact: he.
  split=> //; last exact: sty_le_sty_instantiate.
  exact: ctx_le_ctx_instantiate.
Qed.

#[local]
Lemma hinit_msf msf : Pi (Iinit_msf msf).
Proof.
  move=> > /typediI [-> ->].
  have ? := ctx_le_ctx_instantiate_ctx_after_init.
  by eeauto.
Qed.

#[local]
Lemma hupdate_msf x y e : Pi (Iupdate_msf x y e).
Proof. move=> > /typediI [???]; subst. by eeauto. Qed.

#[local]
Lemma hprotect x y msf : Pi (Iprotect x y msf).
Proof.
  move=> > /typediI [???]; subst.
  rewrite ctx_instantiate_ctx_update_reg.
  have ? := ctx_le_ctx_instantiate_ctx_after_protect.
  by eeauto.
Qed.

#[local]
Lemma hif e c0 c1 : Pc c0 -> Pc c1 -> Pi (Iif e c0 c1).
Proof. move=> h0 h1 > /typediI [/ctx_instantiate_typede ???]. by eeauto. Qed.

#[local]
Lemma hwhile e c : Pc c -> Pi (Iwhile e c).
Proof.
  move=> h > /typediI [/ctx_instantiate_typede ????]; subst. by eeauto.
Qed.

#[local]
Lemma hcall l xi f : Pi (Icall l xi f).
Proof.
  move=> > /typediI [?? [? [??]]]; subst.
  rewrite !ctx_instantiate_compose.
  by eeauto.
Qed.

#[local]
Lemma hnil : Pc [::].
Proof. move=> > /typedcI [? /ctx_le_ctx_instantiate ?]. by eeauto. Qed.

#[local]
Lemma hcons i c : Pi i -> Pc c -> Pc (i :: c).
Proof.
  move=> hi hc > /typedcI [? [? [? [? [? [? []]]]]]]
    /hi /typedc_typedi [? [? [? [? [?????]]]]]
    /hc ?????.
  have ? := ctx_le_ctx_instantiate.
  apply: typed_weak; by eeauto.
Qed.

Lemma main c : Pc c.
Proof.
  apply: (code_rect _ _ (Pi := Pi) (Pc := Pc)) => // {c} *;
    by eauto using
      hassign,
      hload,
      hstore,
      hinit_msf,
      hupdate_msf,
      hprotect,
      hif,
      hwhile,
      hcall,
      hnil,
      hcons.
Qed.

End PROOF.

End __TypedInstantiation.

Definition ctx_instantiate_typedc := __TypedInstantiation.main.

Module __TypedContinuation.

Section PROOF.

Context
  (f : funname)
  (cert : certificate)
.

Notation typedi := (typedi cert).
Notation typedc := (typedc cert).

Notation sigmaf' := (cert f |> cert_mss').
Notation gammaf' := (cert f |> cert_ctx').

Let Pi i :=
  forall sigma sigma' gamma gamma' l xi cont,
    typedi sigma gamma i sigma' gamma'
    -> List.In (l, xi, cont) (conti f i)
    -> exists theta sigma_call,
         let: theta_gammaf' := ctx_instantiate theta gammaf' in
         [/\ mss_call sigmaf' xi = Some sigma_call
           & typedc sigma_call theta_gammaf' cont sigma' gamma'
         ].

Let Pc c :=
  forall sigma sigma' gamma gamma' l xi cont,
    typedc sigma gamma c sigma' gamma'
    -> List.In (l, xi, cont) (contc f c)
    -> exists theta sigma_call,
         let: theta_gammaf' := ctx_instantiate theta gammaf' in
         [/\ mss_call sigmaf' xi = Some sigma_call
           & typedc sigma_call theta_gammaf' cont sigma' gamma'
         ].

#[local]
Lemma hassign x e : Pi (Iassign x e).
Proof. done. Qed.

#[local]
Lemma hload x a e : Pi (Iload x a e).
Proof. done. Qed.

#[local]
Lemma hstore a e x : Pi (Istore a e x).
Proof. done. Qed.

#[local]
Lemma hinit_msf msf : Pi (Iinit_msf msf).
Proof. done. Qed.

#[local]
Lemma hupdate_msf x y e : Pi (Iupdate_msf x y e).
Proof. done. Qed.

#[local]
Lemma hprotect x y msf : Pi (Iprotect x y msf).
Proof. done. Qed.

#[local]
Lemma hif e c0 c1 : Pc c0 -> Pc c1 -> Pi (Iif e c0 c1).
Proof.
  move=> ?? > /typediI [_ ??]; rewrite conti_if => hin.
  case: (List.in_app_or _ _ _ hin); by eeauto.
Qed.

#[local]
Lemma hwhile e c : Pc c -> Pi (Iwhile e c).
Proof.
  move=> hc sigma sigma' gamma gamma' l xi cont /typediI [htye htyc ??] /inP;
    subst.
  rewrite conti_while => /mapP [] /= [] [] l' xi' cont' /inP hin [???]; subst l' xi' cont.
  have [theta [sigma_call [hsigma_call hcont']]] := hc _ _ _ _ _ _ _ htyc hin.
  eexists; eexists; split; first eassumption.
  apply: typed_capp; first exact: hcont'.
  by eeauto.
Qed.

#[local]
Lemma hcall l xi g : Pi (Icall l xi g).
Proof.
  move=> sigma sigma' gamma gamma' l' xi' cont /typediI [?? [theta [??]]] /=;
    subst.
  rewrite conti_call.
  case: eqP => [?|//].
  move=> [[???] | //]; subst.
  by eeauto.
Qed.

#[local]
Lemma hnil : Pc [::].
Proof. done. Qed.

#[local]
Lemma hcons i c : Pi i -> Pc c -> Pc (i :: c).
Proof.
  move=> hi hc > /typedcI [? [? [? [? [? [? [htyi htyc ????]]]]]]].
  rewrite contc_cons => hin.
  case: (List.in_app_or _ _ _ hin); rewrite -/conti -/contc.
  - move=> h.
    have [[[l' xi'] cont'] [[???] hcont']] := map_in h; subst.
    have [? [? [??]]] := hi _ _ _ _ _ _ _ htyi hcont'.
    eexists; eexists; split; first eassumption.
    apply: typed_capp; by eeauto.
  move=> /hc. apply. apply: typed_weak; by eeauto.
Qed.

Lemma main c : Pc c.
Proof.
  apply: (code_rect (Pi := Pi) (Pc := Pc)) => {c} *;
    by eauto using
      hassign,
      hload,
      hstore,
      hinit_msf,
      hupdate_msf,
      hprotect,
      hif,
      hwhile,
      hcall,
      hnil,
      hcons.
Qed.

End PROOF.

End __TypedContinuation.

Definition typedc_contc := __TypedContinuation.main.

(* -------------------------------------------------------------------------- *)
(* Final MSS of functions. *)

Section FINAL_MSS.

Context
  (cert : certificate)
  (p : program)
  (htyp : typedp cert p)
.

Let Pi i :=
  forall sigma gamma sigma' gamma' f l xi cont,
    typedi cert sigma gamma i sigma' gamma' ->
    List.In (l, xi, cont) (conti f i) ->
    isSome (mss_call (cert_mss' (cert f)) xi).

Let Pc c :=
  forall sigma gamma sigma' gamma' f l xi cont,
    typedc cert sigma gamma c sigma' gamma' ->
    List.In (l, xi, cont) (contc f c) ->
    isSome (mss_call (cert_mss' (cert f)) xi).

Lemma final_mss_updated_c c : Pc c.
Proof.
  apply: (code_rect (Pi := Pi) (Pc := Pc)) =>
    [?? | ??? | ??? | ? | ??? | ???
    | e c1 h1 c0 h0
    | e c1 h1
    | l xi g
    |
    | i hi c' hc']
    sigma gamma sigma' gamma' f l' xi' cont //=.
  - move=> /typediI [_ ??]; rewrite conti_if => /List.in_app_iff []; by eauto.
  - move=> /typediI [_ ? _ _]; rewrite conti_while => /inP/mapP [] /= [] [] l0 xi0 c' /inP hin [???].
    by subst l0 xi0 cont; eauto.
  - move=> /typediI [? h [? [??]]]; rewrite conti_call.
    case: eqP => [-> | //] [] [] _ <- ?.
    by rewrite h.
  move=> /typedcI [? [? [? [? [? [? [??????]]]]]]]; rewrite contc_cons => /List.in_app_iff [];
    last by eauto.
  move=> /map_in [[[l0 xi0] c0] [[??] hc0]]; subst l0 xi0 cont.
  by eauto.
Qed.

Lemma final_mss_updated callee caller l xi cont :
  List.In (caller, l, xi, cont) (contp callee p) ->
  isSome (mss_call (cert_mss' (cert callee)) xi).
Proof.
  move=> /in_contpI.
  by move: (htyp caller) => /final_mss_updated_c /[apply].
Qed.

End FINAL_MSS.
