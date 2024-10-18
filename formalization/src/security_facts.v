From Coq Require Import ZArith.
From Coq Require Morphisms.
From mathcomp Require Import all_ssreflect.

Require Import
  security
  semantics
  semantics_facts
  syntax
  syntax_facts
  typesystem
  typesystem_facts
  utils
  utils_facts
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.


(* -------------------------------------------------------------------------- *)
(* Valid machines. *)

Section VALID.

Context (cert : certificate).

Notation typedi := (typedi cert).
Notation typedc := (typedc cert).

(* We need to know that the MSF is in range because after an update_msf, if
   we are not misspeculating, we know
       [Vm.get vm1 msf != msf_mask]
       [Vm.get vm2 msf != msf_mask]
   but we need to prove
       [eq_val (Vm.get vm1 msf) (Vm.get vm2 msf)]
   This is true because [eq_vm gamma vm1 vm2] and [gamma msf = Public], but to
   prove this we need to keep the invariant that [msf] is always public.
   Having this in [synced] is less effort (we would need a new invariant on
   [sigma], [gamma] and [vm]. *)
Definition msf_in_range (vm : Vm.t) (x : regvar) : bool :=
  [|| Vm.get vm x == msf_mask | Vm.get vm x == msf_nomask ].

Definition synced (sigma : mss) (vm : Vm.t) (ms : bool) : bool :=
  match sigma with
  | MSSunknown => true
  | MSSupdated x => [&& ms == (Vm.get vm x == msf_mask) & msf_in_range vm x ]
  | MSSoutdated x e =>
      [&& if ms
          then [|| eval vm e == Vbool false | Vm.get vm x == msf_mask ]
          else [&& eval vm e == Vbool true & Vm.get vm x != msf_mask ]
        & msf_in_range vm x
      ]
  end.

(* We need this part of the invariant because even thought we know that if we
   return, we go to a continuation (it's a hypothesis for speculative returns
   and provable as an invariant for sequential ones), in sequential execution we
   need not only that there exists an instantiation such that the continuation
   is typable, which is what [typedc_contc] says, but that this instantiation is
   exactly the one we used at the callsite. *)
Inductive typed_callstack : mss -> ctx -> callstack -> Prop :=
  | typed_callstack_nil :
      forall sigma gamma,
        typed_callstack sigma gamma [::]

  | typed_callstack_cons :
      forall f l c cs sigma gamma theta,
        let: sigmaf' := cert_mss' (cert f) in
        let: gammaf' := cert_ctx' (cert f) |> ctx_instantiate theta in
        typedc sigma gamma c sigmaf' gammaf'
        -> typed_callstack sigmaf' gammaf' cs
        -> typed_callstack sigma gamma ((f, l, c) :: cs)
.

Definition typedm (sigma : mss) (gamma : ctx) (m : machine) : Prop :=
  exists theta,
    let: c := cert (m_fn m) in
    let: sigmaf' := cert_mss' c in
    let: gammaf' := ctx_instantiate theta (cert_ctx' c) in
    typedc sigma gamma (m_c m) sigmaf' gammaf'
    /\ typed_callstack sigmaf' gammaf' (m_cs m).

End VALID.

Section UTILS.

Context
  (cert : certificate)
  (p : program)
.

Notation typedi := (typedi cert).
Notation typedc := (typedc cert).
Notation step := (step p).
Notation typedm := (typedm cert).
Notation typed_callstack := (typed_callstack cert).

Lemma eq_val_refl t v :
  eq_val t v v.
Proof. by rewrite /eq_val eqxx orbT. Qed.

Lemma weak_eq_val t t' v v' :
  eq_val t v v'
  -> ty_le t t'
  -> eq_val t' v v'.
Proof.
  move=> /orP [].
  - move=> /ty_eqb_tpublic ht hle.
    apply: orb_implP => /ty_eqb_tpublic ?; subst t'.
    move: hle => /ty_le_tpublicI ?.
    by subst t.
  move=> /eqP -> _.
  exact: eq_val_refl.
Qed.

Lemma weak_eq_map X (get get' : X -> vtype) m0 m1 :
  eq_map get m0 m1
  -> (forall x, ty_le (get x) (get' x))
  -> eq_map get' m0 m1.
Proof. move=> ???; eauto using weak_eq_val. Qed.

Lemma weak_eq_vm is_n gamma gamma' vm0 vm1 :
  eq_vm is_n gamma vm0 vm1
  -> ctx_le gamma gamma'
  -> eq_vm is_n gamma' vm0 vm1.
Proof.
  move=> /weak_eq_map h hle.
  apply: h => x.
  case: is_n (ctx_le_reg hle x) => /andP [] //=.
  by eeauto.
Qed.

Lemma weak_eq_mem is_n gamma gamma' m0 m1 :
  eq_mem is_n gamma m0 m1
  -> ctx_le gamma gamma'
  -> eq_mem is_n gamma' m0 m1.
Proof.
  move=> /weak_eq_map h hle.
  apply: h => -[a i].
  case: is_n (ctx_le_arr hle a) => /andP [] //=.
  by eeauto.
Qed.

Lemma weak_eq_st_on_ms is_n gamma gamma' st1 st2 b b' :
  let: st1' := with_ms st1 (b || st_ms st1) in
  let: st2' := with_ms st2 (b' || st_ms st2) in
  eq_st_on is_n gamma st1 st2
  -> ctx_le gamma gamma'
  -> eq_st_on is_n gamma' st1' st2'.
Proof.
  move=> [hvm hmem] hle.
  case: b;
    case: b';
    rewrite ?with_ms_id;
    split;
    by eauto using weak_eq_vm, weak_eq_mem.
Qed.

Lemma eq_st_set_ms gamma st st' :
  eq_st_on_s gamma st st'
  -> eq_st gamma (set_ms st) (set_ms st').
Proof. by move=> [hvm hmem]; split=> //; left. Qed.

Lemma eq_st_with_ms gamma st1 st2 b :
  eq_st gamma st1 st2 ->
  eq_st gamma (with_ms st1 (b || st_ms st1)) (with_ms st2 (b || st_ms st2)).
Proof.
  case b => //=; case: st1 st2 => vm1 m1 ms1 [vm2 m2 ms2] h //=.
  by case: h => [/= h1 ?] <-; have /= := eq_st_set_ms h1; apply.
Qed.

Lemma weak_eq_st_on is_n gamma gamma' st st' :
  eq_st_on is_n gamma st st'
  -> ctx_le gamma gamma'
  -> eq_st_on is_n gamma' st st'.
Proof.
  move=> /(weak_eq_st_on_ms false false) /[apply]. by rewrite /= !with_ms_id.
Qed.

Lemma weak_eq_st gamma gamma' st st' :
  eq_st gamma st st'
  -> ctx_le gamma gamma'
  -> eq_st gamma' st st'.
Proof.
  move=> [hspec hseq hms] hle.
  split=> //.
  - apply: weak_eq_st_on; by eauto.
  case: hseq; first by auto.
  move=> /weak_eq_st_on h.
  right.
  exact: h.
Qed.


Section EQ_CTX_EQ_ST.

Import Morphisms.

#[local]
Lemma eq_ctx_eq_vm :
  Proper (eq ==> eq_ctx ==> eq ==> eq ==> Basics.impl) eq_vm.
Proof. move=> ? _ <- ?? [h _] ? _ <- ? _ <- ??. congruence. Qed.

#[export]
Instance eq_ctx_eq_vm_Proper :
  Proper (eq ==> eq_ctx ==> eq ==> eq ==> iff) eq_vm.
Proof. split; apply: eq_ctx_eq_vm => //; by symmetry. Qed.

#[local]
Lemma eq_ctx_eq_mem :
  Proper (eq ==> eq_ctx ==> eq ==> eq ==> Basics.impl) eq_mem.
Proof.
  move=> ? _ <- ?? [_ hgamma] ? _ <- ? _ <- hmem [??].
  rewrite -hgamma.
  exact: (hmem (_, _)).
Qed.

#[export]
Instance eq_ctx_eq_mem_Proper :
  Proper (eq ==> eq_ctx ==> eq ==> eq ==> iff) eq_mem.
Proof. split; apply: eq_ctx_eq_mem => //; by symmetry. Qed.

#[local]
Lemma eq_ctx_eq_st_on :
  Proper (eq ==> eq_ctx ==> eq ==> eq ==> Basics.impl) eq_st_on.
Proof.
  move=> is_n _ <- ?? hgamma ? _ <- ? _ <- [hvm hmem].
  split; by rewrite -hgamma.
Qed.

#[export]
Instance eq_ctx_eq_st_on_Proper :
  Proper (eq ==> eq_ctx ==> eq ==> eq ==> iff) eq_st_on.
Proof. split; apply: eq_ctx_eq_st_on => //; by symmetry. Qed.

#[local]
Lemma eq_ctx_eq_st :
  Proper (eq_ctx ==> eq ==> eq ==> Basics.impl) eq_st.
Proof.
  move=> ?? hgamma ? _ <- ? _ <- [hspec hseq hms].
  split=> //.
  - exact: (eq_ctx_eq_st_on erefl hgamma erefl erefl).
  case: hseq => hseq; first by left.
  right.
  exact: (eq_ctx_eq_st_on erefl hgamma erefl erefl).
Qed.

#[export]
Instance eq_ctx_eq_st_Proper :
  Proper (eq_ctx ==> eq ==> eq ==> iff) eq_st.
Proof. split; apply: eq_ctx_eq_st => //; by symmetry. Qed.

End EQ_CTX_EQ_ST.

Lemma eq_vm_eval_e_public is_n gamma vm vm' e t :
  eq_vm is_n gamma vm vm'
  -> typede gamma e t
  -> ty_eqb (proj_is_n is_n t) tpublic
  -> eval vm e = eval vm' e.
Proof.
  move=> hvm hty ht.
  apply: eval_eq_on => x /(typede_free_variables hty) {hty}.
  move=> /andP [].
  case: is_n ht hvm (hvm x) => /ty_eqb_tpublic /=.
  - move=> -> _ hx /ty_le_tpublicI h _. move: hx. by rewrite h => /eqP.
  move=> /ty_of_lvl_tpublic -> _ hx _ /lvl_le_PublicI h.
  move: hx.
  by rewrite h => /eqP.
Qed.

Lemma eq_vm_vm_set is_n gamma vm vm' x v v' t :
  let: gamma' := ctx_update_reg gamma x t in
  eq_vm is_n gamma vm vm'
  -> eq_val (proj_is_n is_n t) v v'
  -> eq_vm is_n gamma' (Vm.set vm x v) (Vm.set vm' x v').
Proof.
  move=> h hv y.
  rewrite /= !Vm.get_set.
  by case: eqP.
Qed.

Lemma eq_mem_mem_write is_n gamma gamma' m m' a i v v' t :
  let: proj := proj_is_n is_n in
  eq_mem is_n gamma m m'
  -> ctx_le gamma gamma'
  -> ty_le (proj t) (ctx_arr gamma' a |> proj)
  -> in_bounds a i
  -> eq_val (proj t) v v'
  -> eq_mem is_n gamma' (Mem.write m a i v) (Mem.write m' a i v').
Proof.
  move=> h hle ht hi hv [b j].
  rewrite /= !Mem.read_write // {hi}.
  case: andP => [[/eqP <- _] | _]; first by eauto using weak_eq_val.
  apply: weak_eq_val; first exact: (h (_, _)).
  move: (ctx_le_arr hle b) => /andP [].
  case: is_n h ht hv => //.
  by eeauto.
Qed.

Lemma eq_vm_vm_set_eq is_n gamma vm vm' x v :
  eq_vm is_n gamma vm vm'
  -> eq_vm is_n gamma (Vm.set vm x v) (Vm.set vm' x v).
Proof.
  move=> h.
  rewrite -(ctx_update_reg_id gamma x).
  apply: eq_vm_vm_set => //; by rewrite eq_val_refl ?orbT.
Qed.

Lemma eq_st_on_write_reg is_n gamma st1 st2 x v v' t :
  let: gamma' := ctx_update_reg gamma x t in
  eq_st_on is_n gamma st1 st2
  -> eq_val (proj_is_n is_n t) v v'
  -> eq_st_on is_n gamma' (write_reg st1 x v) (write_reg st2 x v').
Proof.
  move=> [hvm hmem].
  split=> //.
  exact: eq_vm_vm_set.
Qed.

Lemma eq_st_on_write_mem is_n gamma gamma' st1 st2 a i v v' t :
  let: proj := proj_is_n is_n in
  eq_st_on is_n gamma st1 st2
  -> ctx_le gamma gamma'
  -> ty_le (proj t) (ctx_arr gamma' a |> proj)
  -> in_bounds a i
  -> eq_val (proj t) v v'
  -> eq_st_on is_n gamma' (write_mem st1 a i v) (write_mem st2 a i v').
Proof.
  move=> [hvm hmem] hgamma hi hv.
  split; first by eauto using weak_eq_vm.
  apply: eq_mem_mem_write; by eauto.
Qed.

Lemma eq_st_write_reg gamma st1 st2 x v v' t :
  let: gamma' := ctx_update_reg gamma x t in
  eq_st gamma st1 st2
  -> eq_val (ty_of_lvl (sty_s t)) v v'
  -> (st_ms st1 || eq_val (sty_n t) v v')
  -> eq_st gamma' (write_reg st1 x v) (write_reg st2 x v').
Proof.
  move=> [hspec hseq hms] hspecv hseqv.
  split=> //; first exact: eq_st_on_write_reg.
  case: hseq => hseq; first by left.
  move: hseqv => /orP [] hseqv; first by left.
  right.
  exact: eq_st_on_write_reg.
Qed.

Lemma eq_st_write_mem gamma gamma' st1 st2 a i v v' t :
  eq_st gamma st1 st2
  -> ctx_le gamma gamma'
  -> sty_le t (ctx_arr gamma' a)
  -> in_bounds a i
  -> eq_val (ty_of_lvl (sty_s t)) v v'
  -> (st_ms st1 || eq_val (sty_n t) v v')
  -> eq_st gamma' (write_mem st1 a i v) (write_mem st2 a i v').
Proof.
  move=> [hspec hseq hms] hle /andP [htn hts] hi hspecv hseqv.
  split=> //.
  - apply: eq_st_on_write_mem; by eauto using ty_le_ty_of_lvl.
  case: hseq => hseq; first by left.
  move: hseqv => /orP [] hseqt; first by left.
  right; apply: eq_st_on_write_mem; by eauto.
Qed.

Lemma eq_st_write_reg_eq gamma st1 st2 x v :
  eq_st gamma st1 st2
  -> eq_st gamma (write_reg st1 x v) (write_reg st2 x v).
Proof.
  move=> h.
  rewrite -(ctx_update_reg_id gamma x).
  apply: eq_st_write_reg => //; by rewrite eq_val_refl ?orbT.
Qed.

Lemma eq_st_on_ctx_update_write_reg is_n gamma st1 st2 x e t :
  let: gamma' := ctx_update_reg gamma x t in
  let: st1' := write_reg st1 x (eval (st_vm st1) e) in
  let: st2' := write_reg st2 x (eval (st_vm st2) e) in
  eq_st_on is_n gamma st1 st2
  -> typede gamma e t
  -> eq_st_on is_n gamma' st1' st2'.
Proof.
  move=> [hvm hmem] he.
  apply: eq_st_on_write_reg => //.
  apply: orb_implP => ht.
  apply/eqP.
  apply: eq_vm_eval_e_public; by eauto.
Qed.

Lemma eq_st_ctx_update_write_reg gamma st1 st2 x e t :
  let: gamma' := ctx_update_reg gamma x t in
  let: st1' := write_reg st1 x (eval (st_vm st1) e) in
  let: st2' := write_reg st2 x (eval (st_vm st2) e) in
  eq_st gamma st1 st2
  -> typede gamma e t
  -> eq_st gamma' st1' st2'.
Proof.
  move=> [hspec hseq hms] he.
  split=> //; first exact: eq_st_on_ctx_update_write_reg.
  case: hseq; first by left.
  right.
  exact: eq_st_on_ctx_update_write_reg.
Qed.

Lemma eq_mem_ctx_update_reg is_n gamma x t m m' :
  eq_mem is_n gamma m m'
  -> eq_mem is_n (ctx_update_reg gamma x t) m m'.
Proof. done. Qed.

Lemma eq_vm_s_instantiate vm vm' theta theta' gamma gamma' :
  eq_vm_s gamma vm vm'
  -> ctx_le gamma (ctx_instantiate theta gamma')
  -> eq_vm_s (ctx_instantiate theta' gamma') vm vm'.
Proof.
  move=> hvm hle.
  apply: (weak_eq_map hvm) => x.
  move: (ctx_le_reg hle x) => /andP [] _.
  by rewrite ty_le_ty_of_lvl.
Qed.

Lemma eq_mem_s_instantiate m m' theta theta' gamma gamma' :
  eq_mem_s gamma m m'
  -> ctx_le gamma (ctx_instantiate theta gamma')
  -> eq_mem_s (ctx_instantiate theta' gamma') m m'.
Proof.
  move=> hvm hle.
  apply: (weak_eq_map hvm) => -[a i].
  move: (ctx_le_arr hle a) => /andP [] _.
  by rewrite ty_le_ty_of_lvl.
Qed.

Lemma eq_st_on_s_instantiate st1 st2 gamma gamma' xi theta theta' :
  eq_st_on_s gamma st1 st2
  -> ctx_le gamma (ctx_instantiate theta gamma')
  -> eq_st_on_s
       (ctx_instantiate theta' gamma')
       (st_after_RET_S st1 xi)
       (st_after_RET_S st2 xi).
Proof.
  move=> [hvm hmem] hle.
  split.
  - case: xi => [msf|] /=.
    + apply: eq_vm_vm_set_eq. apply: eq_vm_s_instantiate; by eauto.
    apply: eq_vm_s_instantiate; by eauto.
  apply: eq_mem_s_instantiate; by eauto.
Qed.

Lemma weak_synced sigma sigma' vm ms :
  synced sigma vm ms
  -> mss_le sigma' sigma
  -> synced sigma' vm ms.
Proof. move=> h [] ?; by subst. Qed.

Lemma synced_mss_cond sigma vm e b b' ms :
   synced sigma vm ms
  -> eval vm e = Vbool b'
  -> synced (mss_cond sigma (if b then e else enot e)) vm ((b != b') || ms).
Proof.
  case: sigma => [//| msf |//] /= /andP [/eqP <- ->].
  by case: b b' => /= -[] /= -> //=; case: ms.
Qed.

Lemma synced_mss_restrict sigma vm x v ms :
  synced sigma vm ms
  -> synced (mss_restrict sigma x) (Vm.set vm x v) ms.
Proof.
  rewrite /mss_restrict.
  case hx: Sr.mem => //.
  move: hx => /negPf.
  case: sigma => [// | msf | msf e] /=.
  - by rewrite /msf_in_range Sr.F.singleton_b Sr.eqbP eq_sym Vm.get_set => ->.
  rewrite Sr.F.add_b Sr.eqbP eq_sym => /norP [??].
  by rewrite /msf_in_range eval_set // set_neq.
Qed.

Lemma typed_callstackI sigma gamma cs :
  typed_callstack sigma gamma cs
  -> match cs with
     | [::] => True
     | (f, _, c) :: cs' =>
         exists theta,
           let: sigmaf' := cert_mss' (cert f) in
           let: gammaf' := cert_ctx' (cert f) |> ctx_instantiate theta in
           typedc sigma gamma c sigmaf' gammaf'
           /\ typed_callstack sigmaf' gammaf' cs'
     end.
Proof. case; by eeauto. Qed.

Lemma is_n_sty_after_init_msf is_n t :
  let: t' := proj_is_n is_n (sty_after_init_msf t) in
  t' = sty_n t \/ t' = tsecret.
Proof. case: is_n => /=; first by left. case: sty_n => [|[]]; by auto. Qed.

Lemma eq_st_on_ctx_after_init_msf is_n gamma st1 st2 msf :
  let: gamma' := ctx_after_init_msf gamma msf in
  let: st1' := write_reg st1 msf msf_nomask in
  let: st2' := write_reg st2 msf msf_nomask in
  eq_st_on_n gamma st1 st2
  -> eq_st_on is_n gamma' st1' st2'.
Proof.
  move=> [hvm hmem].
  split=> [x | [a i]] /=.
  - rewrite !Vm.get_set.
    case: eqP => _; first exact: eq_val_refl.
    by case: (is_n_sty_after_init_msf is_n (ctx_reg gamma x)) => ->.
  case: (is_n_sty_after_init_msf is_n (ctx_arr gamma a)) => -> //.
  exact: (hmem (_, _)).
Qed.

Lemma eq_st_ctx_after_init_msf gamma st1 st2 msf :
  let: gamma' := ctx_after_init_msf gamma msf in
  let: st1' := write_reg st1 msf msf_nomask in
  let: st2' := write_reg st2 msf msf_nomask in
  eq_st gamma st1 st2
  -> ~~ st_ms st1
  -> eq_st gamma' st1' st2'.
Proof.
  move=> [_ hseq hms] /negPf hms1.
  case: hseq => hseq; first congruence.
  split=> //; first exact: eq_st_on_ctx_after_init_msf.
  right.
  exact: eq_st_on_ctx_after_init_msf.
Qed.

Lemma eq_st_ctx_after_update_msf gamma st1 st2 x y e :
  let: st1' := st_after_update_msf st1 x y e in
  let: st2' := st_after_update_msf st2 x y e in
  eq_st gamma st1 st2
  -> synced (MSSoutdated y e) (st_vm st1) (st_ms st1)
  -> synced (MSSoutdated y e) (st_vm st2) (st_ms st2)
  -> eq_st gamma st1' st2'.
Proof.
  move=> hst.
  have := eq_st_ms hst.
  rewrite /st_after_update_msf /=.
  case: (st_ms st1) => /= <-.
  - move=>  /andP [] /orP [] /eqP -> _ /andP [] /orP [] /eqP -> _ /=;
      rewrite ?if_same;
      exact: eq_st_write_reg_eq.
  rewrite /msf_in_range => /andP [] /andP [] /eqP -> /negPf -> /eqP -> /andP []
    /andP [] /eqP -> /negPf -> /eqP ->.
  exact: eq_st_write_reg_eq.
Qed.

Lemma eq_st_ctx_after_protect gamma st1 st2 x y msf :
  let: st1' := st_after_protect st1 x y msf in
  let: st2' := st_after_protect st2 x y msf in
  eq_st gamma st1 st2
  -> synced (MSSupdated msf) (st_vm st1) (st_ms st1)
  -> synced (MSSupdated msf) (st_vm st2) (st_ms st2)
  -> eq_st (ctx_after_protect gamma x y) st1' st2'.
Proof.
  rewrite /st_after_protect.
  move=> [hspec hseq hms] /andP [/eqP <- _] /andP [/eqP <- _].
  rewrite -hms.
  case hms1: st_ms.
  - apply: eq_st_write_reg => //; first exact: eq_val_refl. by rewrite hms1.
  move: hseq.
  rewrite hms1.
  move=> [// | hseq].
  apply: eq_st_write_reg.
  - split=> //. by right.
  - rewrite /sty_after_init_msf /=.
    apply: weak_eq_val; first exact: (eq_st_on_vm hseq).
    exact: ty_le_lvl_of_ty_ty_of_lvl.
  rewrite hms1 /=.
  exact: (eq_st_on_vm hseq).
Qed.

Lemma synced_after_ret_s sigma sigma' xi st :
  mss_call sigma xi = Some sigma'
  -> synced sigma' (st_vm (st_after_RET_S st xi)) true.
Proof.
  move=> /mss_callE [[-> ->] // | [msf [-> -> ->]]]; subst.
  by rewrite /= /msf_in_range set_eq.
Qed.

Lemma synced_after_init_msf vm msf :
  synced (MSSupdated msf) (Vm.set vm msf msf_nomask) false.
Proof. by rewrite /= /msf_in_range set_eq. Qed.

Lemma synced_after_update_msf st x y e :
  let: st' := st_after_update_msf st x y e in
  synced (MSSoutdated y e) (st_vm st) (st_ms st)
  -> synced (MSSupdated x) (st_vm st') (st_ms st).
Proof.
  move=> /andP [].
  rewrite /= /msf_in_range set_eq.
  case: st_ms; last by move=> /andP [/eqP -> /negPf ->].
  move=> /orP [] /eqP ->; first by rewrite eqxx.
  by case: ifP.
Qed.

End UTILS.


Section TYPEDM_SYNCED.

Context
  (cert : certificate)
  (p : program)
  (htyp : typedp cert p)
.

Lemma typedm_synced_step m m' d o sigma gamma :
  let: st := m_st m in
  let: st' := m_st m' in
  step p m d o m' ->
  typedm cert sigma gamma m ->
  synced sigma (st_vm st) (st_ms st) ->
  exists sigma' gamma',
      [/\ typedm cert sigma' gamma' m'
        & synced sigma' (st_vm st') (st_ms st')
      ].
Proof.
  case=> {m m' d o} => - [_c g cs st] /=.

  - move=> x e c ? [theta [/= htyc htycs]] hsync; subst _c.
    move: htyc => /typedcI [sigma0 [gamma0 [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [? [t htye ?]]; subst.
    exists (mss_restrict sigma0 x), (ctx_update_reg gamma0 x t); split.
    + exists theta; split=> /=; last assumption. apply: typed_weak; by eeauto.
    apply: synced_mss_restrict. apply: weak_synced; eassumption.

  - move=> x a e c i ? hi ha [theta [/= htyc htycs]] hsync; subst _c.
    move: htyc => /typedcI [sigma0 [gamma0 [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [htye ??]; subst.
    exists (mss_restrict sigma0 x), (ctx_after_load gamma0 x a); split.
    + exists theta; split=> /=; last assumption. apply: typed_weak; by eeauto.
    apply: synced_mss_restrict. apply: weak_synced; eassumption.

  - move=> x a e c i b j ? hi hb ha hms [theta [/= htyc htycs]] hsync; subst _c.
    move: htyc => /typedcI [sigma0 [gamma0 [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [htye ??]; subst.
    exists (mss_restrict sigma0 x), (ctx_after_load gamma0 x a); split.
    + exists theta; split=> /=; last assumption. apply: typed_weak; by eeauto.
    apply: synced_mss_restrict. apply: weak_synced; eassumption.

  - move=> a e x c i ? hi ha [theta [/= htyc htycs]] hsync; subst _c.
    move: htyc => /typedcI [sigma0 [? [? [gamma1 [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [htye ? hgamma1]; subst.
    exists sigma0, gamma1; split.
    + exists theta; split=> /=; last assumption. apply: typed_weak; by eeauto.
    apply: weak_synced; eassumption.

  - move=> a e x c i b j ? hi hb ha hms [theta [/= htyc htycs]] hsync; subst _c.
    move: htyc => /typedcI [sigma0 [? [? [gamma1 [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [htye ? hgamma1]; subst.
    exists sigma0, gamma1; split.
    + exists theta; split=> /=; last assumption. apply: typed_weak; by eeauto.
    apply: weak_synced; eassumption.

  - move=> msf c ? /negPf hms [theta [/= htyc htycs]] hsync; subst _c.
    move: htyc => /typedcI [sigma0 [gamma0 [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [??]; subst.
    exists (MSSupdated msf), (ctx_after_init_msf gamma0 msf); split.
    + exists theta; split=> /=; last assumption. apply: typed_weak; by eeauto.
    rewrite hms. exact: synced_after_init_msf.

  - move=> msf' msf e c ? [theta [/= htyc htycs]] hsync; subst _c.
    move: htyc => /typedcI [sigma0 [gamma0 [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [???]; subst.
    exists (MSSupdated msf'), gamma0; split.
    + exists theta; split=> /=; last assumption. apply: typed_weak; by eeauto.
    apply: synced_after_update_msf. apply: weak_synced; eassumption.

  - move=> x y msf c ? [theta [/= htyc htycs]] hsync; subst _c.
    move: htyc => /typedcI [sigma0 [gamma0 [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [???]; subst.
    exists (mss_restrict (MSSupdated msf) x), (ctx_after_protect gamma0 x y);
      split.
    + exists theta; split=> /=; last assumption. apply: typed_weak; by eeauto.
    apply: synced_mss_restrict. apply: weak_synced; eassumption.

  - move=> e c1 c0 c b b' ? he [theta [/= htyc htycs]] hsync; subst _c.
    move: htyc => /typedcI [sigma0 [gamma0 [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [htye hty1 hty0]; subst.
    exists (mss_cond sigma0 (if b then e else enot e)), gamma0; split.
    + exists theta; split=> /=; last assumption.
      apply: typed_after_if; [eassumption | eassumption|].
      apply: typed_weak; by eeauto.
    apply: synced_mss_cond => //. apply: weak_synced; eassumption.

  - move=> e c1 c b b' ? he [theta [/= htyc htycs]] hsync; subst _c.
    move: htyc => /typedcI [sigma0 [gamma0 [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [htye hty1 ??]; subst.
    exists (mss_cond sigma0 (if b then e else enot e)), gamma0; split.
    + rewrite -cat_rcons -cats1 -{3}(cat0s c) -(fun_if (fun x => x ++ c)).
      exists theta; split=> /=; last assumption.
      apply: typed_after_if; [| by constructor |].
      * apply: typed_capp; first eassumption.
        apply: typed_weak; by eeauto.
      apply: typed_weak; by eeauto.
    apply: synced_mss_cond => //. apply: weak_synced; eassumption.

  - move=> f l xi c ? [theta [/= htyc htycs]] hsync; subst _c.
    move: htyc => /typedcI [sigma0 [gamma0 [? [? [? [? [htyi htyc ????]]]]]]].
    move: htyi => /typediI [?? [thetaf [??]]]; subst.
    exists (cert_mss (cert f)), (ctx_instantiate thetaf (cert_ctx (cert f)));
      split.
    + exists thetaf; split=> /=; first exact: ctx_instantiate_typedc.
      econstructor; last eassumption.
      apply: typed_weak; by eeauto.
    apply: weak_synced; eassumption.

  move=> f l xi cont m' ? hret [theta [/= htyc htycs]] hsync; subst _c.
  move: htyc => /typedcI [??].
  case: (boolP (is_speculative_ret _ _ _ _)) hret => hret.
  - move=> [/in_contpI hcont ?]; subst m' => /=.
    have [theta' [sigma_call [hsigma_call htycont]]] :=
      typedc_contc (htyp f) hcont.
    exists sigma_call, (ctx_instantiate theta' (cert_ctx' (cert g))); split.
    + exists theta_Secret; split=> /=; last by constructor.
      apply: typed_weak; last exact: ctx_instantiate_theta_Secret; by eeauto.
    apply: synced_after_ret_s. eassumption.

  move=> ?; subst m' => /=.
  have hcs : cs = (f, l, cont) :: drop 1 cs.
  - case: (cs) hret => //= -[[f' l'] cont'] ?.
    by rewrite /is_speculative_ret /= negbK drop0 => /eqP ->.
  move: htycs.
  rewrite hcs => /typed_callstackI [thetaf [htyc {}hcs]].
  exists (cert_mss' (cert g)), (ctx_instantiate theta (cert_ctx' (cert g)));
    split.
  - rewrite /= drop0. by exists thetaf.
  apply: weak_synced; eassumption.
Qed.

Lemma typedm_synced_sem m m' ds os sigma gamma :
  let: st := m_st m in
  let: st' := m_st m' in
  sem p m ds os m' ->
  typedm cert sigma gamma m ->
  synced sigma (st_vm st) (st_ms st) ->
  exists sigma' gamma',
    [/\ typedm cert sigma' gamma' m'
      & synced sigma' (st_vm st') (st_ms st')
    ].
Proof.
  elim: ds m m' os sigma gamma => [|d ds hind] m m' os sigma gamma /semI [].
  - move=> ->. by eeauto.
  move=> o [os' [? [mi hstep hsem]]] htym hsync.
  have [? [? [??]]] := typedm_synced_step hstep htym hsync.
  by eeauto.
Qed.

End TYPEDM_SYNCED.


Module __SingleStepSoundness.

Section PROOF.

Context
  (cert : certificate)
  (p : program)
  (htyp : typedp cert p)
.

Notation typedi := (typedi cert).
Notation typedc := (typedc cert).
Notation step := (step p).
Notation sem := (sem p).
Notation typedm := (typedm cert).

Let sss_invariant sigma gamma m1 m2 :=
  let: st1 := m_st m1 in
  let: st2 := m_st m2 in
  [/\ typedm sigma gamma m1
    , synced sigma (st_vm st1) (st_ms st1)
    , synced sigma (st_vm st2) (st_ms st2)
    & eq_m gamma m1 m2
  ].

Let single_step_soundnessT m1 d :=
  forall m1' m2 m2' o1 o2 sigma gamma,
    step m1 d o1 m1'
    -> step m2 d o2 m2'
    -> sss_invariant sigma gamma m1 m2
    -> o1 = o2
       /\ exists sigma' gamma', sss_invariant sigma' gamma' m1' m2'.

Lemma sss_assign m1 d x e c :
  m_c m1 = Iassign x e :: c
  -> d = Dstep
  -> single_step_soundnessT m1 d.
Proof.
  move: m1 => [/= _ g cs [vm1 m1 ms]] -> ?; subst.
  move=> m1' [/= c2 g2 cs2 [vm2 m2 ms2]] m2' o1 o2 sigma gamma hsem1 hsem2
    [/= hty1 hsync1 hsync2 [/= ??? hst]];
    subst.
  move: hsem1 hsem2 => /stepI [??] /stepI [??]; subst.
  split=> //.
  move: hty1 => [/= theta [hty1 hcs]].
  move: hty1 =>
    /typedcI [sigma0 [gamma0 [sigmai [gammai [sigma0' [gamma0' []]]]]]]
    /typediI [? [t htye ?]] htyc ????;
    subst.
  exists (mss_restrict sigma0 x), (ctx_update_reg gamma0 x t).
  split=> /=; last split=> //=.
  - by eeauto.
  - by eauto using synced_mss_restrict, weak_synced.
  - by eauto using synced_mss_restrict, weak_synced.
  by eauto using eq_st_ctx_update_write_reg, weak_eq_st.
Qed.

Lemma sss_load_n m1 d x a e c :
  m_c m1 = Iload x a e :: c
  -> d = Dstep
  -> single_step_soundnessT m1 d.
Proof.
  move: m1 => [/= _ g cs [vm1 m1 ms]] -> ?; subst.
  move=> m1' [/= c2 g2 cs2 [vm2 m2 ms2]] m2' o1 o2 sigma gamma hsem1 hsem2
    [/= hty1 hsync1 hsync2 [/= ??? [/= hspec hseq ?]]];
    subst c2 g2 cs2 ms2.
  move: hsem1 hsem2 =>
    /stepI [i1 [/= heval1 hina1 ??]] /stepI [i2 [/= heval2 _ ??]]; subst.
  move: hty1 => [/= theta [hty1 hcs]].
  move: hty1 =>
    /typedcI [sigma0 [gamma0 [sigmai [gammai [sigma0' [gamma0' []]]]]]]
    /typediI [htye ??] htyc ?? hgamma ?;
    subst.
  move: heval1.
  rewrite (eq_vm_eval_e_public (is_n := false) (vm' := vm2) _ htye erefl);
    first last.
  - move: hspec => [/= ? _]. by eauto using weak_eq_vm.
  rewrite heval2 => -[?]; subst i2.
  split=> //.
  exists (mss_restrict sigma0 x), (ctx_after_load gamma0 x a).
  split=> /=; last split=> //=.
  - by eeauto.
  - by eauto using synced_mss_restrict, weak_synced.
  - by eauto using synced_mss_restrict, weak_synced.
  apply: eq_st_write_reg; [apply: weak_eq_st; by eeauto | done|].
  apply/orP.
  case: hseq => [-> | hseq]; first by left.
  right.
  apply: weak_eq_val; first exact: (eq_st_on_mem hseq (_, _)).
  by move: (ctx_le_arr hgamma a) => /andP [-> _].
Qed.

Lemma sss_load_s m1 d x a e c b j :
  m_c m1 = Iload x a e :: c
  -> d = Dmem b j
  -> single_step_soundnessT m1 d.
Proof.
  move: m1 => [/= _ g cs [vm1 m1 ms]] -> ?; subst.
  move=> m1' [/= c2 g2 cs2 [vm2 m2 ms2]] m2' o1 o2 sigma gamma hsem1 hsem2
    [/= hty1 hsync1 hsync2 [/= ??? [/= hspec hseq ?]]];
    subst c2 g2 cs2 ms2.
  move: hsem1 hsem2 =>
    /stepI [i1 [/= heval1 _ hinb1 hspec1 ??]]
    /stepI [i2 [/= heval2 _ _ _ ??]]; subst.
  move: hty1 => [/= theta [hty1 hcs]].
  move: hty1 =>
    /typedcI [sigma0 [gamma0 [sigmai [gammai [sigma0' [gamma0' []]]]]]]
    /typediI [htye ??] htyc ?? hgamma ?;
    subst.
  move: heval1.
  rewrite (eq_vm_eval_e_public (is_n := false) (vm' := vm2) _ htye erefl);
    first last.
  - move: hspec => [/= ? _]. by eauto using weak_eq_vm.
  rewrite heval2 => -[?]; subst i2.
  split=> //.
  exists (mss_restrict sigma0 x), (ctx_after_load gamma0 x a).
  split=> /=; last split=> //=.
  - by eeauto.
  - by eauto using synced_mss_restrict, weak_synced.
  - by eauto using synced_mss_restrict, weak_synced.
  apply: eq_st_write_reg; [apply: weak_eq_st; by eeauto | done|].
  by rewrite /= hspec1.
Qed.

Lemma sss_store_n m1 d x a e c :
  m_c m1 = Istore a e x :: c
  -> d = Dstep
  -> single_step_soundnessT m1 d.
Proof.
  move: m1 => [/= _ g cs [vm1 m1 ms]] -> ?; subst.
  move=> m1' [/= c2 g2 cs2 [vm2 m2 ms2]] m2' o1 o2 sigma gamma hsem1 hsem2
    [/= hty1 hsync1 hsync2 [/= ??? [/= hspec hseq ?]]];
    subst c2 g2 cs2 ms2.
  move: hsem1 hsem2 =>
    /stepI [i1 [/= heval1 hina ??]] /stepI [i2 [/= heval2 _ ??]]; subst.
  move: hty1 => [/= theta [hty1 hcs]].
  move: hty1 =>
    /typedcI [sigma0 [gamma0 [sigmai [gammai [sigma0' [gamma0' []]]]]]]
    /typediI [htye ? [hle /andP [hxn hxs] hb]] htyc ?? hgamma hgamma';
    subst.
  move: heval1.
  rewrite (eq_vm_eval_e_public (is_n := false) (vm' := vm2) _ htye erefl);
    first last.
  - move: hspec => [/= ? _]. by eauto using weak_eq_vm.
  rewrite heval2 => -[?]; subst i2.
  split=> //.
  exists sigma0, gammai.
  split=> /=; last split=> //=.
  - by eeauto.
  - by eauto using weak_synced.
  - by eauto using weak_synced.
  split=> //=.
  + apply: eq_st_on_write_mem; [| eassumption | | done |].
    + by apply: (weak_eq_st_on_ms false false hspec).
    + by eeauto.
    apply: weak_eq_val; first exact: (eq_st_on_vm hspec).
    move: (ctx_le_reg hgamma x) => /andP [??].
    by rewrite ty_le_ty_of_lvl; eeauto.
  case: hseq => [? | hseq]; [by left | right].
  apply: eq_st_on_write_mem; [| eassumption | | done |].
  + by apply: (weak_eq_st_on_ms false false hseq).
  + by eeauto.
  apply: weak_eq_val; first exact: (eq_st_on_vm hseq).
  by move: (ctx_le_reg hgamma x) => /andP [].
Qed.

Lemma sss_store_s m1 d x a e c b j :
  m_c m1 = Istore a e x :: c
  -> d = Dmem b j
  -> single_step_soundnessT m1 d.
Proof.
  move: m1 => [/= _ g cs [vm1 m1 ms]] -> ?; subst.
  move=> m1' [/= c2 g2 cs2 [vm2 m2 ms2]] m2' o1 o2 sigma gamma hsem1 hsem2
    [/= hty1 hsync1 hsync2 [/= ??? [/= hspec hseq ?]]];
    subst c2 g2 cs2 ms2.
  move: hsem1 hsem2 =>
    /stepI [i1 [/= heval1 _ hinb hspec1 ??]]
    /stepI [i2 [/= heval2 _ _ _ ??]]; subst.
  move: hty1 => [/= theta [hty1 hcs]].
  move: hty1 =>
    /typedcI [sigma0 [gamma0 [sigmai [gammai [sigma0' [gamma0' []]]]]]]
    /typediI [htye ? [hle /andP [hxn hxs] hb]] htyc ?? hgamma hgamma';
    subst.
  move: heval1.
  rewrite (eq_vm_eval_e_public (is_n := false) (vm' := vm2) _ htye erefl);
    first last.
  - move: hspec => [/= ? _]. by eauto using weak_eq_vm.
  rewrite heval2 => -[?]; subst i2.
  split=> //.
  exists sigma0, gammai.
  split=> /=; last split=> //=.
  - by eeauto.
  - by eauto using weak_synced.
  - by eauto using weak_synced.
  split => //; rewrite hspec1; last by left.
  apply: eq_st_on_write_mem; [| eassumption | | done |].
  - by apply: (weak_eq_st_on_ms true true hspec).
  - by eeauto.
  apply: weak_eq_val; first exact: (eq_st_on_vm hspec).
  move: (ctx_le_reg hgamma x) => /andP [??] /=.
  rewrite ty_le_ty_of_lvl.
  case: (a =P b) => [? | /eqP].
  + subst b; by apply: lvl_le_trans hxs.
  by move=> /hb; apply: lvl_le_trans.
Qed.

Lemma sss_init_msf m1 d msf c :
  m_c m1 = Iinit_msf msf :: c
  -> d = Dstep
  -> single_step_soundnessT m1 d.
Proof.
  move: m1 => [/= _ g cs [vm1 m1 ms]] -> ?; subst.
  move=> m1' [/= c2 g2 cs2 [vm2 m2 ms2]] m2' o1 o2 sigma gamma hsem1 hsem2
    [/= hty1 hsync1 hsync2 [/= ??? hst]];
    subst.
  move: hsem1 hsem2 => /stepI [/= /negPf ???] /stepI [/= /negPf ???]; subst.
  split=> //.
  move: hty1 => [/= theta [hty1 hcs]].
  move: hty1 =>
    /typedcI [sigma0 [gamma0 [sigmai [gammai [sigma0' [gamma0' []]]]]]]
    /typediI [??] htyc ????;
    subst.
  exists (MSSupdated msf), (ctx_after_init_msf gamma0 msf).
  split; last split=> //=.
  - by eeauto.
  - exact: synced_after_init_msf.
  - exact: synced_after_init_msf.
  by eauto using eq_st_ctx_after_init_msf, weak_eq_st.
Qed.

Lemma sss_update_msf m1 d x y e c :
  m_c m1 = Iupdate_msf x y e :: c
  -> d = Dstep
  -> single_step_soundnessT m1 d.
Proof.
  move: m1 => [/= _ g cs [vm1 m1 ms]] -> ?; subst.
  move=> m1' [/= c2 g2 cs2 [vm2 m2 ms2]] m2' o1 o2 sigma gamma hsem1 hsem2
    [/= hty1 hsync1 hsync2 [/= ??? hst]];
    subst.
  move: hsem1 hsem2 => /stepI [/= ??] /stepI [/= ??]; subst.
  split=> //.
  move: hty1 => [/= theta [hty1 hcs]].
  move: hty1 =>
    /typedcI [sigma0 [gamma0 [sigmai [gammai [sigma0' [gamma0' []]]]]]]
    /typediI [???] htyc [] ????;
    subst=> //.
  exists (MSSupdated x), gamma0.
  split; last split=> //=.
  - by eeauto.
  - exact: (synced_after_update_msf (st := {| st_mem := m1; |})).
  - exact: (synced_after_update_msf (st := {| st_mem := m2; |})).
  by eauto using eq_st_ctx_after_update_msf, weak_eq_st.
Qed.

Lemma sss_protect m1 d x y msf c :
  m_c m1 = Iprotect x y msf :: c
  -> d = Dstep
  -> single_step_soundnessT m1 d.
Proof.
  move: m1 => [/= _ g cs [vm1 m1 ms]] -> ?; subst.
  move=> m1' [/= c2 g2 cs2 [vm2 m2 ms2]] m2' o1 o2 sigma gamma hsem1 hsem2
    [/= hty1 hsync1 hsync2 [/= ??? hst]];
    subst.
  move: hsem1 hsem2 => /stepI [/= ??] /stepI [/= ??]; subst.
  split=> //.
  move: hty1 => [/= theta [hty1 hcs]].
  move: hty1 =>
    /typedcI [sigma0 [gamma0 [sigmai [gammai [sigma0' [gamma0' []]]]]]]
    /typediI [???] htyc [] ????;
    subst=> //.
  exists (mss_restrict (MSSupdated msf) x), (ctx_after_protect gamma0 x y).
  split; last split=> //=.
  - by eeauto.
  - exact: synced_mss_restrict.
  - exact: synced_mss_restrict.
  by eauto using eq_st_ctx_after_protect, weak_eq_st.
Qed.

Lemma sss_if m1 d b e c0 c1 c :
  m_c m1 = Iif e c0 c1 :: c
  -> d = Dforce b
  -> single_step_soundnessT m1 d.
Proof.
  move: m1 => [/= _ g cs [vm1 m1 ms]] -> ?; subst.
  move=> m1' [/= c2 g2 cs2 [vm2 m2 ms2]] m2' o1 o2 sigma gamma hsem1 hsem2
    [/= hty1 hsync1 hsync2 [/= ??? hst]];
    subst.
  move: hsem1 hsem2 => /stepI [/= b1' [hb ??]] /stepI [/= b2' [hb' ??]];
    subst.
  move: hty1 => [/= theta [hty1 hcs]].
  move: hty1 =>
    /typedcI [sigma0 [gamma0 [sigmai [gammai [sigma0' [gamma0' []]]]]]]
    /typediI [htye htyc0 htyc1] htyc ????.
  move: (hb).
  rewrite (eq_vm_eval_e_public (is_n := false) (vm' := vm2) _ htye erefl);
    first last.
  - move: hst => [[/= ? _] _ _]. by eauto using weak_eq_vm.
  rewrite hb' => -[?]; subst.
  split=> //.
  exists (mss_cond sigma0 (if b then e else enot e)), gamma0.
  split; last split=> //=.
  - exists theta; split=> //=.
    apply: typed_weak; first (by eauto using typed_after_if); by eeauto.

  - by apply: synced_mss_cond => //=; apply: (weak_synced hsync1).
  - by apply: synced_mss_cond => //=; apply: (weak_synced hsync2).
  apply: weak_eq_st; last eassumption.
  by apply: eq_st_with_ms hst.
Qed.

Lemma sss_while m1 d b e c0 c :
  m_c m1 = Iwhile e c0 :: c
  -> d = Dforce b
  -> single_step_soundnessT m1 d.
Proof.
  move: m1 => [/= _ g cs [vm1 m1 ms]] -> ?; subst.
  move=> m1' [/= c2 g2 cs2 [vm2 m2 ms2]] m2' o1 o2 sigma gamma hsem1 hsem2
    [/= hty1 hsync1 hsync2 [/= ??? hst]];
    subst.
  move: hsem1 hsem2 => /stepI [/= b1' [hb ??]] /stepI [/= b2' [hb' ??]];
    subst.
  move: hty1 => [/= theta [hty1 hcs]].
  move: hty1 =>
    /typedcI [sigma0 [gamma0 [? [? [? [? []]]]]]]
    /typediI [htye htyc0 ??] htyc ????;
    subst.
  move: (hb).
  rewrite (eq_vm_eval_e_public (is_n := false) (vm' := vm2) _ htye erefl);
    first last.
  - move: hst => [[/= ? _] _ _]. by eauto using weak_eq_vm.
  rewrite hb' => -[?]; subst.
  split=> //.
  exists (mss_cond sigma0 (if b then e else enot e)), gamma0.
  split; last split=> //=.
  - rewrite -cat_rcons -cats1 -{3}(cat0s c) -(fun_if (fun x => x ++ c)).
    exists theta; split=> //=.
    {
      apply: typed_weak.
      - apply: typed_after_if; [|by constructor | eassumption].
        apply: typed_capp; first eassumption.
        apply: typed_weak; by eeauto.
      all: by eeauto.
    }
  - apply: synced_mss_cond; by eauto using weak_synced.
  - apply: synced_mss_cond; by eauto using weak_synced.
  apply: weak_eq_st; last eassumption.
  by apply: eq_st_with_ms hst.
Qed.

Lemma sss_call m1 d l xi f c :
  m_c m1 = Icall l xi f :: c
  -> d = Dstep
  -> single_step_soundnessT m1 d.
Proof.
  move: m1 => [/= _ g cs [vm1 m1 ms]] -> ?; subst.
  move=> m1' [/= c2 g2 cs2 [vm2 m2 ms2]] m2' o1 o2 sigma gamma hsem1 hsem2
    [hty1 /= hsync1 hsync2 [/= ??? hst]];
    subst.
  move: hsem1 hsem2 => /stepI [/= ??] /stepI [/= ??]; subst.

  have := htyp f.
  set sigmaf := cert_mss (cert f).
  set sigmaf' := cert_mss' (cert f).
  set gammaf := cert_ctx (cert f).
  set gammaf' := cert_ctx' (cert f).
  move=> htyf.

  split=> //.
  move: hty1 => [/= thetag [hty1 hcs]].
  move: hty1 =>
    /typedcI [_ [_ [? [_ [? [? []]]]]]]
    /typediI [-> ? [thetaf [-> ->]]] htyc ????.
  exists sigmaf, (ctx_instantiate thetaf gammaf).
  split; last split=> //=.
  - exists thetaf; split=> /=; first exact: ctx_instantiate_typedc.
    by eeauto.
  - by eauto using weak_synced.
  - by eauto using weak_synced.
  by eauto using weak_eq_st.
Qed.


Lemma sss_ret m1 d f l xi cont :
  m_c m1 = [::]
  -> d = Dreturn f l xi cont
  -> single_step_soundnessT m1 d.
Proof.
  move: m1 => [/= _ g cs [vm1 m1 ms]] -> ?; subst d.
  move=> m1' [/= c2 g2 cs2 [vm2 m2 ms2]] m2' o1 o2 sigma gamma hsem1 hsem2
    [/= hty1 hsync1 hsync2 [/= ??? [/= hspec ? hst]]];
    subst c2 g2 cs2 ms2.
  move: hsem1 hsem2 => /stepI /= [] ? hmspec /stepI /= [] ? hmspec'; subst o1 o2.
  split => //.
  move: hmspec hmspec'.
  case: (boolP (is_speculative_ret cs f l cont)) => hisspec.
  + move=> [hcont ->] [_ ->].
    move: hty1 => [/= theta [hty1 _]].
    move: hty1 => /typedcI [hsigma0 hgamma0].
    set sigmag' := cert_mss' (cert g).
    set gammag' := cert_ctx' (cert g).

    have := htyp f.
    set sigmaf' := cert_mss' (cert f).
    set gammaf' := cert_ctx' (cert f).
    move=> htyf.

    have {}hcont : List.In (l, xi, cont) (contc g (p f)).
    - by eauto using in_contpI.

    have [theta' [sigma_call [hsigma_call htycont]]] := typedc_contc htyf hcont.
    clear hcont htyf.

    exists sigma_call, (ctx_instantiate theta' gammag').
    split; last split=> //=.
    - exists theta_Secret; split=> /=; last by constructor.
      apply: typed_weak; last exact: ctx_instantiate_theta_Secret; by eeauto.
    - exact: (synced_after_ret_s (sigma := sigmag') {| st_vm := _; |}).
    - exact: (synced_after_ret_s (sigma := sigmag') {| st_vm := _; |}).
    split=> //=; last by constructor.
    apply: eq_st_on_s_instantiate; by eauto.
  move=> -> ->.
  have heqcs : cs = (f, l, cont) :: drop 1 cs.
  - case: (cs) hisspec => //= -[[f' l'] cont'] ?.
    rewrite /is_speculative_ret /=.
    by rewrite negbK drop0 => /eqP ->.
  move: hty1 => [/= thetag [hty1 hcs]].
  move: hty1 => /typedcI [hmssle hctxle].
  move: hcs; rewrite heqcs => /typed_callstackI [thetaf [htyc hcs]].
  exists (cert_mss' (cert g)), (ctx_instantiate thetag (cert_ctx' (cert g))).
  split; last split=> //=.
  - rewrite /= drop0. by eeauto.
  - by eauto using weak_synced.
  - by eauto using weak_synced.
  by apply: weak_eq_st hctxle; split.
Qed.

Lemma main m1 d :
  single_step_soundnessT m1 d.
Proof.
  move=> > [] > *.
  - apply: sss_assign; by eeauto.
  - apply: sss_load_n; by eeauto.
  - apply: sss_load_s; by eeauto.
  - apply: sss_store_n; by eeauto.
  - apply: sss_store_s; by eeauto.
  - apply: sss_init_msf; by eeauto.
  - apply: sss_update_msf; by eeauto.
  - apply: sss_protect; by eeauto.
  - apply: sss_if; by eeauto.
  - apply: sss_while; by eeauto.
  - apply: sss_call; by eeauto.
  apply: sss_ret; by eeauto.
Qed.

End PROOF.

End __SingleStepSoundness.

Definition single_step_soundness := __SingleStepSoundness.main.


(* -------------------------------------------------------------------------- *)
(* Multi-step soundness. *)

Section MULTISTEP.

Context
  (cert : certificate)
  (p : program)
  (htyp : typedp cert p)
.

Notation typedi := (typedi cert).
Notation typedc := (typedc cert).
Notation step := (step p).
Notation sem := (sem p).
Notation typedm := (typedm cert).

Lemma multi_step_soundness m1 m1' m2 m2' ds os1 os2 sigma gamma :
  let: st1 := m_st m1 in
  let: st2 := m_st m2 in
  let: st1' := m_st m1' in
  let: st2' := m_st m2' in
  sem m1 ds os1 m1'
  -> sem m2 ds os2 m2'
  -> typedm sigma gamma m1
  -> synced sigma (st_vm st1) (st_ms st1)
  -> synced sigma (st_vm st2) (st_ms st2)
  -> eq_m gamma m1 m2
  -> os1 = os2
     /\ exists sigma' gamma',
          [/\ typedm sigma' gamma' m1'
            , synced sigma' (st_vm st1') (st_ms st1')
            , synced sigma' (st_vm st2') (st_ms st2')
            & eq_m gamma' m1' m2'
          ].
Proof.
  elim: ds m1 m1' m2 m2' os1 os2 sigma gamma
    => [|d ds hind] m1 m1' m2 m2' os1 os2 sigma gamma
    /semI hsem1 /semI hsem2 htym1 hsync1 hsync2 heqm.
  - move: hsem1 hsem2 => [??] [??]; subst. by eeauto.
  move: hsem1 hsem2
    => [o1 [os1' [? [mi1 hstep1 hsem1]]]] [o2 [os2' [? [mi2 hstep2 hsem2]]]];
    subst.
  have hsss_invariant := And4 htym1 hsync1 hsync2 heqm.
  have [? [sigmai [gammai [htymi1 hsynci1 hsynci2 heqmi]]]] :=
    single_step_soundness htyp hstep1 hstep2 hsss_invariant.
  subst.
  by have [-> ?] :=
    hind _ _ _ _ _ _ _ _ hsem1 hsem2 htymi1 hsynci1 hsynci2 heqmi.
Qed.

Lemma typedm_initial_machine m :
  let: c := cert (p_entry_fn p) in
  let: sigma := cert_mss c in
  let: gamma := cert_ctx c in
  typedp cert p
  -> is_initial_machine p m
  -> typedm sigma gamma m.
Proof.
  move: m => [c f cs st] /(_ (p_entry_fn p)).
  move=> hty /and3P [] /= /eqP ? /eqP ? /eqP ?; subst c f cs.
  exists theta_Secret; split; last by constructor.
  apply: typed_weak; last exact: ctx_instantiate_theta_Secret; by eeauto.
Qed.

Lemma eqm_initial_machine m1 m2 :
  let: c := cert (p_entry_fn p) in
  let: gamma := cert_ctx c in
  let: st1 := m_st m1 in
  let: st2 := m_st m2 in
  initial_phi p gamma m1 m2
  -> eq_m gamma m1 m2.
Proof.
  move=> [] /and3P [] /eqP ? /eqP ? /eqP ? /and3P [] /eqP ? /eqP ? /eqP ? []
    [??] [??] ?.
  split; [congruence | congruence | congruence|].
  split=> //.
  by right.
Qed.

End MULTISTEP.

Lemma typedp_soundness p cert :
  Typedp_soundness p cert.
Proof.
  set c := cert (p_entry_fn p).
  set gamma := cert_ctx c.
  move=> /= hsigma htyp ds os1 os2 m1 m2 m1' m2' [hm1 hm2 hst] hsem1 hsem2.
  have htym1 := typedm_initial_machine htyp hm1.
  have htym2 := typedm_initial_machine htyp hm2.
  have heqm := eqm_initial_machine (And3 hm1 hm2 hst).
  have [||-> //] := multi_step_soundness htyp hsem1 hsem2 htym1 _ _ heqm.
  all: by move: hsigma => /wfcertP ->.
Qed.
