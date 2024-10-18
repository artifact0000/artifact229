From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  utils
  utils_facts
  var
  syntax
  syntax_facts
  semantics
  semantics_facts
  typesystem
  typesystem_facts
  security
  security_facts
  linear
  linearization
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.


Lemma step_load p m x a e c i b j d :
  let: m' := m_after_load m c x b j in
  m_c m = Iload x a e :: c ->
  eval (st_vm (m_st m)) e = Vint i ->
  in_bounds b j ->
  (if in_bounds a i
  then [/\ a = b, i = j & d = Dstep ]
  else [/\ st_ms (m_st m) & d = Dmem b j ]) ->
  step p m d (Oaddr a i) m'.
Proof.
  case: (boolP (in_bounds a i)) => hina hc hi hb.
  - move=> [???]; subst a i d. apply: step_load_n; eassumption.
  move=> [hms ?]; subst d.
  apply: step_load_s; eassumption.
Qed.

Lemma step_store p m x a e c i b j d :
  let: m' := m_after_store m c b j x in
  m_c m = Istore a e x :: c ->
  eval (st_vm (m_st m)) e = Vint i ->
  in_bounds b j ->
  (if in_bounds a i
  then [/\ a = b, i = j & d = Dstep ]
  else [/\ st_ms (m_st m) & d = Dmem b j ]) ->
  step p m d (Oaddr a i) m'.
Proof.
  case: (boolP (in_bounds a i)) => hina hc hi hb.
  - move=> [???]; subst a i d. apply: step_store_n; eassumption.
  move=> [hms ?]; subst d.
  apply: step_store_s; eassumption.
Qed.

Lemma lsemI lp m ds os m' :
  lsem lp m ds os m' ->
  match ds with
  | [::] => [/\ os = [::] & m = m' ]
  | d :: ds' =>
      exists o os' mi,
      [/\ os = o :: os'
        , lstep lp m d o mi
        & lsem lp mi ds' os' m'
      ]
  end.
Proof. case; by eeauto. Qed.

Section PROOF.

Context
  (p : program)
  (lp : lprogram)
  (Lin Lret : funname -> label)
  (ra : funname -> regvar)
  (to_Z : funname -> label -> Z) (* This should be in Label. *)
  (RA : Sr.t)
.

Notation compile_i := (compile_i p lp Lin ra to_Z RA).
Notation compile_c := (compile_c p lp Lin ra to_Z RA).
Notation compile_call_cont := (compile_call_cont lp RA).
Notation compile_r := (compile_r p lp ra to_Z).
Notation is_call := (is_call p).
Notation eq_on_RA := (eq_on_RA RA).

Lemma compile_iI f l i cont l' :
  compile_i f l i cont l' ->
  match i with
  | Iassign x e =>
      [/\ lp l = (Lassign N x e, [:: l' ])
        , ~~ Sr.mem x RA
        & disjoint RA (free_variables e)
      ]

  | Iload x a e =>
      [/\ lp l = (Lload x a e, [:: l' ])
        , ~~ Sr.mem x RA
        & disjoint RA (free_variables e)
      ]

  | Istore a e x =>
      [/\ lp l = (Lstore a e x, [::l'])
        , ~~ Sr.mem x RA
        & disjoint RA (free_variables e)
      ]

  | Iinit_msf msf =>
      [/\ lp l = (Linit_msf msf, [::l'])
        & ~~ Sr.mem msf RA
      ]

  | Iupdate_msf msf' msf e =>
      [/\ lp l = (Lupdate_msf N msf' msf e, [::l'])
        , ~~ Sr.mem msf' RA
        , ~~ Sr.mem msf RA
        & disjoint RA (free_variables e)
      ]

  | Iprotect x y msf =>
      [/\ lp l = (Lprotect x y msf, [::l'])
        , ~~ Sr.mem x RA
        , ~~ Sr.mem y RA
        & ~~ Sr.mem msf RA
      ]

  | Iif e c1 c0 =>
      [/\ disjoint RA (free_variables e)
        & exists l1 l0 l1',
            [/\ lp l = (Lcjump N e, [::l1; l0])
              , compile_c f l1 c1 cont l1'
              , lp l1' = (Ljump N, [::l'])
              & compile_c f l0 c0 cont l'
            ]
      ]

  | Iwhile e c1 =>
      let: w := Iwhile e c1 in
      [/\ disjoint RA (free_variables e)
        & exists l1 l1',
            [/\ lp l = (Lcjump N e, [::l1; l'])
              , compile_c f l1 c1 (w :: cont) l1'
              & lp l1' = (Ljump N, [::l])
            ]
      ]

  | Icall lr xi g =>
      let: lg := Lin g in
      let: rag := ra g in
      exists l0,
        let: zl := Econst (to_Z g lr) in
        [/\ List.In (f, lr, xi, cont) (contp g p)
          , lp l = (Lassign C rag zl, [::l0])
          , lp l0 = (Ljump C, [::lg])
          & compile_call_cont xi rag zl lr l'
        ]
  end.
Proof. case=> //; by eeauto. Qed.

Lemma compile_cI f l c cont l' :
  compile_c f l c cont l' ->
  match c with
  | [::] => l = l'
  | i :: c' =>
      exists2 li,
        compile_i f l i (c' ++ cont) li
        & compile_c f li c' cont l'
  end.
Proof. case; by eauto. Qed.

Inductive compile_cont (f : funname) : Label.t -> code -> Prop :=
  | CompCont_nil : compile_cont f (Lret f) [::]

  | CompCont_cons : forall i cont l l',
    compile_i f l i cont l' ->
    compile_cont f l' cont ->
    compile_cont f l (i :: cont)

  | CompCont_jumpN : forall cont l l',
    lp l = (Ljump N, [:: l']) ->
    compile_cont f l' cont ->
    compile_cont f l cont.

Inductive compile_callstack (sms : bool) (st:state) : funname -> callstack -> Prop :=
  | CompCs_nil : forall g, sms -> compile_callstack sms st g [::]
  | CompCs_entry : compile_callstack sms st (p_entry_fn p) [::]
  | CompCs_cons : forall g xi cs f cont lr l',
     let: rag := ra g in
     let: zl := Econst (to_Z g lr) in
     List.In (f, lr, xi, cont) (contp g p) ->
     compile_cont f l' cont  ->
     Vm.get (st_vm st) rag = Vint (to_Z g lr) ->
     compile_call_cont xi rag zl lr l' ->
     compile_callstack sms st f cs ->
     compile_callstack sms st g ((f, lr, cont) :: cs).

Lemma compile_callstackI sms st g cs :
  compile_callstack sms st g cs ->
  [\/ [/\ sms & cs = [::] ]
    , [/\ g = p_entry_fn p & cs = [::] ]
    | exists xi cs' f cont lr l',
        let: rag := ra g in
        let: zl := Econst (to_Z g lr) in
        [/\ List.In (f, lr, xi, cont) (contp g p)
          , compile_cont f l' cont
          , Vm.get (st_vm st) rag = Vint (to_Z g lr)
          , compile_call_cont xi rag zl lr l'
          , compile_callstack sms st f cs'
          & cs = (f, lr, cont) :: cs'
        ]
    ].
Proof. case; by eeauto. Qed.

(* Relating source and target state *)

Definition eq_vm_ex_cont ocont vm vm' :=
  match ocont with
  | None => forall r, ~~ Sr.mem r RA -> Vm.get vm r = Vm.get vm' r
  | Some (callee, msf, ra, lr) =>
      [/\ forall r,
          ~~ Sr.mem r RA ->
          msf <> r ->
          Vm.get vm r = Vm.get vm' r
        & let: zl := Econst (to_Z callee lr) in
          let: e := Eop2 Oeq (Evar ra) zl in
          let: v :=
            if eval vm' e == Vbool true then Vm.get vm' msf else msf_mask
          in
          Vm.get vm msf = v
      ]
  end.

Definition eq_ex (eqms : bool) (msf : option (funname * regvar * regvar * label)) (s : state) (t: state) :=
  [/\ st_mem s = st_mem t
    , if eqms then st_ms s = st_ms t else st_ms t
    & eq_vm_ex_cont msf (st_vm s) (st_vm t)
  ].

Definition cont_in_ra (f : funname) (vm : Vm.t) (c : continuation) : bool :=
  if Vm.get vm (ra f) is Vint z
  then z == to_Z f c.1.1.2
  else false.

Definition ret_eqms
  (f : funname) (t : lmachine) (tbl : seq continuation) : bool :=
  has (cont_in_ra f (st_vm (l_st t))) tbl.

Inductive compile_s : machine -> lmachine -> Prop :=
  | CompS_cont : forall s t,
    let: f := m_fn s in
    let: l := l_pc t in
    let: c := m_c s in
    compile_cont f l c ->
    eq_ex true None (m_st s) (l_st t) ->
    compile_callstack (st_ms (m_st s)) (l_st t) f (m_cs s) ->
    compile_s s t

  | CompS_jumpC : forall s t g lr l' c xi,
    let: f := m_fn s in
    let: l := l_pc t in
    let: rag := ra g in
    let: zl := Econst (to_Z g lr) in
    m_c s = Icall lr xi g :: c ->
    List.In (f, lr, xi, c) (contp g p) ->
    lp l = (Ljump C, [:: Lin g]) ->
    compile_call_cont xi rag zl lr l' ->
    compile_cont f l' c ->
    Vm.get (st_vm (l_st t)) (ra g) = (Vint (to_Z g lr)) ->
    eq_ex true None (m_st s) (l_st t) ->
    compile_callstack (st_ms (m_st s)) (l_st t) f (m_cs s) ->
    compile_s s t

  | CompS_upd : forall s t g lr l' msf,
    let: f := m_fn s in
    let: l := l_pc t in
    let: c := m_c s in
    let: lg := Lin g in
    let: rag := ra g in
    let: zl := Econst (to_Z g lr) in
    ~~ Sr.mem msf RA ->
    List.In (f, lr, Some msf, c) (contp g p) ->
    lp l = (Lupdate_msf C msf msf (Eop2 Oeq (Evar rag) zl), [::l']) ->
    compile_cont f l' c ->
    eq_ex true (Some (g, msf, rag, lr)) (m_st s) (l_st t) ->
    compile_callstack (st_ms (m_st s)) (l_st t) f (m_cs s) ->
    compile_s s t

  | CompSret : forall s t tbl,
    let: f := m_fn s in
    let: l := l_pc t in
    let: eqms := ret_eqms f t tbl in
    f <> p_entry_fn p ->
    incl tbl (contp f p) ->
    uniq tbl ->
    m_c s = [::] ->
    compile_r f l tbl ->
    eq_ex eqms None (m_st s) (l_st t) ->
    (~~ st_ms (m_st s) -> st_ms (l_st t) = ~~ eqms) ->
    compile_callstack (st_ms (m_st s)) (l_st t) f (m_cs s) ->
    compile_s s t

  | CompSfinal : forall s t,
    let: main := p_entry_fn p in
    m_fn s = main ->
    m_cs s = [::] ->
    l_pc t = Lret main ->
    compile_s s t
.

(* Directive and Leakage transformer *)

Definition Tdir (l : label) (d : directive) : seq directive :=
  match lp l with
  | (Ljump N, _) => [::]
  | (Lassign C _ _, _) => [::]
  | (Lupdate_msf C _ _ _, _) => [::]
  | (Ljump R, lr :: _) =>
      if label_lookup lr p is Some (f, _, xi, cont)
      then [:: Dreturn f lr xi cont ]
      else [:: d ]  (* dummy *)
  | (Lcjump R _, lr :: _) =>
    match d with
    | Dforce true =>
        if label_lookup lr p is Some (f, _, xi, cont)
        then [:: Dreturn f lr xi cont ]
        else [::d ] (* dummy *)
    | Dforce false => [::]
    | _ => [:: d] (* dummy *)
    end
  | _ => [::d]
  end.

Definition Tobs (l : label) (ra_vm:Vm.t) (O: seq observation) : observation :=
  match lp l with
  | (Ljump N, _) => Onone
  | (Lassign C _ _, _) => Onone
  | (Lupdate_msf C _ _ _, _) => Onone
  | (Ljump R, lr :: _) => Onone
  | (Lcjump R e, lr :: _) =>
    match eval ra_vm e with
    | Vbool b => Obranch b
    | _ => Onone (* dummy *)
    end
  | _ => head Onone O
  end.

Definition Tvm (l : label) (ra_vm:Vm.t) : Vm.t :=
  match lp l with
  | (Lassign C ra e, _) => Vm.set ra_vm ra (eval ra_vm e)
  | _ => ra_vm
  end.

Lemma eq_on_RA_nra x v vm ra_vm :
  ~~ Sr.mem x RA ->
  eq_on_RA vm ra_vm ->
  eq_on_RA (Vm.set vm x v) ra_vm.
Proof.
  move=> /negPf hnin heq y.
  rewrite Vm.get_set.
  case: eqP => [<- | hne]; last by apply heq.
  by rewrite hnin.
Qed.

Lemma eq_on_RA_ra x v vm ra_vm :
  eq_on_RA vm ra_vm ->
  eq_on_RA (Vm.set vm x v) (Vm.set ra_vm x v).
Proof.
  move => heq y; rewrite !Vm.get_set; case: eqP => // _.
  apply eq_val_refl.
Qed.

Context
  (cert : certificate)
  (htyp : typedp cert p)
  (p_lp : compile p lp Lin Lret ra to_Z RA)
  (hcchecks : compiler_checks p lp Lret ra to_Z RA)
.

Let hwfp := proj6_1 hcchecks.
Let ra_RA := proj6_2 hcchecks.
Let to_Z_inj := proj6_3 hcchecks.
Let no_rec := proj6_4 hcchecks.
Let is_call_ra_inj := proj6_5 hcchecks.
Let ret_entry := proj6_6 hcchecks.

Lemma contp_inj f g g' l xi xi' c c' :
  List.In (g, l, xi, c) (contp f p) ->
  List.In (g', l, xi', c') (contp f p) ->
  [/\ g = g', xi = xi' & c = c' ].
Proof.
  move=> /(label_lookup_l hwfp) h /(label_lookup_l hwfp). by rewrite h => -[].
Qed.

Lemma compile_cont_cat f c cont l l' :
  compile_c f l c cont l' ->
  compile_cont f l' cont ->
  compile_cont f l (c ++ cont).
Proof.
  move=> hc hcont; elim: c l hc=> [ | i c ih] l /compile_cI /=.
  + by move=> ?; subst l'.
  move=> [li hi /ih hc]; econstructor; eauto.
Qed.

Lemma hcomp_call_ret callee caller xi cont lr :
  List.In (caller, lr, xi, cont) (contp callee p) ->
  exists2 l',
    compile_call_cont xi (ra callee) (Econst (to_Z callee lr)) lr l'
    & compile_cont caller l' cont.
Proof.
  move=> /inP /mapP []/= [callee1 C]; rewrite mem_filter => /andP [] /= /eqP ? + ?.
  subst callee1 C => /flatten_mapP [caller1] _ /mapP []/= [callee1] [] [] l1 xi1 cont1 hin [?????].
  subst callee1 caller1 l1 xi1 cont1.
  have [hcomp _] := p_lp caller.
  have : compile_cont caller (Lret caller) [::] by constructor.
  rewrite -(cats0 cont).
  move: (p caller) (Lin caller) cont [::] (Lret caller) hcomp hin.
  set Pi := fun (i : instruction) =>
    forall (l:label) (cont cont' : code) (l' : label),
     compile_i caller l i cont' l' ->
     (callee, (lr, xi, cont)) \in all_conti i ->
     compile_cont caller l' cont' ->
     exists2 l' : label,
        compile_call_cont xi (ra callee) (Econst (to_Z callee lr)) lr l' & compile_cont caller l' (cont ++ cont').
  set Pc := fun (c : code) =>
    forall (l:label) (cont cont' : code) (l' : label),
     compile_c caller l c cont' l' ->
     (callee, (lr, xi, cont)) \in all_contc c ->
     compile_cont caller l' cont' ->
     exists2 l' : label,
        compile_call_cont xi (ra callee) (Econst (to_Z callee lr)) lr l' & compile_cont caller l' (cont ++ cont').
  apply: (code_rect (Pi:=Pi) (Pc:=Pc)) => //=.
  + move=> e c1 c0 hc1 hc0 l cont cont' l' /compile_iI [] _ [] l1 [] l0 [] l1' /= [] hl hcc1 hl1' hcc0.
    rewrite mem_cat => /orP [] hin hcompc.
    + by apply (hc1 _ _ _ _ hcc1 hin); apply: CompCont_jumpN hl1' hcompc.
    by apply (hc0 _ _ _ _ hcc0 hin).
  + move=> e c1 hc1 l cont_ cont' l' /compile_iI [] hdisj [] l1 [] l1' [] hl hcc1 hl1' /=.
    move=> /mapP [] /= [] f_ [] [] l_ xi_ cont hin [??? heq] hcompc; subst f_ l_ xi_ cont_.
    rewrite -catA /=; apply: (hc1 _ _ _ _ hcc1 hin).
    apply/(CompCont_jumpN hl1')/(CompCont_cons (l':=l')) => //.
    by apply: (CompWhile hdisj hl hcc1 hl1').
  + move=> lr' xi' g l cont cont' l' /compile_iI [] l1 [] hin hl hl1 hccc /= + hcompc.
    by rewrite mem_seq1 => /eqP [*]; subst g lr' xi' cont; exists l'.
  move=> i c hi hc l cont cont' l' /compile_cI [li] hci hcc /=.
  rewrite mem_cat => /orP []; last by apply: hc hcc.
  move=> /mapP [] [] g [] [] lr' xi' cont_ hin [????] hcompc; subst g lr' xi' cont; rewrite -catA.
  by apply/(hi _ _ _ _ hci hin)/(compile_cont_cat hcc hcompc).
Qed.

Lemma compile_callstack_nra sms x v st f cs:
  ~~ Sr.mem x RA ->
  compile_callstack sms st f cs ->
  compile_callstack sms (with_vm st (Vm.set (st_vm st) x v)) f cs.
Proof.
  move=> hnra; elim => {f cs}.
  + by move=> *; apply: CompCs_nil.
  + by apply CompCs_entry.
  move=> g xi cs f c lr lr' hL hcomp hget hcallcont _.
  apply: CompCs_cons hcallcont => //=.
  rewrite semantics_facts.set_neq //; apply /eqP => ?; subst x.
  by rewrite ra_RA in hnra.
Qed.

Lemma compile_callstack_write_mem ms st a i v f cs:
  compile_callstack ms st f cs ->
  compile_callstack ms (write_mem st a i v) f cs.
Proof.
  elim; first by constructor.
  + by apply CompCs_entry.
  move=> callee xi {}cs caller cont lr l' hin hcont hget hccont _.
  by apply: CompCs_cons hccont.
Qed.

Lemma compile_callstack_write_ra callee caller ms v st cs :
  is_call callee caller ->
  compile_callstack ms st caller cs ->
  compile_callstack ms (write_reg st (ra callee) v) caller cs.
Proof.
  move=> his hcs; elim: hcs his; first by constructor.
  + by move=> _; apply CompCs_entry.
  move=> g xi {}cs f cont lr l' hin hcont hget hccont _ ih his.
  econstructor; eauto => /=; last first.
  + by move/inP: hin => hin; apply/ih/Ctrans; eauto; econstructor; eauto.
  have /eqP hn := is_call_ra_inj his.
  by rewrite Vm.get_set (negbTE hn).
Qed.

Lemma compile_callstack_upd_ms ms st b f cs:
  compile_callstack ms st f cs ->
  compile_callstack (b || ms) (upd_ms st b) f cs.
Proof.
  elim.
  + by move=> ? ->; rewrite orbT; constructor.
  + by apply CompCs_entry.
  move=> callee xi {}cs caller cont lr l' hin hcont hget hccont _.
  by apply: CompCs_cons hccont.
Qed.

Lemma compile_callstack_with_ms sms t f cs b :
  compile_callstack sms t f cs ->
  compile_callstack sms (with_ms t b) f cs.
Proof. elim; by eeauto. Qed.

Lemma compile_cs_ret_eqms ms st f cs :
  f <> p_entry_fn p ->
  compile_callstack ms (l_st st) f cs ->
  ~~ms ->
  ret_eqms f st (contp f p).
Proof.
  move=> hentry hcs; case: hcs hentry => //; first by move=> ? ->.
  move=> {}f xi {}cs caller cont lr l' /inP hin _ hget _ _ _ _.
  apply/hasP.
  rewrite /cont_in_ra hget.
  by eeauto.
Qed.

Lemma notin_ret_eqms tbl f caller lr xi cont vm :
  (caller, lr, xi, cont) \in contp f p ->
  cont_in_ra f vm (caller, lr, xi, cont) ->
  incl tbl (contp f p) ->
  (caller, lr, xi, cont) \notin tbl ->
  ~~ has (cont_in_ra f vm) tbl.
Proof.
  move=> hlr hcont.
  elim: tbl => [// | /= [[[g lr'] xi'] cont'] tbl hind] /andP [hc hincl].
  rewrite in_cons !negb_or => /andP [hne hnin].
  rewrite {}hind // andbT.
  move: hcont.
  rewrite /cont_in_ra /=.
  case: Vm.get => //= _ /eqP ->.
  apply/negP => /eqP/to_Z_inj ?; subst lr'.
  move: hc hlr => /inP hc /inP hlr.
  have [???] := contp_inj hc hlr; subst g xi' cont'.
  by rewrite eqxx in hne.
Qed.

Lemma eq_ex_eval s t e :
  disjoint RA (free_variables e) ->
  eq_ex true None s t ->
  eval (st_vm s) e = eval (st_vm t) e.
Proof.
  move=> hdisj [] _ _ hms.
  apply eval_eq_on => x /Sr.mem_spec hin.
  apply/hms/negP => /Sr.mem_spec hin'.
  by apply/(hdisj x)/Sr.inter_spec.
Qed.

Lemma eq_ex_write_reg s t x v:
   eq_ex true None s t ->
   eq_ex true None (write_reg s x v)
                   (write_reg t x v).
Proof.
  move=> [] hmem hms hvm; split => // r hrin.
  by rewrite /write_reg !Vm.get_set; case: eqP => // _; apply hvm.
Qed.

Lemma eq_ex_write_mem s t a i v:
  eq_ex true None s t ->
  eq_ex true None (write_mem s a i v) (write_mem t a i v).
Proof. by move=> [] hmem hms hvm; split => //; rewrite /write_mem hmem. Qed.

Lemma eq_ex_upd_ms s t b :
  eq_ex true None s t ->
  eq_ex true None (upd_ms s b) (upd_ms t b).
Proof. by move=> [hmem hms hvm]; split => //=; rewrite hms. Qed.

Lemma compile_c_compile_cont l f c :
  compile_c f l c [::] (Lret f) ->
  compile_cont f l c.
Proof.
  move=> h. rewrite -(cats0 c). apply: (compile_cont_cat h). by constructor.
Qed.

Lemma compS_cat s t c cont l l' :
  compile_c (m_fn s) l c cont l' ->
  compile_cont (m_fn s) l' cont ->
  eq_ex true None (m_st s) (l_st t) ->
  compile_callstack (st_ms (m_st s)) (l_st t) (m_fn s) (m_cs s) ->
  compile_s (with_c s (c ++ cont)) (with_pc t l).
Proof.
  move=> hc hcont hex hcs.
  apply CompS_cont => //; apply: compile_cont_cat hc hcont.
Qed.

Lemma compiler_security_step_r sigma gamma ra_vm s t d o t' tbl :
  m_fn s <> p_entry_fn p ->
  incl tbl (contp (m_fn s) p) ->
  uniq tbl ->
  m_c s = [::] ->
  compile_r (m_fn s) (l_pc t) tbl ->
  eq_ex (ret_eqms (m_fn s) t tbl) None (m_st s) (l_st t) ->
  (~~ st_ms (m_st s) -> st_ms (l_st t) = ~~ ret_eqms (m_fn s) t tbl) ->
  compile_callstack (st_ms (m_st s)) (l_st t) (m_fn s) (m_cs s) ->
  typedm cert sigma gamma s ->
  synced sigma (st_vm (m_st s)) (st_ms (m_st s)) ->
  lstep lp t d o t' ->
  eq_on_RA (st_vm (l_st t)) ra_vm ->
  exists (s' : machine) (O : seq observation),
    [/\ sem p s (Tdir (l_pc t) d) O s', o = Tobs (l_pc t) ra_vm O
      , eq_on_RA (st_vm (l_st t')) (Tvm (l_pc t) ra_vm)
      & compile_s s' t'
    ].
Proof.
  move: tbl => /= tbl.
  move=> hnentry hincl huniq hcnil hcompr hex hms hcs htym hsync /lstepI.
  case: {-2}_ _ / hcompr (erefl (l_pc t)) hex hms hincl huniq.

  (* The return table has exactly one entry. *)
  + move=> l caller xi cont lr hlr hpc ? hex hms _ _; subst l; rewrite hpc.
    move=> [???] heqra; subst.
    rewrite /Tdir /Tobs /Tvm /= hpc.
    move: (hlr) => /(label_lookup_l hwfp) ->.
    have [l' hcallcont hccont] := hcomp_call_ret hlr.
    set s' :=
      if is_speculative_ret (m_cs s) caller lr cont
      then m_after_ret_s s caller xi cont
      else m_after_ret_n s caller cont (drop 1 (m_cs s)).
    exists s', [:: Onone ].
    subst s'.
    split=> //.
    + apply: sem_step1. apply: step_ret => //. by case: is_speculative_ret.

    move: hcs => /compile_callstackI [|[] //|].

    (* Callstack is empty and the source is misspeculating. *)
    + move=> [hsms hscs]; rewrite hscs /=.
      case: xi hlr hex hcallcont hms => [msf|] /= hlr hex hcallcont hms.
      + move: hcallcont => [hmsfnra hplr].
        apply: CompS_upd; eauto=> /=.
        + move: hex.
          rewrite orbF => -[hmem hems hvm]; split => //=.
          by case: ifP hems => [ _ <- | _ ->].
        split.
        + by move=> r hnRA /eqP hne; rewrite Vm.get_set (negbTE hne); apply hvm.
        move: htym => [theta0 []]; rewrite hcnil => /typedcI [].
        move: (final_mss_updated htyp hlr) =>
          /isSome_exists [_ /mss_callI [-> _]] /mss_le_MSSupdatedI ? _ _;
          subst sigma.
        move: hsync => /andP [].
        rewrite hsms eq_sym => /eqP /eqP hmsf _.
        by rewrite -(hvm _ hmsfnra) hmsf if_same set_eq.
        + by constructor.
      subst l'; apply: CompS_cont => //=; last by apply CompCs_nil.
      move: hex; rewrite orbF => -[hmem hems hvm]; split => //=.
      by case: ifP hems => [ _ <- | _ ->].

    (* Callstack is not empty. *)
    move=> [xi' [cs [f [c [lr' [l0 [hlr'c hc hra hcont hcompilecs hcs]]]]]]].
    rewrite hcs /=.

    case: (boolP (is_speculative_ret _ _ _ _));
      rewrite /is_speculative_ret /= => hspec.

      (* The directive is a speculative return. *)
    + move: hex => [] /=.
      rewrite /cont_in_ra orbF hra.
      case: (boolP (_ == _)) => [|/negPf hencode].
      + move=> /eqP /to_Z_inj ?; subst.
        have [???] := contp_inj hlr'c hlr; subst f xi' c.
        by rewrite eqxx in hspec.
      (* We know that [ms_t] is set. *)
      move=> hmem hsms hvm.
      clear hms.

      case: xi hlr hcallcont hencode => [msf|] /= hlr hcallcont hencode.
      + move: hcallcont => [hmsfnra hplr].
        apply: CompS_upd; eauto=> /=.
        split=> //=.
        split.
        + by move=> r hnRA /eqP hne; rewrite Vm.get_set (negbTE hne); apply hvm.
        move: htym => [theta0 []]; rewrite hcnil => /typedcI [].
        move: (final_mss_updated htyp hlr) =>
          /isSome_exists [_ /mss_callI [-> _]] /mss_le_MSSupdatedI ? _ _;
          subst sigma.
        by rewrite hra hencode /= set_eq.
        + by constructor.
      by subst l'; apply: CompS_cont => //=; constructor.

    (* The directive is a normal return. *)
    rewrite drop0.
    move: hspec => /negPn /eqP [???]; subst f lr' c.
    have [_ ? _] := contp_inj hlr hlr'c; subst xi'.
    clear hlr'c.
    move: hex => [] /=.
    rewrite /cont_in_ra orbF hra eqxx => hmem hsms hvm.
    case: xi hlr hcallcont hms hcont => [msf|] /= hlr hcallcont hms hcont.
    + move: hcallcont => [hmsfnra hplr].
      apply: CompS_upd; eauto=> /=.
      + split=> //=.
        split.
        + move=> r hnRA /eqP hne. exact: hvm.
        move: htym => [theta0 []]; rewrite hcnil => /typedcI [].
        move: (final_mss_updated htyp hlr) =>
          /isSome_exists [_ /mss_callI [-> _]] /mss_le_MSSupdatedI ? _ _;
          subst sigma.
        by rewrite hra /= eqxx /= hvm.
    by apply: CompS_cont => //=; subst.

  (* The return table has more than one entry. *)
  move=> l caller xi cont rest lr l0 hlr hpc hrest ? hex hmsret hincl huniq;
    subst l.
  rewrite /Tdir /Tobs /Tvm hpc => -[b [b' []]] /= hb' ??? hvmra; subst d o t'.
  have := hvmra (ra (m_fn s)).
  rewrite ra_RA => /eqP <-.
  move: (hlr) => /(label_lookup_l hwfp) -> /=.
  have [l' hcallcont hccont] := hcomp_call_ret hlr.
  move: hincl => /andP [] _ hincl.
  move: huniq => /andP [hnin huniq].
  move: hb' hex.
  rewrite /= /cont_in_ra /=.
  case hra: Vm.get => [zl | // | //] [?] hex; subst b'.
  case: b; first last.

  (* Case: skip this cjump. *)
  + exists s, [::].
    case: (zl =P _) hex => /= [hzl | hret] [hmem hms hvmnra].

    (* Case: we misspeculate. *)
    + have hcontinra :
        cont_in_ra (m_fn s) (st_vm (l_st t)) (caller, lr, xi, cont).
      + by rewrite /cont_in_ra hra hzl eqxx.
      move: hlr => /inP hlr.
      move: (notin_ret_eqms hlr hcontinra hincl hnin) => /negPf hreteqms.
      split=> //=; first by constructor.
      apply: (CompSret _ hincl) => //=.
      + by rewrite /ret_eqms /= hreteqms.
      + by rewrite /ret_eqms /= hreteqms.
      exact: compile_callstack_with_ms.

    (* Case: we don't misspeculate. *)
    split=> //=; first by constructor.
    apply: (CompSret _ hincl) => //=.
    + move: hms. rewrite /ret_eqms /=. case: has => //. by move=> -> /negPf ->.
    exact: compile_callstack_with_ms.

  (* Case: Perform the return. *)
  set s' :=
    if is_speculative_ret (m_cs s) caller lr cont
    then m_after_ret_s s caller xi cont
    else m_after_ret_n s caller cont (drop 1 (m_cs s)).
  exists s', [:: Onone ].
  subst s'.
  split=> //.
  + apply: sem_step1. apply: step_ret => //. by case: is_speculative_ret.
  move: hcs => /compile_callstackI [|[] //|].

  (* Callstack is empty and the source is misspeculating. *)
  + clear hmsret.
    move=> [hsms hcs].
    rewrite hcs /=.
    case: xi hlr hex hcallcont hnin => [msf|] /= hlr hex hcallcont hin.
    + move: hcallcont => [hmsfnra hplr].
      apply: CompS_upd; eauto=> /=.
      + move: hex => [hmem hms hnra].
        split=> //=.
        + move: hms. rewrite hsms. by case: eqP.
        split.
        + move=> ?? /eqP /negPf hmsf. rewrite Vm.get_set hmsf. by eauto.
        rewrite set_eq -(hnra _ hmsfnra).
        move: htym => [theta0 []]; rewrite hcnil => /typedcI [].
        move: (final_mss_updated htyp hlr) =>
          /isSome_exists [_ /mss_callI [-> _]] /mss_le_MSSupdatedI ? _ _;
          subst sigma.
        move: hsync => /andP [] /eqP.
        rewrite hsms => /esym /eqP -> _.
        by rewrite if_same.
      by constructor.
    subst l'; apply: CompS_cont => //=; last by apply CompCs_nil.
    move: hex => [hmem hms hnra].
    split=> //=.
    move: hms; rewrite hsms; by case: eqP.

  (* Callstack is not empty. *)
  move=> [xi' [cs [f [c [lr' [l1 [hlr'c hc hra' hcont hcompilecs hcs]]]]]]].
  rewrite hcs /=.
  move: hra'.
  rewrite hra => -[?]; subst zl.

  case: (boolP (is_speculative_ret _ _ _ _));
    rewrite /is_speculative_ret /= => hspec.

  (* The directive is a speculative return. *)
  + move: hex => [] /=.
    case: (boolP (_ == _)) => [|/negPf hencode].
    + move=> /eqP /to_Z_inj ?; subst.
      have [???] := contp_inj hlr'c hlr; subst f xi' c.
      by rewrite eqxx in hspec.
    (* We know that [ms_t] is set. *)
    move=> hmem hsms hvm.
    clear hmsret.

    case: xi hlr hcallcont hencode hnin => [msf|] /= hlr hcallcont hencode hnin.
    + move: hcallcont => [hmsfnra hplr].
      apply: CompS_upd; eauto=> /=.
      split=> //=.
      split.
      + by move=> r hnRA /eqP hne; rewrite Vm.get_set (negbTE hne); apply hvm.
      move: htym => [theta0 []]; rewrite hcnil => /typedcI [].
      move: (final_mss_updated htyp hlr) =>
        /isSome_exists [_ /mss_callI [-> _]] /mss_le_MSSupdatedI ? _ _;
        subst sigma.
      by rewrite hra hencode /= set_eq.
      + by constructor.
    by subst l'; apply: CompS_cont => //=; constructor.

  (* The directive is a normal return. *)
  rewrite drop0.
  move: hspec => /negPn /eqP [???]; subst f lr' c.
  have [_ ? _] := contp_inj hlr hlr'c; subst xi'.
  clear hlr'c.
  move: hex => [hmem hsms hvm].
  case: xi hlr hcallcont hcont hmsret hnin =>
    [msf|] /= hlr hcallcont hcont hmsret hnin.
  + move: hcallcont => [hmsfnra hplr].
    apply: CompS_upd; eauto=> /=.
    + split=> //=.
      + move: hsms. by case: eqP.
      split.
      + move=> r hnRA /eqP hne. exact: hvm.
      move: htym => [theta0 []]; rewrite hcnil => /typedcI [].
      move: (final_mss_updated htyp hlr) =>
        /isSome_exists [_ /mss_callI [-> _]] /mss_le_MSSupdatedI ? _ _;
        subst sigma.
      by rewrite hra /= eqxx /= hvm.
    exact: compile_callstack_with_ms.
  subst l'; apply: CompS_cont => //=.
  + move: hsms. by case: eqP.
  exact: compile_callstack_with_ms.
Qed.


Lemma compiler_security_step sigma gamma ra_vm s t d o t':
  compile_s s t ->
  typedm cert sigma gamma s ->
  synced sigma (st_vm (m_st s)) (st_ms (m_st s)) ->
  lstep lp t d o t' ->
  eq_on_RA (st_vm (l_st t)) ra_vm ->
  let: l := l_pc t in
  exists s' O,
    [/\ sem p s (Tdir l d) O s'
      , o = Tobs l ra_vm O
      , eq_on_RA (st_vm (l_st t')) (Tvm l ra_vm)
      & compile_s s' t'].
Proof.
  case=> {}s {}t.
  (* Case: compile_cont *)
  + move=> hcont heqex;
    case: (heqex) => hmem hms hvm.
    case: {-1}_ {-1}_ / hcont (erefl (l_pc t)) (erefl (m_c s)).
    + move=> hpc hmc hcs htym hsync hlstep heqra.
      case: (m_fn s =P p_entry_fn p) => [hentry | hnentry].
      (* The state t is final we can't progress *)
      + by have /lstepI := hlstep; rewrite hpc hentry ret_entry.
      have :=
        compiler_security_step_r
          hnentry _ _ hmc _ _ _ hcs htym hsync hlstep heqra.
      rewrite -hpc; apply.
      + by apply /inclP/List.incl_refl.
      + exact: (uniq_contp _ hwfp).
      + by have [_] := p_lp (m_fn s); rewrite hpc; apply.
      + split => //; case: ifPn => //.
        rewrite -hms; have := compile_cs_ret_eqms hnentry hcs.
        by case: st_ms => // ->.
      move=> hsms.
      by rewrite -hms (compile_cs_ret_eqms hnentry hcs hsms) (negbTE hsms).
    + move=> i c l l' hi hc ? hmc hcs htym hsync hlstep heqra; subst l.
      case: i {hi hlstep} (compile_iI hi) (lstepI hlstep) hmc =>
        [ x e
        | x a e
        | a e x
        | msf
        | msf' msf e
        | x y msf
        | e c1 c0
        | e c1
        | lcont xi g
        ] + + hmc.

    (* Subcase: Assignment. *)
    + move=> [hpc hx he];
      rewrite /Tdir /Tobs /Tvm hpc /= => -[???]; subst d o t'.
      exists (m_after_assign s c x e), [:: Onone ].
      split=> //.
      + by eeauto.
      + by apply eq_on_RA_nra.
      apply CompS_cont => //=; last by apply compile_callstack_nra.
      by rewrite (eq_ex_eval he heqex); apply eq_ex_write_reg.

    (* Subcase: Normal load. *)
    + move=> [hpc hx he].
      rewrite /Tdir /Tobs /Tvm hpc /= => -[] i [] b [] j [] hi hinb hspec ??;
        subst.
      exists (m_after_load s c x b j), [:: Oaddr a i ]; split => //.
      + apply/sem_step1/step_load => //; first by rewrite hmc.
        + by rewrite (eq_ex_eval he heqex).
        by rewrite hms.
      + by apply: eq_on_RA_nra heqra.
      apply: CompS_cont => //=; last by apply compile_callstack_nra.
      by rewrite hmem; apply eq_ex_write_reg.

    (* Subcase: Store. *)
    + move=> [hpc hx he].
      rewrite /Tdir /Tobs /Tvm hpc /= => -[] i [] b [] j [] hi hinb hspec ??;
        subst.
      exists (m_after_store s c b j x), [:: Oaddr a i]; split => //.
      + apply/sem_step1/step_store => //; first by rewrite hmc.
        + by rewrite (eq_ex_eval he heqex).
        + by rewrite hms.
      apply: CompS_cont => //=; last by apply compile_callstack_write_mem.
      by rewrite hvm //; apply eq_ex_write_mem.

    (* Subcase: Init MSF. *)
    + move=> [hpc hmsf].
      rewrite /Tdir /Tobs /Tvm hpc /= => -[hmst ???]; subst d o t'.
      exists (m_after_init_msf s c msf), [:: Onone]; split => //.
      + by apply: sem_step1; constructor => //; rewrite hms.
      + by apply: eq_on_RA_nra.
      apply: CompS_cont => //=; last by apply compile_callstack_nra.
      by apply eq_ex_write_reg.

    (* Subcase: Update MSF. *)
    + move=> [hpc hmsf' hmsf he].
      rewrite /Tdir /Tobs /Tvm hpc /= => -[???]; subst d o t'.
      exists (m_after_update_msf s c msf' msf e), [::Onone]; split => //.
      + by apply sem_step1; constructor.
      + by apply: eq_on_RA_nra.
      apply: CompS_cont => //=; last by apply compile_callstack_nra.
      rewrite /st_after_update_msf (eq_ex_eval he heqex) hvm //.
      by apply eq_ex_write_reg.

    (* Subcase: Protect. *)
    + move=> [hpc hx hy hmsf].
      rewrite /Tdir /Tobs /Tvm !hpc /= => -[???]; subst d o t'.
      exists (m_after_protect s c x y msf), [::Onone]; split => //.
      + by apply sem_step1; constructor.
      + by apply: eq_on_RA_nra.
      apply: CompS_cont => //=; last by apply compile_callstack_nra.
      rewrite /st_after_protect !hvm //.
      by apply eq_ex_write_reg.

    (* Subcase: Conditional. *)
    + move=> [he [l1 [l0 [l1' [hpc hcc1 hl1' hcc0]]]]].
      rewrite /Tdir /Tobs /Tvm !hpc /= => -[b [b' [hb ???]]]; subst d o t'.
      set c' := (if b then c1 else c0) ++ c.
      set st' := with_ms (m_st s) ((b != b') || st_ms (m_st s)).
      exists (with_c (semantics.with_st s st') c'), [::Obranch b']; split => //.
      + apply/sem_step1/step_if; first by rewrite hmc.
        by rewrite (eq_ex_eval _ heqex).
      have {heqex} := eq_ex_upd_ms (b != b') heqex.
      subst c' st'; case: b => /= heqex.
      + apply: compS_cat => //=; first by apply: hcc1.
        + by apply: CompCont_jumpN; eauto.
        by apply compile_callstack_upd_ms.
      apply: compS_cat => //=; first by apply: hcc0.
      + done.
      by apply compile_callstack_upd_ms.

    (* Subcase: Loop. *)
    + move=> [he [l1 [l1' [hpc hcc1 hl1']]]].
      rewrite /Tdir /Tobs /Tvm !hpc /= => -[b [b' [hb ???]]]; subst d o t'.
      set c' := if b then c1 ++ (m_c s) else c.
      set st' := with_ms (m_st s) ((b != b') || st_ms (m_st s)).
      exists (with_c (semantics.with_st s st') c'), [::Obranch b']; split => //.
      + apply/sem_step1/step_while; first by rewrite hmc.
        by rewrite (eq_ex_eval _ heqex).
      have {heqex} := eq_ex_upd_ms (b != b') heqex.
      subst c' st'; case: b => heqex.
      + rewrite hmc; apply: compS_cat => //=; first by apply: hcc1.
        + apply: CompCont_jumpN; first apply hl1'.
          apply: CompCont_cons; last by apply hc.
          by apply: CompWhile hpc hcc1 hl1'.
        by apply compile_callstack_upd_ms.
      by apply: CompS_cont => //=; apply: compile_callstack_upd_ms.

    (* Subcase: Call. *)
    + move=> [l0 [hcont hpc hcall hupdate]].
      rewrite /Tdir /Tobs /Tvm hpc /= => -[???]; subst d o t'.
      exists s, [::]; split => //.
      + by apply sem_done.
      + by apply: eq_on_RA_ra.
      apply: CompS_jumpC => //.
      + by rewrite hmc.
      + by apply hcont.
      + done.
      + by apply hupdate.
      + done.
      + by rewrite /l_after_assign /= Vm.get_set eqxx.
      + split => // r hin; rewrite Vm.get_set; case: eqP => heq; last by apply hvm.
        by subst r; rewrite ra_RA in hin.
      rewrite /l_after_assign /=.
      by apply compile_callstack_write_ra => //; econstructor; apply/inP/hcont.

  (* Case: Normal jump. *)
  + move=> cont l l' hpc hcomp ?? hcs htym hsync /lstepI; subst l cont; rewrite hpc.
    move=> [???] heqra; subst; exists s, [::].
    rewrite /Tdir /Tobs /Tvm hpc; split => //; first by constructor.
    by apply CompS_cont.

  (* Case: jump_call. *)
  + move=> g lr l0 c xi hmc hcont hpc hccont hcomp hrag hex hcs htym hsync
      /lstepI; rewrite hpc.
    move=> [???] heqra; subst.
    rewrite /Tdir /Tobs /Tvm hpc.
    exists (m_after_call s c g (p g) lr), [::Onone]; split => //.
    + apply: (sem_step1 (m':= m_after_call s c g (p g) lr)).
      by apply (step_call p (xi:=xi)).
    have [hcg _] := p_lp g.
    apply: CompS_cont => //=.
    + exact: compile_c_compile_cont.
    by apply: (CompCs_cons (xi:= xi) (lr:=lr) (l':= l0)).

  (* Case: update_msf after call *)
  + move=> g lr l' msf hnin hL hpc hccont hex hcs htym hsync /lstepI; rewrite hpc.
    move=> [???] heqra; subst.
    rewrite /Tdir /Tobs /Tvm hpc; exists s, [::]; split => //; first by constructor.
    + by apply eq_on_RA_nra.
    apply CompS_cont => //=; last by apply : compile_callstack_nra hnin hcs.
    case: hex => hmem hms [] hget hmsf; split => //= x hxra.
    by rewrite Vm.get_set; case: eqP => [<- | hneq] //; apply hget.

  (* The rest of the cases are in the return table. *)
  + by apply: compiler_security_step_r.

  (* Final state. *)
  move=> hfn hcd hpc _ _ /lstepI. by rewrite hpc ret_entry.
Qed.

(* ---------------------------------------------------------------------------------------- *)
(* Do the same for many steps                                                               *)

Definition next_label l d :=
  match lp l, d with
  | (_, [:: l1; l0]), Dforce b => if b then l1 else l0
  | (_, ls), _ => head (Lret (p_entry_fn p)) ls
  end.

Fixpoint Tdirs (l : label) (Dt : seq directive) : seq directive :=
  match Dt with
  | [::] => [::]
  | d :: Dt => Tdir l d ++ Tdirs (next_label l d) Dt
  end.

Fixpoint Tobss (l : label) (Dt : seq directive) (ra_vm:Vm.t) (Os: seq observation) : seq observation :=
  match Dt with
  | [::] => [::]
  | d :: Dt =>
    let sd := Tdir l d in
    let ot := Tobs l ra_vm (take (size sd) Os) in
    ot :: Tobss (next_label l d) Dt (Tvm l ra_vm) (drop (size sd) Os)
  end.

Lemma lsem_next_label t dt o t':
  lstep lp t dt o t' ->
  l_pc t' = next_label (l_pc t) dt.
Proof.
  move=> /lstepI; rewrite /next_label; case (lp (l_pc t)).
  move=>
    [an x e | x a e | a e x | msf | an msf msf' e | x y msf | an | an e ]
    [] // l1 [] //;
    try by move=> [_ _ ->].
  + by move=> [] i [] b [] j [] ???? ->.
  + by move=> [] i [] b [] j [] ???? ->.
  + by move=> [_ _ _ ->].
  by move=> l0 [] // [b] [b'] [_ -> _ ->].
Qed.

Lemma compiler_security_sem sigma gamma ra_vm s t Dt Ot t':
  lsem lp t Dt Ot t' ->
  compile_s s t ->
  typedm cert sigma gamma s ->
  synced sigma (st_vm (m_st s)) (st_ms (m_st s)) ->
  eq_on_RA (st_vm (l_st t)) ra_vm ->
  let: l := l_pc t in
  exists s' Os,
    sem p s (Tdirs l Dt) Os s' /\
    Ot = Tobss l Dt ra_vm Os.
Proof.
  move=> hsem.
  elim: hsem s sigma gamma ra_vm => {t Dt Ot t'} /=.
  + by move=> t s sigma gamma ra_vm hcomp _ _ _; exists s, [::]; split => //; constructor.
  move=> t t' t'' dt ot Dt Ot hlstep hlsem ih s sigma gamma ra_vm hcomp htym hsync heqra.
  have [s' [Os' [hsem' hot heqra' hcomp']]]:= compiler_security_step hcomp htym hsync hlstep heqra.
  have [sigma' [gamma' [htym' hsync']]]:= typedm_synced_sem htyp hsem' htym hsync.
  have [s'' [Os'' [hsem'' hOt]]] := ih _ _ _ _ hcomp' htym' hsync' heqra'.
  subst ot Ot; exists s'', (Os' ++ Os''); split.
  + by rewrite -(lsem_next_label hlstep); apply: sem_cat hsem''.
  by rewrite (size_obs hsem') take_size_cat // -(lsem_next_label hlstep) drop_size_cat.
Qed.

Lemma compile_s_initial s t :
  is_initial_machine p s ->
  is_initial_lmachine Lin p t ->
  m_st s = l_st t ->
  compile_s s t.
Proof.
  move=> /and3P [] /eqP hc /eqP hf /eqP hcs /eqP hpc hst.
  apply: CompS_cont.
  - apply: compile_c_compile_cont.
    rewrite hpc hc hf.
    by have [? _] := p_lp (p_entry_fn p).
  - by rewrite hst.
  rewrite hcs hf.
  exact: CompCs_entry.
Qed.

Lemma is_initial_machineP (p' : program) st :
  let: m :=
    {|
      m_c := p' (p_entry_fn p');
      m_fn := p_entry_fn p';
      m_cs := [::];
      m_st := st;
    |}
  in
  is_initial_machine p' m.
Proof. by rewrite /is_initial_machine /= !eqxx. Qed.

Lemma compiler_soundness :
  let: gamma := cert_ctx (cert (p_entry_fn p)) in
  let: phi := l_initial_phi Lin RA p gamma in
  wfcert cert p ->
  l_speculative_constant_time phi lp.
Proof.
  move=> hwf Dt os1 os2 t1 t2 t1' t2' [hpc1 hpc2 hinit_phi heqra] hlsem1 hlsem2.
  have hinit1 := is_initial_machineP p (l_st t1).
  have hcomp1 := compile_s_initial hinit1 hpc1 erefl.
  have hty1 := typedm_initial_machine htyp hinit1.
  have /(_ (st_vm (l_st t2))) [] := compiler_security_sem hlsem1 hcomp1 hty1.
  - by rewrite /synced /= wfcertP.
  - done.
  move=> s2 [Os] [] hsem1 ->.
  have hinit2 := is_initial_machineP p (l_st t2).
  have hcomp2 := compile_s_initial hinit2 hpc2 erefl.
  have hty2 := typedm_initial_machine htyp hinit2.
  have /(_ (st_vm (l_st t2))) [] := compiler_security_sem hlsem2 hcomp2 hty2.
  - by rewrite /synced /= wfcertP.
  - by move=> ?; apply eq_val_refl.
  move=> s2' [Os'] [] hsem2 ->.
  move: hpc2 hpc1 hsem2 => /eqP -> /eqP <- hsem2.
  by rewrite (typedp_soundness hwf htyp _ hsem1 hsem2).
Qed.

End PROOF.
