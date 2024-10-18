From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  semantics
  syntax
  syntax_facts
  utils
  utils_facts
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma with_ms_id st :
  with_ms st (st_ms st) = st.
Proof. by move: st => []. Qed.

Lemma set_eq vm x v :
  Vm.get (Vm.set vm x v) x = v.
Proof. by rewrite Vm.get_set eqxx. Qed.

Lemma set_neq vm x y v :
  x != y
  -> Vm.get (Vm.set vm x v) y = Vm.get vm y.
Proof. by rewrite Vm.get_set => /negPf ->. Qed.

Lemma eval_set vm e x v' :
  ~~ Sr.mem x (free_variables e)
  -> eval (Vm.set vm x v') e = eval vm e.
Proof.
  elim: e => [// | // | y | op e hind | op e0 hind0 e1 hind1].
  - rewrite Sr.F.singleton_b Sr.eqbP eq_sym => ?. by rewrite /= set_neq.
  - case: op => /= hx; by erewrite hind.
  rewrite Sr.F.union_b -/free_variables.
  case: op => /= /norP [??]; by rewrite hind0 // hind1.
Qed.

Definition eq_on (s : Sr.t) (vm vm' : Vm.t) : Prop :=
  forall x, Sr.mem x s -> Vm.get vm x = Vm.get vm' x.

Lemma eq_on_cat s0 s1 vm vm' :
  eq_on (Sr.union s0 s1) vm vm'
  -> eq_on s0 vm vm' /\ eq_on s1 vm vm'.
Proof.
  move=> h. split=> y hy; apply: h; by rewrite Sr.F.union_b hy // orbT.
Qed.

Lemma eval_eq_on vm vm' e :
  eq_on (free_variables e) vm vm'
  -> eval vm e = eval vm' e.
Proof.
  elim: e => [// | // | x | op e hind | op e0 hind0 e1 hind1] /=.
  - move=> -> //. by rewrite Sr.F.singleton_b Sr.eqbP eqxx.
  - by move=> /hind ->.
  by move=> /eq_on_cat [] /hind0 -> /hind1 ->.
Qed.

Lemma stepI p m d o m' :
  let: st := m_st m in
  step p m d o m'
  -> match d, m_c m with
     | Dstep, Iassign x e :: c =>
         [/\ o = Onone
           & m' = m_after_assign m c x e
         ]

     | Dstep, Iload x a e :: c =>
         exists i,
           [/\ eval (st_vm st) e = Vint i
             , in_bounds a i
             , o = Oaddr a i
             & m' = m_after_load m c x a i
           ]

     | Dmem b j, Iload x a e :: c =>
         exists i,
           [/\ eval (st_vm st) e = Vint i
             , ~~ in_bounds a i
             , in_bounds b j
             , st_ms st
             , o = Oaddr a i
             & m' = m_after_load m c x b j
           ]

     | Dstep, Istore a e x :: c =>
         exists i,
           [/\ eval (st_vm st) e = Vint i
             , in_bounds a i
             , o = Oaddr a i
             & m' = m_after_store m c a i x
           ]

     | Dmem b j, Istore a e x :: c =>
         exists i,
           [/\ eval (st_vm st) e = Vint i
             , ~~ in_bounds a i
             , in_bounds b j
             , st_ms st
             , o = Oaddr a i
             & m' = m_after_store m c b j x
           ]

     | Dstep, Iinit_msf msf :: c =>
         [/\ ~~ st_ms (m_st m)
           , o = Onone
           & m' = m_after_init_msf m c msf
         ]

     | Dstep, Iupdate_msf x y e :: c =>
         [/\ o = Onone
           & m' = m_after_update_msf m c x y e
         ]

     | Dstep, Iprotect x y msf :: c =>
         [/\ o = Onone
           & m' = m_after_protect m c x y msf
         ]

     | Dforce b, Iif e c0 c1 :: c =>
         exists b',
           let: st := m_st m in
           [/\ eval (st_vm st) e = Vbool b'
             , o = Obranch b'
             & let: c' := (if b then c0 else c1) ++ c in
               let: st' := with_ms st ((b != b') || st_ms st) in
               m' = with_st (with_c m c') st'
           ]

     | Dforce b, Iwhile e c0 :: c =>
         exists b',
           let: st := m_st m in
           [/\ eval (st_vm (m_st m)) e = Vbool b'
             , o = Obranch b'
             & let: c' := if b then c0 ++ (m_c m) else c in
               let: st' := with_ms st ((b != b') || st_ms st) in
               m' = with_st (with_c m c') st'
           ]

     | Dstep, Icall l xi f :: c =>
         [/\ o = Onone
           & m' = m_after_call m c f (p f) l
         ]

     | Dreturn f l xi c, [::] =>
         [/\ o = Onone
           & if is_speculative_ret (m_cs m) f l c
             then
               [/\ List.In (f, l, xi, c) (contp (m_fn m) p)
                 & m' = m_after_ret_s m f xi c
               ]
             else m' = m_after_ret_n m f c (drop 1 (m_cs m))
         ]

     | _, _ => False
     end.
Proof. case=> -[??? [???]] /= *; subst; by eeauto. Qed.

Lemma semI p m ds os m' :
  sem p m ds os m'
  -> match ds with
     | [::] => m = m' /\ os = [::]
     | d :: ds' =>
         exists o os',
           os = o :: os' /\ exists2 mi, step p m d o mi & sem p mi ds' os' m'
     end.
Proof. case; by eeauto. Qed.

Lemma sem_step1 p m d o m' :
  step p m d o m' ->
  sem p m [:: d ] [:: o ] m'.
Proof. by eeauto. Qed.

Lemma sem_cat p m m' m'' D D' O O' : 
  sem p m D O m' ->
  sem p m' D' O' m'' ->
  sem p m (D ++ D') (O ++ O') m''.
Proof. by elim => //= > hstep _ h /h; econstructor; eauto. Qed.

Lemma size_obs p m D O m' : sem p m D O m' -> size D = size O.
Proof. by elim => //= > _ _ ->. Qed.
