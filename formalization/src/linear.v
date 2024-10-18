From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  syntax
  semantics
  security
  typesystem
  utils
  utils_facts
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.


(* -------------------------------------------------------------------------- *)
(* Syntax. *)
(* -------------------------------------------------------------------------- *)

Variant annot :=
  | N
  | C
  | R.

Inductive linstr :=
  | Lassign     of annot  & regvar & expression
  | Lload       of regvar & arrvar & expression
  | Lstore      of arrvar & expression & regvar
  | Linit_msf   of regvar
  | Lupdate_msf of annot  & regvar & regvar & expression
  | Lprotect    of regvar & regvar & regvar
  | Ljump       of annot
  | Lcjump      of annot  & expression.

Definition lprogram := label -> linstr * list label.

(* Semantics *)

Record lmachine :=
  {
    l_pc : label;
    l_st : state;
  }.

Definition with_pc (m : lmachine) (l : label) : lmachine :=
  {|
    l_pc := l ;
    l_st := l_st m;
  |}.

Definition with_st (m : lmachine) (st : state) : lmachine :=
  {|
    l_pc := l_pc m;
    l_st := st;
  |}.


(* -------------------------------------------------------------------------- *)
(* Small step semantics. *)

Definition l_after_assign m l x e :=
  let st := l_st m in
  let v := eval (st_vm st) e in
  let st' := write_reg st x v in
  with_pc (with_st m st') l.

Definition l_after_init_msf m l msf :=
  let st' := write_reg (l_st m) msf msf_nomask in
  with_pc (with_st m st') l.

Definition l_after_update_msf m l x y e :=
  let st' := st_after_update_msf (l_st m) x y e in
  with_pc (with_st m st') l.

Definition l_after_protect m l x y msf :=
  let st' := st_after_protect (l_st m) x y msf in
  with_pc (with_st m st') l.

Definition l_after_load m l x a i :=
  let st := l_st m in
  let v := Mem.read (st_mem st) a i in
  let st' := write_reg st x v in
  with_pc (with_st m st') l.

Definition l_after_store m l a i x :=
  let st := l_st m in
  let v := Vm.get (st_vm st) x in
  let st' := write_mem st a i v in
  with_pc (with_st m st') l.

(* The rules for unsafe loads and stores require that the misspeculation status
   is set, because we assume that the program is sequentially safe, and
   therefore unsafe memory accesses must happen under misspeculation. *)

Definition upd_ms (st:state) (b:bool) : state :=
  with_ms st (b || st_ms st).

Variant lstep
  (p : lprogram) : lmachine -> directive -> observation -> lmachine -> Prop :=
  | lstep_assign :
    forall a m x e l',
      p (l_pc m) = (Lassign a x e, [::l'])
      -> lstep p m Dstep Onone (l_after_assign m l' x e)

  | lstep_load_n :
    forall m x a e l' i,
      let: st := l_st m in
      let: m' := l_after_load m l' x a i in
      p (l_pc m) = (Lload x a e, [::l'])
      -> eval (st_vm st) e = Vint i
      -> in_bounds a i
      -> lstep p m Dstep (Oaddr a i) m'

  | lstep_load_s :
    forall m x a e l' i b j,
      let: st := l_st m in
      let: m' := l_after_load m l' x b j in
      p (l_pc m) = (Lload x a e, [::l'])
      -> eval (st_vm st) e = Vint i
      -> ~~ in_bounds a i
      -> in_bounds b j
      -> st_ms st
      -> lstep p m (Dmem b j) (Oaddr a i) m'

  | lstep_store_n :
    forall m a e x l' i,
      let: st := l_st m in
      let: m' := l_after_store m l' a i x in
      p (l_pc m) = (Lstore a e x, [:: l'])
      -> eval (st_vm st) e = Vint i
      -> in_bounds a i
      -> lstep p m Dstep (Oaddr a i) m'

  | lstep_store_s :
    forall m a e x l' i b j,
      let: st := l_st m in
      let: m' := l_after_store m l' b j x in
      p (l_pc m) = (Lstore a e x, [:: l'])
      -> eval (st_vm st) e = Vint i
      -> ~~ in_bounds a i
      -> in_bounds b j
      -> st_ms st
      -> lstep p m (Dmem b j) (Oaddr a i) m'

  | lstep_init_msf :
    forall m msf l',
      p (l_pc m) =(Linit_msf msf, [::l'])
      -> ~~ st_ms (l_st m)
      -> lstep p m Dstep Onone (l_after_init_msf m l' msf)

  | lstep_update_msf :
    forall a m x y e l',
      p (l_pc m) = (Lupdate_msf a x y e, [:: l'])
      -> lstep p m Dstep Onone (l_after_update_msf m l' x y e)

  | lstep_protect :
    forall m x y msf l',
      p (l_pc m) = (Lprotect x y msf, [::l'])
      -> lstep p m Dstep Onone (l_after_protect m l' x y msf)

  | lstep_jump :
    forall a m l',
      p (l_pc m) = (Ljump a, [:: l'])
      -> lstep p m Dstep Onone (with_pc m l')

  | lstep_cjump :
    forall a m e l1 l0 b b',
      p (l_pc m) = (Lcjump a e, [:: l1; l0])
      -> let: st := l_st m in
         eval (st_vm st) e = Vbool b'
         -> let: l' := if b then l1 else l0 in
            let: m' := with_pc (with_st m (upd_ms st (b != b'))) l' in
            lstep p m (Dforce b) (Obranch b') m'.

Inductive lsem
  (p : lprogram) :
  lmachine -> seq directive -> seq observation -> lmachine -> Prop :=
  | lsem_done :
    forall m, lsem p m [::] [::] m

  | lsem_step :
    forall m m' m'' d o ds os,
      lstep p m d o m'
      -> lsem p m' ds os m''
      -> lsem p m (d :: ds) (o :: os) m''
.

Lemma lstepI (lp:lprogram) (m:lmachine) (d:directive) (o:observation) (m':lmachine) :
  lstep lp m d o m' ->
  match lp (l_pc m) with
  | (Lassign a x e, [::l']) =>
    [/\ d = Dstep, o = Onone & m' = l_after_assign m l' x e ]

  | (Lload x a e, [::l']) =>
    let: st := l_st m in
    exists i b j,
    [/\ eval (st_vm st) e = Vint i
      , in_bounds b j
      , (if in_bounds a i
         then [/\ a = b, i = j & d = Dstep ]
         else [/\ st_ms st & d = Dmem b j ])
      , o = Oaddr a i
      & m' = l_after_load m l' x b j]

  | (Lstore a e x, [::l']) =>
    let: st := l_st m in
    exists i b j,
    [/\ eval (st_vm st) e = Vint i
      , in_bounds b j
      , (if in_bounds a i
         then [/\ a = b, i = j & d = Dstep ]
         else [/\ st_ms st & d = Dmem b j ])
      , o = Oaddr a i
      & m' = l_after_store m l' b j x ]

  | (Linit_msf msf, [::l']) =>
    [/\ ~~ st_ms (l_st m)
      , d = Dstep, o = Onone & m' = l_after_init_msf m l' msf ]

  | (Lupdate_msf a x y e, [:: l']) =>
    [/\ d = Dstep, o = Onone & m' = l_after_update_msf m l' x y e ]

  | (Lprotect x y msf, [::l']) =>
    [/\ d = Dstep, o = Onone & m' = l_after_protect m l' x y msf ]

  | (Ljump a, [:: l']) =>
    [/\ d = Dstep, o = Onone & m' = with_pc m l' ]

  | (Lcjump a e, [:: l1; l0]) =>
    let: st := l_st m in
    exists b b',
    let: l' := if b then l1 else l0 in
    [/\ eval (st_vm st) e = Vbool b'
      , d = Dforce b, o = Obranch b' & m' = with_pc (with_st m (upd_ms st (b != b'))) l' ]

  | _ => False
  end.
Proof.
  case => {m d o m'}; try by move=> > ->.
  + move=> m x a e l' i -> -> hin. exists i, a, i. rewrite hin. by eeauto.
  + move=> m x a e l' i b j -> -> hin ??.
    exists i, b, j.
    rewrite (negbTE hin).
    by eeauto.
  + move=> m a e x l' i -> -> hin. exists i, a, i. rewrite hin. by eeauto.
  + move=> m a e x l' i b j -> -> hin ??.
    exists i, b, j.
    rewrite (negbTE hin).
    by eeauto.
  by move=> a m e l1 l0 b b' -> ->; exists b, b'.
Qed.

Definition l_speculative_constant_time
  (phi : lmachine -> lmachine -> Prop) (lp : lprogram) : Prop :=
  forall ds os1 os2 m1 m2 m1' m2',
    phi m1 m2 ->
    lsem lp m1 ds os1 m1' ->
    lsem lp m2 ds os2 m2' ->
    os1 = os2.

Definition eq_on_RA (RA : Sr.t) (vm ra_vm : Vm.t) : Prop :=
  eq_map
    (fun x => if Sr.mem x RA then tpublic else tsecret)
    (Vm.get vm)
    (Vm.get ra_vm).

Definition is_initial_lmachine
  (Lin : funname -> label) (p : program) (m : lmachine) : bool :=
  l_pc m == Lin (p_entry_fn p).

Definition l_initial_phi
  (Lin : funname -> label)
  (RA : Sr.t)
  (p : program)
  (gamma : ctx)
  (m1 m2 : lmachine) :
  Prop :=
  let: st1 := l_st m1 in
  let: st2 := l_st m2 in
  [/\ is_initial_lmachine Lin p m1
    , is_initial_lmachine Lin p m2
    , initial_phi_st gamma st1 st2
    & eq_on_RA RA (st_vm st1) (st_vm st2)
  ].
