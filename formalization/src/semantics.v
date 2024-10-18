(* -------------------------------------------------------------------------- *)
(* Semantics. *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
From Coq Require Relations.
From mathcomp Require Import all_ssreflect.

Require Import
  syntax
  utils
  var
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.


(* -------------------------------------------------------------------------- *)
(* Values. *)

Variant value :=
  | Vint of Z
  | Vbool of bool
  | Vundef
.

(* These can be anything, we only need them to be different. *)
Definition msf_mask : value := Vbool true.
Definition msf_nomask : value := Vbool false.

Scheme Equality for value.

Lemma value_eq_axiom : Equality.axiom value_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_value_dec_bl internal_value_dec_lb).
Qed.

Definition value_eqMixin := Equality.Mixin value_eq_axiom.
Canonical value_eqType := EqType value value_eqMixin.


(* -------------------------------------------------------------------------- *)
(* Variable maps. *)

Module Type VmT.
  Parameter t : Type.
  Parameter get : t -> regvar -> value.
  Parameter set : t -> regvar -> value -> t.

  Parameter get_set :
    forall vm x y v,
      get (set vm x v) y = if x == y then v else get vm y.
End VmT.

Module Vm : VmT.
  Definition t := regvar -> value.

  Definition get (vm : t) (x : regvar) : value  := vm x.
  Definition set (vm : t) (x : regvar) (v : value) : t :=
    fun y => if x == y then v else vm y.

  Lemma get_set vm x y v :
    get (set vm x v) y = if x == y then v else get vm y.
  Proof. done. Qed.
End Vm.


(* -------------------------------------------------------------------------- *)
(* Memory. *)
(* We have a segmented memory (in arrays) and reads or writes that are out of
   bounds always return [Vundef].
   We still capture the attacker's capabilities because the rules for unsafe
   loads and stores allows them to load or store any value from any array. *)

Definition in_bounds (a : arrvar) (i : Z) :=
  [&& 0 <=? i & i <? ArrayVar.len a ]%Z.

Module Type MemT.
  Parameter t : Type.
  Parameter read : t -> arrvar -> Z -> value.
  Parameter write : t  -> arrvar -> Z -> value -> t.

  Parameter read_write :
    forall m a i b j v,
      in_bounds a i
      -> read (write m a i v) b j
         = if [&& a == b & Z.eqb i j ] then v else read m b j.

End MemT.

Module Mem : MemT.
  Record _t :=
    {
      mem_map : arrvar -> Z -> value;
    }.

  Definition t := _t.
  Definition undef : t :=
    {| mem_map := fun _ _ => Vundef; |}.

  Definition read (m : t) (a : arrvar) (i : Z) : value :=
    if in_bounds a i then mem_map m a i else Vundef.

  Definition write (m : t) (a : arrvar) (i : Z) (v : value) : t :=
    if in_bounds a i
    then
      let map' a' i' :=
        if [&& a' == a & Z.eqb i i' ] then v else mem_map m a' i'
      in
      {| mem_map := map'; |}
    else
      undef.

  Lemma read_write m a i b j v :
    in_bounds a i
    -> read (write m a i v) b j
       = if [&& a == b & Z.eqb i j ] then v else read m b j.
  Proof.
    move=> hi.
    rewrite /write hi /read /= /in_bounds /= -/(in_bounds b j) eq_sym.
    case: andP; last done.
    move=> [/eqP ? /Z.eqb_eq ?]; subst b j.
    by rewrite hi.
  Qed.

End Mem.

(* -------------------------------------------------------------------------- *)
(* States. *)

Record state :=
  {
    st_vm : Vm.t;
    st_mem : Mem.t;
    st_ms : bool;
  }.

Definition with_vm st vm :=
  {|
    st_vm := vm;
    st_mem := st_mem st;
    st_ms := st_ms st;
  |}.

Definition with_mem st mem :=
  {|
    st_vm := st_vm st;
    st_mem := mem;
    st_ms := st_ms st;
  |}.

Definition with_ms st ms :=
  {|
    st_vm := st_vm st;
    st_mem := st_mem st;
    st_ms := ms;
  |}.

Definition set_ms st := with_ms st true.


(* -------------------------------------------------------------------------- *)
(* Evaluating expressions. *)

Fixpoint eval (vm : Vm.t) (e : expression) : value :=
  match e with
  | Econst z => Vint z
  | Ebool b => Vbool b
  | Evar x => Vm.get vm x
  | Eop1 Onot e => if eval vm e is Vbool b then Vbool (~~ b) else Vundef
  | Eop1 Oneg e => if eval vm e is Vint z then Vint (- z)%Z else Vundef
  | Eop2 op e0 e1 =>
      match op, eval vm e0, eval vm e1 with
      | Oadd, Vint z0, Vint z1 => Vint (z0 + z1)
      | Oeq, Vint z0, Vint z1 => Vbool (z0 == z1)%Z
      | Olt, Vint z0, Vint z1 => Vbool (z0 <? z1)%Z
      | Oeq, Vbool b0, Vbool b1 => Vbool (b0 == b1)
      | Oand, Vbool b0, Vbool b1 => Vbool (b0 && b1)
      | _, _, _ => Vundef
      end
  end.


(* -------------------------------------------------------------------------- *)
(* Writing. *)

Definition write_reg (st : state) (x : regvar) (v : value) : state :=
  Vm.set (st_vm st) x v |> with_vm st.

Definition write_mem (st : state) (a : arrvar) (i : Z) (v : value) : state :=
  Mem.write (st_mem st) a i v |> with_mem st.


(* -------------------------------------------------------------------------- *)
(* Machines. *)

Definition callstack := seq (funname * label * code).

Record machine :=
  {
    m_c : code;
    m_fn : funname;
    m_cs : callstack;
    m_st : state;
  }.

Definition with_c (m : machine) (c : code) : machine :=
  {|
    m_c := c;
    m_fn := m_fn m;
    m_cs := m_cs m;
    m_st := m_st m;
  |}.

Definition with_st (m : machine) (st : state) : machine :=
  {|
    m_c := m_c m;
    m_fn := m_fn m;
    m_cs := m_cs m;
    m_st := st;
  |}.


(* -------------------------------------------------------------------------- *)
(* Small step semantics. *)

Variant directive :=
  | Dstep
  | Dforce of bool
  | Dmem of arrvar & Z
  | Dreturn of funname & label & option regvar & code
.

Variant observation :=
  | Onone
  | Oaddr of arrvar & Z
  | Obranch of bool
.

Definition m_after_assign m c x e :=
  let st := m_st m in
  let v := eval (st_vm st) e in
  let st' := write_reg st x v in
  with_c (with_st m st') c.

Definition m_after_init_msf m c msf :=
  let st' := write_reg (m_st m) msf msf_nomask in
  with_c (with_st m st') c.

Definition st_after_update_msf st x y e :=
  let vm := st_vm st in
  let v := if eval vm e == Vbool true then Vm.get vm y else msf_mask in
  write_reg st x v.

Definition m_after_update_msf m c x y e :=
  let st' := st_after_update_msf (m_st m) x y e in
  with_c (with_st m st') c.

Definition st_after_protect st x y msf :=
  let vm := st_vm st in
  let v := if Vm.get vm msf == msf_mask then msf_mask else Vm.get vm y in
  write_reg st x v.

Definition m_after_protect m c x y msf :=
  let st' := st_after_protect (m_st m) x y msf in
  with_c (with_st m st') c.

Definition m_after_load m c x a i :=
  let st := m_st m in
  let v := Mem.read (st_mem st) a i in
  let st' := write_reg st x v in
  with_c (with_st m st') c.

Definition m_after_store m c a i x :=
  let st := m_st m in
  let v := Vm.get (st_vm st) x in
  let st' := write_mem st a i v in
  with_c (with_st m st') c.

Definition m_after_call m c f cf l :=
  {|
    m_c := cf;
    m_fn := f;
    m_cs := (m_fn m, l, c) :: m_cs m;
    m_st := m_st m;
  |}.

Definition m_after_ret_n m f c cs :=
  {|
    m_c := c;
    m_fn := f;
    m_cs := cs;
    m_st := m_st m;
  |}.

Definition st_after_RET_S st xi :=
  let vm := st_vm st in
  let vm' := if xi is Some x then Vm.set vm x msf_mask else vm in
  with_vm st vm' |> set_ms.

Definition m_after_ret_s m f xi c :=
  {|
    m_c := c;
    m_fn := f;
    m_cs := [::];
    m_st := st_after_RET_S (m_st m) xi;
  |}.

Definition is_speculative_ret
  (cs : callstack) (f : funname) (l : label) (c : code) : bool :=
  match ohead cs with
  | Some (f', l', c') => (f, l, c) != (f', l', c')
  | None => true
  end.

(* The rules for unsafe loads and stores require that the misspeculation status
   is set, because we assume that the program is sequentially safe, and
   therefore unsafe memory accesses must happen under misspeculation. *)
Variant step
  (p : program) : machine -> directive -> observation -> machine -> Prop :=
  | step_assign :
    forall m x e c,
      m_c m = Iassign x e :: c
      -> step p m Dstep Onone (m_after_assign m c x e)

  | step_load_n :
    forall m x a e c i,
      let: st := m_st m in
      let: m' := m_after_load m c x a i in
      m_c m = Iload x a e :: c
      -> eval (st_vm st) e = Vint i
      -> in_bounds a i
      -> step p m Dstep (Oaddr a i) m'

  | step_load_s :
    forall m x a e c i b j,
      let: st := m_st m in
      let: m' := m_after_load m c x b j in
      m_c m = Iload x a e :: c
      -> eval (st_vm st) e = Vint i
      -> ~~ in_bounds a i
      -> in_bounds b j
      -> st_ms st
      -> step p m (Dmem b j) (Oaddr a i) m'

  | step_store_n :
    forall m a e x c i,
      let: st := m_st m in
      let: m' := m_after_store m c a i x in
      m_c m = Istore a e x :: c
      -> eval (st_vm st) e = Vint i
      -> in_bounds a i
      -> step p m Dstep (Oaddr a i) m'

  | step_store_s :
    forall m a e x c i b j,
      let: st := m_st m in
      let: m' := m_after_store m c b j x in
      m_c m = Istore a e x :: c
      -> eval (st_vm st) e = Vint i
      -> ~~ in_bounds a i
      -> in_bounds b j
      -> st_ms st
      -> step p m (Dmem b j) (Oaddr a i) m'

  | step_init_msf :
    forall m msf c,
      m_c m = Iinit_msf msf :: c
      -> ~~ st_ms (m_st m)
      -> step p m Dstep Onone (m_after_init_msf m c msf)

  | step_update_msf :
    forall m x y e c,
      m_c m = Iupdate_msf x y e :: c
      -> step p m Dstep Onone (m_after_update_msf m c x y e)

  | step_protect :
    forall m x y msf c,
      m_c m = Iprotect x y msf :: c
      -> step p m Dstep Onone (m_after_protect m c x y msf)

  | step_if :
    forall m e c1 c0 c b b',
      m_c m = Iif e c1 c0 :: c
      -> let: st := m_st m in
         eval (st_vm st) e = Vbool b'
         -> let: c' := (if b then c1 else c0) ++ c in
            let: st' := with_ms st ((b != b') || st_ms st) in
            let: m' := with_c (with_st m st') c' in
            step p m (Dforce b) (Obranch b') m'

  | step_while :
    forall m e c1 c b b',
      m_c m = Iwhile e c1 :: c
      -> let: st := m_st m in
         eval (st_vm st) e = Vbool b'
         -> let: c' := if b then c1 ++ (m_c m) else c in
            let: st' := with_ms st ((b != b') || st_ms st) in
            let: m' := with_c (with_st m st') c' in
            step p m (Dforce b) (Obranch b') m'

  | step_call :
    forall m f l xi c,
      m_c m = Icall l xi f :: c
      -> step p m Dstep Onone (m_after_call m c f (p f) l)

  | step_ret :
    forall m f l xi c m',
      m_c m = [::]
      -> (if is_speculative_ret (m_cs m) f l c
          then [/\ List.In (f, l, xi, c) (contp (m_fn m) p)
                 & m' = m_after_ret_s m f xi c
               ]
          else m' = m_after_ret_n m f c (drop 1 (m_cs m)))
      -> step p m (Dreturn f l xi c) Onone m'.

Inductive sem
  (p : program) :
  machine -> seq directive -> seq observation -> machine -> Prop :=
  | sem_done :
    forall m, sem p m [::] [::] m

  | sem_step :
    forall m m' m'' d o ds os,
      step p m d o m'
      -> sem p m' ds os m''
      -> sem p m (d :: ds) (o :: os) m''
.

Definition is_initial_machine (p : program) (m : machine) : bool :=
  [&& m_c m == p (p_entry_fn p)
    , m_fn m == p_entry_fn p
    & m_cs m == [::]
  ].
