(* -------------------------------------------------------------------------- *)
(* Security. *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  semantics
  syntax
  typesystem
  utils
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.


(* -------------------------------------------------------------------------- *)
(* Speculative constant time (phi-SCT). *)

Section SCT.

Context (phi : machine -> machine -> Prop).

Definition speculative_constant_time (p : program) : Prop :=
  forall ds os1 os2 m1 m2 m1' m2',
    phi m1 m2 ->
    sem p m1 ds os1 m1' ->
    sem p m2 ds os2 m2' ->
    os1 = os2.

End SCT.


(* -------------------------------------------------------------------------- *)
(* Type interpretation (indistinguishability). *)

(* Non-secret (public and free) variables need to coincide. *)
Definition eq_val (t : vtype) (x y : value) : bool :=
  [|| ~~ ty_eqb t tpublic | x == y ].

Section EQ_MAP.

Context (is_n : bool).

Definition proj_is_n x := if is_n then sty_n x else ty_of_lvl (sty_s x).

Definition eq_map (X : Type) (get : X -> vtype) (m m' : X -> value) : Prop :=
  forall x, eq_val (get x) (m x) (m' x).

Definition eq_vm (gamma : ctx) (vm0 vm1 : Vm.t) : Prop :=
  eq_map (fun x => proj_is_n (ctx_reg gamma x)) (Vm.get vm0) (Vm.get vm1).

Definition eq_mem (gamma : ctx) (m0 m1 : Mem.t) : Prop :=
  eq_map
    (fun '(a, _) => proj_is_n (ctx_arr gamma a))
    (uncurry (Mem.read m0))
    (uncurry (Mem.read m1)).

Record eq_st_on (gamma : ctx) (st st' : state) : Prop :=
  {
    eq_st_on_vm : eq_vm gamma (st_vm st) (st_vm st');
    eq_st_on_mem : eq_mem gamma (st_mem st) (st_mem st');
  }.

End EQ_MAP.

Definition eq_vm_n := eq_vm true.
Definition eq_vm_s := eq_vm false.
Definition eq_mem_n := eq_mem true.
Definition eq_mem_s := eq_mem false.
Definition eq_st_on_n := eq_st_on true.
Definition eq_st_on_s := eq_st_on false.

Record eq_st (gamma : ctx) (st st' : state) : Prop :=
  {
    eq_st_spec : eq_st_on_s gamma st st';
    eq_st_seq : st_ms st \/ eq_st_on_n gamma st st';
    eq_st_ms : st_ms st = st_ms st';
  }.

Record eq_m (gamma : ctx) (m m' : machine) : Prop :=
  {
    eq_m_c : m_c m = m_c m';
    eq_m_fn : m_fn m = m_fn m';
    eq_m_cs : m_cs m = m_cs m';
    eq_m_st : eq_st gamma (m_st m) (m_st m');
  }.

Definition initial_phi_vm (gamma : ctx) (vm1 vm2 : Vm.t) : Prop :=
  eq_vm_n gamma vm1 vm2 /\ eq_vm_s gamma vm1 vm2.

Definition initial_phi_mem (gamma : ctx) (mem1 mem2 : Mem.t) : Prop :=
  eq_mem_n gamma mem1 mem2 /\ eq_mem_s gamma mem1 mem2.

Definition initial_phi_st (gamma : ctx) (st1 st2 : state) : Prop :=
  [/\ initial_phi_vm gamma (st_vm st1) (st_vm st2)
    , initial_phi_mem gamma (st_mem st1) (st_mem st2)
    & st_ms st1 = st_ms st2
  ].

Definition initial_phi (p : program) (gamma : ctx) (m1 m2 : machine) : Prop :=
  [/\ is_initial_machine p m1
    , is_initial_machine p m2
    & initial_phi_st gamma (m_st m1) (m_st m2)
  ].

(* Final theorem statement. *)
Definition Typedp_soundness
  (p : program) (cert : certificate) : Prop :=
  let: c := cert (p_entry_fn p) in
  let: sigma := cert_mss c in
  let: gamma := cert_ctx c in
  let: phi := initial_phi p gamma in
  wfcert cert p
  -> typedp cert p
  -> speculative_constant_time phi p.
