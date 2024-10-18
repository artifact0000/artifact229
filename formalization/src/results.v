(* -------------------------------------------------------------------------- *)
(* Main results. *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  syntax
  typesystem
  security
  semantics
  linear
  linearization
.
Require
  both_step
  linearization_facts
  security_facts
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

Theorem source_type_system_is_sound p cert :
  let: c := cert (p_entry_fn p) in
  let: sigma := cert_mss c in
  let: gamma := cert_ctx c in
  let: phi := initial_phi p gamma in
  wfcert cert p ->
  typedp cert p ->
  speculative_constant_time phi p.
Proof. exact: security_facts.typedp_soundness. Qed.

Theorem both_initial_machines_step p cert ds os1 m1 m1' m2 :
  let: c := cert (p_entry_fn p) in
  let: sigma := cert_mss c in
  let: gamma := cert_ctx c in
  let: phi := initial_phi p gamma in
  let: st1 := m_st m1 in
  let: st2 := m_st m2 in
  wfcert cert p ->
  typedp cert p ->
  phi m1 m2 ->
  sem p m1 ds os1 m1' ->
  exists m2' os2, sem p m2 ds os2 m2'.
Proof. exact: both_step.both_initial_machines_step. Qed.

Theorem compilation_preserves_SCT p cert lp Lin Lret ra to_Z RA :
  let: gamma := cert_ctx (cert (p_entry_fn p)) in
  let: phi := l_initial_phi Lin RA p gamma in
  wfcert cert p ->
  typedp cert p ->
  compile p lp Lin Lret ra to_Z RA ->
  compiler_checks p lp Lret ra to_Z RA ->
  l_speculative_constant_time phi lp.
Proof. move=> *. exact: linearization_facts.compiler_soundness. Qed.
