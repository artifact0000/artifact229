(* -------------------------------------------------------------------------- *)
(* Syntax. *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  utils
  var
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.


(* -------------------------------------------------------------------------- *)
(* Variables. *)

Module RegisterVar : VarT := DefaultVar.
Definition regvar := RegisterVar.t.
Module Sr := VS(RegisterVar).

Module Type ArrT.
  Parameter t : eqType.
  Parameter len : t -> Z.
End ArrT.

Module ArrayVar : ArrT.
  Definition t := [eqType of DefaultVar.t * Z].
  Definition len (a : t) := a.2.
End ArrayVar.

Definition arrvar := ArrayVar.t.
Module Sa := VS(ArrayVar).

Module FunctionVar : VarT := DefaultVar.
Definition funname := FunctionVar.t.

Module Label : VarT := DefaultVar.
Definition label := Label.t.


(* -------------------------------------------------------------------------- *)
(* Expressions. *)

Variant op1 :=
  | Onot
  | Oneg
.

Variant op2 :=
  | Oadd
  | Oeq
  | Oand
  | Olt
.

Inductive expression :=
  | Econst of Z
  | Ebool of bool
  | Evar of regvar
  | Eop1 of op1 & expression
  | Eop2 of op2 & expression & expression
.

Definition enot (e : expression) := Eop1 Onot e.

Fixpoint free_variables (e : expression) : Sr.t :=
  match e with
  | Econst _ => Sr.empty
  | Ebool _ => Sr.empty
  | Evar x => Sr.singleton x
  | Eop1 _ e => free_variables e
  | Eop2 _ e0 e1 => Sr.union (free_variables e0) (free_variables e1)
  end.

(* -------------------------------------------------------------------------- *)
(* Instructions. *)

(* Function calls are annotated with unique labels to make the proof easier.
   This can be trivially implemented as an annotation in a separate compiler
   pass. *)
Inductive instruction :=
  | Iassign of regvar & expression
  | Iload of regvar & arrvar & expression
  | Istore of arrvar & expression & regvar
  | Iinit_msf of regvar
  | Iupdate_msf of regvar & regvar & expression
  | Iprotect of regvar & regvar & regvar
  | Iif of expression & seq instruction & seq instruction
  | Iwhile of expression & seq instruction
  | Icall of label & option regvar & funname
.

Notation code := (seq instruction).


(* -------------------------------------------------------------------------- *)
(* Programs. *)

Record program :=
  {
    _prog :> funname -> code;
    p_entry_fn : funname;
    p_local_fn : seq funname;
  }.

Definition funnames (p : program) : seq funname := p_entry_fn p :: p_local_fn p.


(* -------------------------------------------------------------------------- *)
(* Continuations. *)

Definition continuation_c : Type := label * option regvar * code.

Definition oplus
  (cs : list (funname * continuation_c))
  (c : code) :
  list (funname * continuation_c) :=
  [seq (f, (l, xi, x ++ c)) | '(f, (l, xi, x)) <- cs ].

Section CONTC_AUX.

Context (conti : instruction -> list (funname * continuation_c)).

Fixpoint contc_aux (c : code) : list (funname * continuation_c) :=
  match c with
  | [::] => [::]
  | i :: c' => oplus (conti i) c' ++ contc_aux c'
  end.

End CONTC_AUX.

Fixpoint all_conti (i : instruction) : list (funname * continuation_c) :=
  match i with
  | Iassign _ _
  | Iload _ _ _
  | Istore _ _ _
  | Iinit_msf _
  | Iupdate_msf _ _ _
  | Iprotect _ _ _
      => [::]
  | Iif _ c0 c1 => contc_aux all_conti c0 ++ contc_aux all_conti c1
  | Iwhile _ c => oplus (contc_aux all_conti c) [:: i]
  | Icall l xi callee => [:: (callee, (l, xi, [::])) ]
  end.

Definition all_contc := contc_aux all_conti.

Definition conti (callee : funname) (i : instruction) :=
   map snd (filter (fun C => callee == C.1) (all_conti i)).

Definition contc (callee : funname) (c : code) :=
   map snd (filter (fun C => callee == C.1) (all_contc c)).

Definition all_conts (p : program) :=
  let f caller :=
    [seq (callee, (caller, l, xi, cont))
    | '(callee, (l, xi, cont)) <- (all_contc (p caller))
    ]
  in
  flat_map f (funnames p).

Definition contp callee p :=
   map snd (filter (fun C => callee == C.1) (all_conts p)).

Definition continuation : Type := funname * label * option regvar * code.

Definition label_of_cont (cont : continuation) : label := cont.1.1.2.

Definition uniq_labels (p : program) : bool :=
  uniq (map (label_of_cont \o snd) (all_conts p)).

Definition label_lookup lr p :=
  omap snd (ohead ((filter (fun C => label_of_cont C.2 == lr) (all_conts p)))).

(* -------------------------------------------------------------------------- *)
(* Equality. *)

Context
  (instruction_beq : instruction -> instruction -> bool)
  (instruction_eq_axiom : Equality.axiom instruction_beq)
.

Definition instruction_eqMixin := Equality.Mixin instruction_eq_axiom.
Canonical instruction_eqType :=
  Eval hnf in EqType instruction instruction_eqMixin.
