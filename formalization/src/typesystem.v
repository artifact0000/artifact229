(* -------------------------------------------------------------------------- *)
(* Type system. *)
(* -------------------------------------------------------------------------- *)

From Coq Require Import ZArith.
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
(* Variable contexts. *)

Variant level :=
  | Public
  | Secret
.

Scheme Equality for level.

Lemma level_eq_axiom : Equality.axiom level_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_level_dec_bl internal_level_dec_lb).
Qed.

Definition level_eqMixin := Equality.Mixin level_eq_axiom.
Canonical level_eqType := EqType level level_eqMixin.

Definition lvl_le (l l' : level) : bool := [|| l == Public | l' == Secret ].
Definition lvl_max (l l' : level) : level := if lvl_le l l' then l' else l.

(* Variable types. *)
Module TypeVar : VarT := DefaultVar.
Definition typevar := TypeVar.t.

(* [Tmax s] is the maximum of the variables in [s]. [Tmax [::]] is [Public]. *)
Variant vtype :=
  | Tsecret
  | Tmax of seq typevar
.

Definition ty_eqb (t t' : vtype) : bool :=
  match t, t' with
  | Tsecret, Tsecret => true
  | Tmax s, Tmax s' => perm_eq s s'
  | _, _ => false
  end.

Definition tpublic : vtype := Tmax [::].
Definition tsecret : vtype := Tsecret.
Definition tvar (x : typevar) : vtype := Tmax [:: x ].

(* The maximum of the set [{t, t'}]. *)
Definition ty_max (t t' : vtype) : vtype :=
  match t, t' with
  | Tsecret, _ => tsecret
  | _, Tsecret => tsecret
  | Tmax s, Tmax s' => Tmax (s ++ s')
  end.

Definition ty_le (t0 t1 : vtype) : bool :=
  match t0, t1 with
  | _, Tsecret => true
  | Tsecret, Tmax _ => false
  | Tmax s, Tmax s' => incl s s'
  end.

Definition lvl_of_ty (t : vtype) : level :=
  match t with
  | Tsecret => Secret
  | Tmax s => if nilp s then Public else Secret
  end.

Definition ty_of_lvl (l : level) : vtype :=
  match l with
  | Public => tpublic
  | Secret => tsecret
  end.


(* Security types. *)
Record stype :=
  {
    sty_n : vtype;
    sty_s : level;
  }.

Definition spublic : stype := {| sty_n := tpublic; sty_s := Public; |}.
Definition ssecret : stype := {| sty_n := tsecret; sty_s := Secret; |}.

Definition sty_eqb (t t' : stype) : bool :=
  [&& ty_eqb (sty_n t) (sty_n t') & sty_s t == sty_s t' ].

Definition with_sty_s (sty : stype) (l : level) : stype :=
  {|
    sty_n := sty_n sty;
    sty_s := l;
  |}.

Definition sty_le (t t' : stype) : bool :=
  [&& ty_le (sty_n t) (sty_n t') & lvl_le (sty_s t) (sty_s t') ].

Definition sty_max (t t' : stype) : stype :=
  {|
    sty_n := ty_max (sty_n t) (sty_n t');
    sty_s := lvl_max (sty_s t) (sty_s t');
  |}.

(* Contexts. *)
Record ctx :=
  {
    ctx_reg : regvar -> stype;
    ctx_arr : arrvar -> stype;
  }.

Definition ctx_update_reg (gamma : ctx) (x : regvar) (t : stype) : ctx :=
  {|
    ctx_reg := fun y => if x == y then t else ctx_reg gamma y;
    ctx_arr := ctx_arr gamma;
  |}.

Definition ctx_update_arr (gamma : ctx) (a : arrvar) (t : stype) : ctx :=
  {|
    ctx_reg := ctx_reg gamma;
    ctx_arr := fun b => if a == b then t else ctx_arr gamma b;
  |}.

Record ctx_le (gamma0 gamma1 : ctx) :=
  {
    ctx_le_reg : forall x, sty_le (ctx_reg gamma0 x) (ctx_reg gamma1 x);
    ctx_le_arr : forall a, sty_le (ctx_arr gamma0 a) (ctx_arr gamma1 a);
  }.


(* Instantiations of type variables. *)
Definition instantiation : Type := typevar -> level.

Definition instantiate (theta : instantiation) (s : seq typevar) : level :=
  List.fold_right (fun y => lvl_max (theta y)) Public s.

Definition ty_instantiate (theta : instantiation) (t : vtype) : vtype :=
  if t is Tmax s then ty_of_lvl (instantiate theta s) else t.

Definition sty_instantiate (theta : instantiation) (t : stype) : stype :=
  {|
    sty_n := ty_instantiate theta (sty_n t);
    sty_s := sty_s t;
  |}.

Definition ctx_instantiate (theta : instantiation) (gamma : ctx) : ctx :=
  {|
    ctx_reg := fun x => sty_instantiate theta (ctx_reg gamma x);
    ctx_arr := fun a => sty_instantiate theta (ctx_arr gamma a);
  |}.


(* -------------------------------------------------------------------------- *)
(* Misspeculation state. *)

Variant mss :=
  | MSSunknown
  | MSSupdated of regvar
  | MSSoutdated of regvar & expression
.

Definition mss_le (sigma0 sigma1 : mss) : Prop :=
  sigma0 = MSSunknown \/ sigma0 = sigma1.

Definition mss_cond (sigma : mss) (e : expression) : mss :=
  if sigma is MSSupdated x then MSSoutdated x e else MSSunknown.

Definition mss_free_variables (sigma : mss) : Sr.t :=
  match sigma with
  | MSSunknown => Sr.empty
  | MSSupdated x => Sr.singleton x
  | MSSoutdated x e => Sr.add x (free_variables e)
  end.

Definition mss_restrict (sigma : mss) (x : regvar) : mss :=
  if Sr.mem x (mss_free_variables sigma) then MSSunknown else sigma.

Definition mss_call (sigma : mss) (xi : option regvar) : option mss :=
  if xi is Some msf
  then
    if sigma is MSSupdated msf'
    then if msf == msf' then Some sigma else None
    else None
  else Some MSSunknown.


(* -------------------------------------------------------------------------- *)
(* Certificate. *)

Record certificate_data :=
  {
    cert_mss : mss;
    cert_mss' : mss;
    cert_ctx : ctx;
    cert_ctx' : ctx;
  }.

Definition certificate := funname -> certificate_data.

Definition wfcert (cert : certificate) (p : program) : bool :=
  if cert_mss (cert (p_entry_fn p)) is MSSunknown then true else false.


(* -------------------------------------------------------------------------- *)
(* Type system. *)

Section TYPED.

Context (cert : certificate).

Inductive typede : ctx -> expression -> stype -> Prop :=
  | typed_const : forall gamma z, typede gamma (Econst z) spublic
  | typed_bool : forall gamma b, typede gamma (Ebool b) spublic
  | typed_var : forall gamma x, typede gamma (Evar x) (ctx_reg gamma x)
  | typed_op1 :
    forall gamma op e t,
      typede gamma e t
      -> typede gamma (Eop1 op e) t
  | typed_o2 :
    forall gamma op e0 e1 t0 t1,
      typede gamma e0 t0
      -> typede gamma e1 t1
      -> typede gamma (Eop2 op e0 e1) (sty_max t0 t1)
.

Definition ctx_after_load (gamma : ctx) (x : regvar) (a : arrvar) : ctx :=
  let t := with_sty_s (ctx_arr gamma a) Secret in
  ctx_update_reg gamma x t.

Definition sty_after_init_msf (t : stype) : stype :=
  let t_n := sty_n t in
  {| sty_n := t_n; sty_s := lvl_of_ty t_n; |}.

Definition ctx_after_init_msf (gamma : ctx) (msf : regvar) : ctx :=
  let g :=
    {|
      ctx_reg := fun x => sty_after_init_msf (ctx_reg gamma x);
      ctx_arr := fun a => sty_after_init_msf (ctx_arr gamma a);
    |}
  in
  ctx_update_reg g msf spublic.

Definition ctx_after_protect (gamma : ctx) (x y : regvar) : ctx :=
  ctx_reg gamma y |> sty_after_init_msf |> ctx_update_reg gamma x.

Definition is_ctx_after_store
  (gamma gamma' : ctx) (a : arrvar) (t : stype) : Prop :=
  [/\ ctx_le gamma gamma'
    , sty_le t (ctx_arr gamma' a)
    & forall a', a != a' -> lvl_le (sty_s t) (ctx_arr gamma' a' |> sty_s)
  ].

Inductive typedi : mss -> ctx -> instruction -> mss -> ctx -> Prop :=
  | typed_assign :
    forall mss gamma x e t,
      let: mss' := mss_restrict mss x in
      let: gamma' := ctx_update_reg gamma x t in
      typede gamma e t
      -> typedi mss gamma (Iassign x e) mss' gamma'

  | typed_load :
    forall sigma gamma x a e,
      let: sigma' := mss_restrict sigma x in
      typede gamma e spublic
      -> typedi sigma gamma (Iload x a e) sigma' (ctx_after_load gamma x a)

  | typed_store :
    forall sigma gamma gamma' a e x,
      typede gamma e spublic
      -> is_ctx_after_store gamma gamma' a (ctx_reg gamma x)
      -> typedi sigma gamma (Istore a e x) sigma gamma'

  | typed_init_msf :
    forall sigma gamma msf,
      let: sigma' := MSSupdated msf in
      typedi sigma gamma (Iinit_msf msf) sigma' (ctx_after_init_msf gamma msf)

  | typed_update_msf :
    forall gamma x y e,
      let: sigma := MSSoutdated y e in
      let: sigma' := MSSupdated x in
      typedi sigma gamma (Iupdate_msf x y e) sigma' gamma

  | typed_protect :
    forall gamma x y msf,
      let: sigma := MSSupdated msf in
      let: sigma' := mss_restrict sigma x in
      typedi sigma gamma (Iprotect x y msf) sigma' (ctx_after_protect gamma x y)

  | typed_if :
    forall sigma sigma' gamma gamma' e c0 c1,
      typede gamma e spublic
      -> typedc (mss_cond sigma e) gamma c0 sigma' gamma'
      -> typedc (mss_cond sigma (enot e)) gamma c1 sigma' gamma'
      -> typedi sigma gamma (Iif e c0 c1) sigma' gamma'

  | typed_while :
    forall sigma gamma e c,
      let: sigma_e := mss_cond sigma e in
      let: sigma_ne := mss_cond sigma (enot e) in
      typede gamma e spublic
      -> typedc sigma_e gamma c sigma gamma
      -> typedi sigma gamma (Iwhile e c) sigma_ne gamma

  | typed_call :
    forall theta sigma'_call l xi f,
      let: c := cert f in
      let: sigma := cert_mss c in
      let: sigma' := cert_mss' c in
      let: gamma := ctx_instantiate theta (cert_ctx c) in
      let: gamma' := ctx_instantiate theta (cert_ctx' c) in
      mss_call sigma' xi = Some sigma'_call
      -> typedi sigma gamma (Icall l xi f) sigma'_call gamma'

with typedc : mss -> ctx -> code -> mss -> ctx -> Prop :=
  | typed_nil :
    forall sigma gamma,
      typedc sigma gamma [::] sigma gamma

  | typed_cons :
    forall sigma0 sigma1 sigma2 gamma0 gamma1 gamma2 i c,
      typedi sigma0 gamma0 i sigma1 gamma1
      -> typedc sigma1 gamma1 c sigma2 gamma2
      -> typedc sigma0 gamma0 (i :: c) sigma2 gamma2

  | typed_weak :
    forall sigma sigma' sigma0 sigma0' gamma gamma' gamma0 gamma0' c,
      typedc sigma0 gamma0 c sigma0' gamma0'
      -> mss_le sigma0 sigma
      -> mss_le sigma' sigma0'
      -> ctx_le gamma gamma0
      -> ctx_le gamma0' gamma'
      -> typedc sigma gamma c sigma' gamma'
.

End TYPED.

Definition typedp (cert : certificate) (p : program) : Prop :=
  forall f,
    let: cf := cert f in
    let: sigma := cert_mss cf in
    let: sigma' := cert_mss' cf in
    let: gamma := cert_ctx cf in
    let: gamma' := cert_ctx' cf in
    typedc cert sigma gamma (p f) sigma' gamma'.
