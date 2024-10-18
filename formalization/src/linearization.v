From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect.

Require Import
  utils
  utils_facts
  var
  syntax
  semantics
  typesystem
  security
  linear
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z.

(* Relating source and target program *)
Section CompilerSpec.

Context
  (p : program)
  (lp : lprogram)
  (Lin Lret : funname -> label)
  (ra : funname -> regvar)
  (to_Z : funname -> label -> Z) (* This should be in Label. *)
  (RA : Sr.t)
.

Definition compile_call_cont (xi : option regvar) ra zl lr l' :=
  match xi with
  | Some msf =>
    ~~ Sr.mem msf RA /\
    lp lr = (Lupdate_msf C msf msf (Eop2 Oeq (Evar ra) zl), [::l'])
  | None =>
    lr = l'
  end.

Definition disjoint (s1 s2 : Sr.t) := Sr.Empty (Sr.inter s1 s2).

Inductive compile_i (f:funname) : label -> instruction -> code -> label -> Prop :=
  | CompAssign : forall l x e l' cont,
    lp l = (Lassign N x e, [::l']) ->
    ~~ Sr.mem x RA -> disjoint RA (free_variables e) ->
    compile_i f l (Iassign x e) cont l'

  | CompLoad : forall l x a e l' cont,
    lp l = (Lload x a e, [::l']) ->
    ~~ Sr.mem x RA -> disjoint RA (free_variables e) ->
    compile_i f l (Iload x a e) cont l'

  | CompStore : forall l a e x l' cont,
    lp l = (Lstore a e x, [::l']) ->
    ~~ Sr.mem x RA -> disjoint RA (free_variables e) ->
    compile_i f l (Istore a e x) cont l'

  | CompInit : forall l x l' cont,
    lp l = (Linit_msf x, [::l']) -> ~~ Sr.mem x RA ->
    compile_i f l (Iinit_msf x) cont l'

  | CompUpdate : forall l msf msf' e l' cont,
    lp l = (Lupdate_msf N msf msf' e, [::l']) ->
    ~~ Sr.mem msf RA -> ~~ Sr.mem msf' RA -> disjoint RA (free_variables e) ->
    compile_i f l (Iupdate_msf msf msf' e) cont l'

  | CompProtect : forall l x y msf l' cont,
    lp l = (Lprotect x y msf, [::l']) ->
    ~~ Sr.mem x RA -> ~~ Sr.mem y RA -> ~~ Sr.mem msf RA ->
    compile_i f l (Iprotect x y msf) cont l'

  | CompIf : forall l e c1 c0 l1 l1' l0 l' cont,
    disjoint RA (free_variables e) ->
    lp l = (Lcjump N e, [::l1; l0]) ->
    compile_c f l1 c1 cont l1'      ->
    lp l1' = (Ljump N, [::l'])      ->
    compile_c f l0 c0 cont l'       ->
    compile_i f l (Iif e c1 c0) cont l'

  | CompWhile : forall l e c l1 l1' l' cont,
    let: w := Iwhile e c in
    disjoint RA (free_variables e) ->
    lp l = (Lcjump N e, [::l1; l'])     ->
    compile_c f l1 c (w :: cont) l1' ->
    lp l1' = (Ljump N, [::l])           ->
    compile_i f l (Iwhile e c) cont l'

  | CompCall : forall l xi g l0 lr l' cont,
    let: lg := Lin g in
    let: rag := ra g in
    let: zl := Econst (to_Z g lr) in
    List.In (f, lr, xi, cont) (contp g p) ->
    lp l  = (Lassign C rag zl, [::l0]) ->
    lp l0 = (Ljump C, [::lg])           ->
    compile_call_cont xi rag zl lr l' ->
    compile_i f l (Icall lr xi g) cont l'

with compile_c (f:funname) : label -> code -> code -> label -> Prop :=
  | Compnil : forall l cont,
    compile_c f l [::] cont l

  | Compcons : forall l i lc c l' cont,
    compile_i f l i (c ++ cont) lc ->
    compile_c f lc c cont  l' ->
    compile_c f l (i :: c) cont l'.

Inductive compile_r (callee:funname) : label -> seq continuation -> Prop :=
  | CompRjump : forall l caller xi cont lr,
    List.In (caller, lr, xi, cont) (contp callee p) ->
    lp l = (Ljump R, [::lr]) ->
    compile_r callee l [:: (caller, lr, xi, cont) ]
  | CompRcjump : forall l caller xi cont rest lr l0,
    List.In (caller, lr, xi, cont) (contp callee p) ->
    let: rag := ra callee in
    let: zl := Econst (to_Z callee lr) in
    lp l = (Lcjump R (Eop2 Oeq (Evar rag) zl), [::lr; l0]) ->
    compile_r callee l0 rest ->
    compile_r callee l ((caller, lr, xi, cont) :: rest).

Definition compile :=
  forall f,
    [/\ compile_c f (Lin f) (p f) [::] (Lret f)
      & f <> p_entry_fn p -> compile_r f (Lret f) (contp f p)
    ].

End CompilerSpec.

(* This allows us to ensure there are no recursive calls.
   This would be checked by the compiler. *)
Inductive is_call (p : program) : funname -> funname -> Prop :=
| Cdirect :
  forall callee caller l xi c,
    (caller, l, xi, c) \in contp callee p ->
    is_call p callee caller
| Ctrans :
  forall callee caller caller',
    is_call p callee caller ->
    is_call p caller caller' ->
    is_call p callee caller'.

Definition no_recursion (p : program) : Prop := forall f, ~ is_call p f f.

Definition cfg_ra_inj (p : program) (ra : funname -> regvar) : Prop :=
  forall callee caller,
    is_call p callee caller ->
    ra callee <> ra caller.

Definition compiler_checks
  (p : program)
  (lp : lprogram)
  (Lret : funname -> label)
  (ra : funname -> regvar)
  (to_Z : funname -> label -> Z)
  (RA : Sr.t)
  : Prop :=
  [/\ uniq_labels p
    , forall f, Sr.mem (ra f) RA
    , forall callee, injective (to_Z callee)
    , no_recursion p
    , cfg_ra_inj p ra
    & lp (Lret (p_entry_fn p)) = (Ljump N, [::])
  ].
