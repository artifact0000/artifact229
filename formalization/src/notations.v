Require Import syntax.
Declare Custom Entry expr.

Definition eadd := Eop2 Oadd.
Definition esub e0 e1 := Eop2 Oadd e0 (Eop1 Oneg e1).
Definition eeq := Eop2 Oeq.
Definition elt := Eop2 Olt.
Definition eand := Eop2 Oand.

Module ExpressionNotations.

Declare Scope expr_scope.
Open Scope expr_scope.

Notation "expr:( e )" :=
  (e)
  (e custom expr at level 0,
   format "'expr:(' e ')'")
  : expr_scope.
Notation "coq:( e )" :=
  (e)
  (in custom expr at level 0,
   e constr at level 0)
  : expr_scope.
Notation "( e )" := (e) (in custom expr at level 0, e custom expr) : expr_scope.
Notation "x" := x (in custom expr at level 0, x ident) : expr_scope.

Notation "# z" :=
  (Econst z)
  (in custom expr at level 0, z constr, format "# z") : expr_scope.
Notation "'tt'" := (Ebool true) (in custom expr at level 0) : expr_scope.
Notation "'ff'" := (Ebool false) (in custom expr at level 0) : expr_scope.
Notation "$( x )" :=
  (Evar x) (in custom expr at level 5, format "'$(' x ')'") : expr_scope.
Notation "! e" := (enot e) (in custom expr at level 2) : expr_scope.
Infix "+" :=
  (eadd) (in custom expr at level 3, left associativity) : expr_scope.
Infix "-" :=
  (esub) (in custom expr at level 3, left associativity) : expr_scope.
Infix "==" := (eeq) (in custom expr at level 4, no associativity) : expr_scope.
Infix "<" := (elt) (in custom expr at level 4, no associativity) : expr_scope.
Infix "&&" :=
  (eand) (in custom expr at level 3, left associativity) : expr_scope.

End ExpressionNotations.

Declare Custom Entry code.

Module CodeNotations.

Declare Scope code_scope.
Open Scope code_scope.

Notation "code:( e )" :=
  (e)
  (e custom code at level 0,
   format "'code:(' e ')'")
  : code_scope.
Notation "coq:( e )" :=
  (e)
  (in custom code at level 0,
   e constr at level 0,
   format "'coq:(' e ')'")
  : code_scope.
Notation "( e )" := (e) (in custom code at level 0, e custom code) : code_scope.
Notation "x" := x (in custom code at level 0, x ident) : code_scope.

Notation "'skip'" :=
  (@nil instruction) (in custom code at level 0) : code_scope.
Notation "i ; c" :=
  (@cons instruction i c)
  (in custom code at level 1,
   i custom code,
   c custom code,
   right associativity,
   format "'[v' i ; '/' c ']'")
  : code_scope.
Notation "x = e" :=
  (Iassign x e)
  (in custom code at level 1,
   x custom code,
   e custom expr)
  : code_scope.
Notation "x = 'load(' a , e ')'" :=
  (Iload x a e)
  (in custom code at level 1,
   x custom code,
   a custom code,
   e custom expr)
  : code_scope.
Notation "'store(' a , e ')' = x" :=
  (Istore a e x)
  (in custom code at level 1,
   a custom code,
   e custom expr,
   x custom code)
  : code_scope.
Notation "msf = 'init_msf()'" :=
  (Iinit_msf msf)
  (in custom code at level 1,
   msf custom code)
  : code_scope.
Notation "x = 'update_msf(' y , e ')'" :=
  (Iupdate_msf x y e)
  (in custom code at level 1,
   x custom code,
   y custom code,
   e custom expr)
  : code_scope.
Notation "x = 'protect(' y , msf ')'" :=
  (Iprotect x y msf)
  (in custom code at level 1,
   x custom code,
   y custom code,
   msf custom code)
  : code_scope.
Notation "'if' e 'then' c0 'else' c1 'end' " :=
  (Iif e c0 c1)
  (in custom code at level 1,
   e custom expr,
   c0 custom code,
   c1 custom code,
   format "'[v' 'if'  e  'then' '/  ' c0 '/'  'else'  c1  'end' ']'")
  : code_scope.
Notation "'while' e 'do' c 'end'" :=
  (Iwhile e c)
  (in custom code at level 1,
   e custom expr,
   c custom code,
   format "'[v' 'while'  e  'do'  '/  ' c '/'  'end' ']'")
  : code_scope.
Notation "'call(' l , f ')'" :=
  (Icall l None f)
  (in custom code at level 1,
   l constr,
   f custom code)
  : code_scope.
Notation "'call(' l , x , f ')'" :=
  (Icall l (Some x) f)
  (in custom code at level 1,
   l constr,
   x custom code,
   f custom code)
  : code_scope.
End CodeNotations.
