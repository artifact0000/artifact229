open Bool
open Datatypes
open MSetDecide
open MSetEqProperties
open PrimInt63
open Eqtype
open Gen_map
open Seq
open Ssrbool
open Type
open Utils0
open Wsize
open Xseq

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module FunName =
 struct
  type t = CoreIdent.funname

  (** val tag : t -> Uint63.t **)

  let tag = CoreIdent.funname_tag

  (** val tagI : __ **)

  let tagI =
    __
 end

module TFunName = Tagged.Tagged(FunName)

(** val funname_eqType : Equality.coq_type **)

let funname_eqType =
  { Equality.op = (fun x y ->
    PrimInt63.eqb (FunName.tag (Obj.magic x)) (FunName.tag (Obj.magic y)));
    Equality.mixin_of__1 = (Obj.magic TFunName.t_eq_axiom) }

module Mf = TFunName.Mt

module Sf = TFunName.St

type funname = CoreIdent.funname

(** val get_fundef : (funname * 'a1) list -> funname -> 'a1 option **)

let get_fundef p f =
  assoc funname_eqType (Obj.magic p) (Obj.magic f)

module MvMake =
 functor (I:Ident.IDENT) ->
 struct
  type var = { vtype : stype; vname : I.ident }

  (** val vtype : var -> stype **)

  let vtype v =
    v.vtype

  (** val vname : var -> I.ident **)

  let vname v =
    v.vname

  (** val var_beq : var -> var -> bool **)

  let var_beq v1 v2 =
    let { vtype = t1; vname = n1 } = v1 in
    let { vtype = t2; vname = n2 } = v2 in
    (&&) (eq_op stype_eqType (Obj.magic t1) (Obj.magic t2))
      (eq_op Ident.ident_eqType (Obj.magic n1) (Obj.magic n2))

  (** val var_eqP : var Equality.axiom **)

  let var_eqP __top_assumption_ =
    let _evar_0_ = fun t1 n1 __top_assumption_0 ->
      let _evar_0_ = fun t2 n2 ->
        iffP (var_beq { vtype = t1; vname = n1 } { vtype = t2; vname = n2 })
          (if var_beq { vtype = t1; vname = n1 } { vtype = t2; vname = n2 }
           then ReflectT
           else ReflectF)
      in
      let { vtype = vtype0; vname = vname0 } = __top_assumption_0 in
      _evar_0_ vtype0 vname0
    in
    let { vtype = vtype0; vname = vname0 } = __top_assumption_ in
    _evar_0_ vtype0 vname0

  (** val var_eqMixin : var Equality.mixin_of **)

  let var_eqMixin =
    { Equality.op = var_beq; Equality.mixin_of__1 = var_eqP }

  (** val var_eqType : Equality.coq_type **)

  let var_eqType =
    Obj.magic var_eqMixin

  (** val var_cmp : var -> var -> comparison **)

  let var_cmp x y =
    match stype_cmp (vtype x) (vtype y) with
    | Eq -> I.Mid.K.cmp (Obj.magic vname x) (Obj.magic vname y)
    | x0 -> x0
 end

module Var = MvMake(Ident.Ident)

(** val is_glob_var : Var.var -> bool **)

let is_glob_var x =
  match Ident.Ident.id_kind (Var.vname x) with
  | Global -> true
  | _ -> false

(** val is_inline_var : Var.var -> bool **)

let is_inline_var x =
  match Ident.Ident.id_kind (Var.vname x) with
  | Inline -> true
  | _ -> false

(** val is_var_in_memory : Var.var -> bool **)

let is_var_in_memory x =
  match Ident.Ident.id_kind (Var.vname x) with
  | Const -> false
  | Reg p ->
    let (_, r0) = p in (match r0 with
                        | Direct -> false
                        | Pointer _ -> true)
  | Inline -> false
  | _ -> true

(** val is_ptr : Var.var -> bool **)

let is_ptr x =
  match Ident.Ident.id_kind (Var.vname x) with
  | Stack r -> (match r with
                | Direct -> false
                | Pointer _ -> true)
  | Reg p ->
    let (_, r0) = p in (match r0 with
                        | Direct -> false
                        | Pointer _ -> true)
  | _ -> false

(** val is_reg_ptr : Var.var -> bool **)

let is_reg_ptr x =
  match Ident.Ident.id_kind (Var.vname x) with
  | Reg p ->
    let (_, r0) = p in (match r0 with
                        | Direct -> false
                        | Pointer _ -> true)
  | _ -> false

(** val is_regx : Var.var -> bool **)

let is_regx x =
  match Ident.Ident.id_kind (Var.vname x) with
  | Reg p -> let (r, _) = p in (match r with
                                | Normal -> false
                                | Extra -> true)
  | _ -> false

(** val is_reg_array : Var.var -> bool **)

let is_reg_array x =
  match Ident.Ident.id_kind (Var.vname x) with
  | Reg p ->
    let (_, r0) = p in
    (match r0 with
     | Direct -> (match Var.vtype x with
                  | Coq_sarr _ -> true
                  | _ -> false)
     | Pointer _ -> false)
  | _ -> false

module CmpVar =
 struct
  (** val t : Equality.coq_type **)

  let t =
    Equality.clone Var.var_eqType (Obj.magic Var.var_eqMixin) (fun x -> x)

  (** val cmp : Equality.sort -> Equality.sort -> comparison **)

  let cmp =
    Obj.magic Var.var_cmp
 end

module SExtra =
 functor (T:CmpType) ->
 struct
  module Sv = Smake(T)

  module SvP = EqProperties(Sv)

  module SvD = WDecide(Sv)

  (** val coq_Sv_memP : Sv.elt -> Sv.t -> reflect **)

  let coq_Sv_memP x s =
    equivP (Sv.mem x s) (if Sv.mem x s then ReflectT else ReflectF)

  (** val coq_Sv_elemsP : Sv.elt -> Sv.t -> reflect **)

  let coq_Sv_elemsP x s =
    equivP (in_mem x (mem (seq_predType T.t) (Obj.magic Sv.elements s)))
      (if in_mem x (mem (seq_predType T.t) (Obj.magic Sv.elements s))
       then ReflectT
       else ReflectF)

  (** val disjoint : Sv.t -> Sv.t -> bool **)

  let disjoint s1 s2 =
    Sv.is_empty (Sv.inter s1 s2)

  (** val disjointP : Sv.t -> Sv.t -> reflect **)

  let disjointP s1 s2 =
    let _evar_0_ = fun _ -> ReflectT in
    let _evar_0_0 = fun _ -> ReflectF in
    if disjoint s1 s2 then _evar_0_ __ else _evar_0_0 __

  (** val sv_of_option : Sv.elt option -> Sv.t **)

  let sv_of_option oa =
    omap_dflt Sv.empty Sv.singleton oa

  (** val sv_of_list : ('a1 -> Sv.elt) -> 'a1 list -> Sv.t **)

  let sv_of_list f =
    foldl (fun s r -> Sv.add (f r) s) Sv.empty

  (** val sv_of_listP : ('a1 -> Sv.elt) -> Sv.elt -> 'a1 list -> reflect **)

  let sv_of_listP f x m =
    coq_Sv_memP x (sv_of_list f m)
 end

module SvExtra = SExtra(CmpVar)

module Mvar = Mmake(CmpVar)
