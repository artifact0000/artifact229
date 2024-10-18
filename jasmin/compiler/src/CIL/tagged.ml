open Bool
open Datatypes
open MSetDecide
open MSetEqProperties
open PrimInt63
open Eqtype
open Gen_map
open Ssrbool

type __ = Obj.t

module type TaggedCore =
 sig
  type t

  val tag : t -> Uint63.t
 end

module Tagged =
 functor (C:TaggedCore) ->
 struct
  type t = C.t

  (** val tag : t -> Uint63.t **)

  let tag =
    C.tag

  (** val t_eqb : t -> t -> bool **)

  let t_eqb x y =
    PrimInt63.eqb (tag x) (tag y)

  (** val t_eq_axiom : t Equality.axiom **)

  let t_eq_axiom x y =
    equivP (t_eqb x y) (iff_reflect (t_eqb x y))

  (** val t_eqMixin : t Equality.mixin_of **)

  let t_eqMixin =
    { Equality.op = t_eqb; Equality.mixin_of__1 = t_eq_axiom }

  (** val t_eqType : Equality.coq_type **)

  let t_eqType =
    Obj.magic t_eqMixin

  (** val cmp : t -> t -> comparison **)

  let cmp x y =
    compares (tag x) (tag y)

  module CmpT =
   struct
    (** val t : Equality.coq_type **)

    let t =
      Equality.clone t_eqType (Obj.magic t_eqMixin) (fun x -> x)

    (** val cmp : Equality.sort -> Equality.sort -> comparison **)

    let cmp =
      Obj.magic cmp
   end

  module Mt = Mmake(CmpT)

  module St = Smake(CmpT)

  module StP = EqProperties(St)

  module StD = WDecide(St)
 end
