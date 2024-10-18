open Eqtype
open Ssralg
open Ssrbool

type __ = Obj.t

(** val ring_display : unit **)

let ring_display =
  ()

module Num =
 struct
  type normed_mixin_of =
    GRing.Zmodule.sort -> GRing.Zmodule.sort
    (* singleton inductive, whose constructor was NormedMixin *)

  module NumDomain =
   struct
    type 't class_of = { base : 't GRing.IntegralDomain.class_of;
                         order_mixin : Equality.sort
                                       Order.Order.POrder.mixin_of;
                         normed_mixin : normed_mixin_of }

    (** val base : 'a1 class_of -> 'a1 GRing.IntegralDomain.class_of **)

    let base c =
      c.base

    (** val order_mixin :
        'a1 class_of -> Equality.sort Order.Order.POrder.mixin_of **)

    let order_mixin c =
      c.order_mixin

    (** val order_base : 'a1 class_of -> 'a1 Order.Order.POrder.class_of **)

    let order_base class_of_T =
      { Order.Order.POrder.base =
        (GRing.ComRing.base
          (GRing.IntegralDomain.base class_of_T.base).GRing.ComUnitRing.base).GRing.Ring.base.GRing.Zmodule.base;
        Order.Order.POrder.mixin = (Obj.magic class_of_T.order_mixin) }

    type coq_type =
      __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    (** val coq_class : coq_type -> sort class_of **)

    let coq_class cT =
      cT

    (** val pack :
        'a1 GRing.IntegralDomain.class_of -> Equality.sort
        Order.Order.POrder.mixin_of -> normed_mixin_of ->
        GRing.IntegralDomain.coq_type -> 'a1 GRing.IntegralDomain.class_of ->
        Equality.sort Order.Order.POrder.mixin_of -> normed_mixin_of ->
        coq_type **)

    let pack _ _ _ _ b om nm =
      { base = (Obj.magic b); order_mixin = om; normed_mixin = nm }

    (** val porderType : coq_type -> Order.Order.POrder.coq_type **)

    let porderType cT =
      order_base (coq_class cT)

    (** val porder_zmodType : coq_type -> GRing.Zmodule.coq_type **)

    let porder_zmodType cT =
      (GRing.ComRing.base
        (GRing.IntegralDomain.base (coq_class cT).base).GRing.ComUnitRing.base).GRing.Ring.base
   end

  module NumMixin =
   struct
    type of_ = { le : GRing.IntegralDomain.sort rel;
                 lt : GRing.IntegralDomain.sort rel;
                 norm : (GRing.IntegralDomain.sort ->
                        GRing.IntegralDomain.sort) }

    (** val le :
        GRing.IntegralDomain.coq_type -> of_ -> GRing.IntegralDomain.sort rel **)

    let le _ o =
      o.le

    (** val lt :
        GRing.IntegralDomain.coq_type -> of_ -> GRing.IntegralDomain.sort rel **)

    let lt _ o =
      o.lt

    (** val norm :
        GRing.IntegralDomain.coq_type -> of_ -> GRing.IntegralDomain.sort ->
        GRing.IntegralDomain.sort **)

    let norm _ o =
      o.norm

    (** val ltPOrderMixin :
        GRing.IntegralDomain.coq_type -> of_ -> Order.Order.LtPOrderMixin.of_ **)

    let ltPOrderMixin _ m =
      { Order.Order.LtPOrderMixin.le = m.le; Order.Order.LtPOrderMixin.lt =
        m.lt }

    (** val normedZmodMixin :
        GRing.IntegralDomain.coq_type -> of_ -> normed_mixin_of **)

    let normedZmodMixin _ m =
      m.norm
   end

  module RealLeMixin =
   struct
    type of_ = { le : GRing.IntegralDomain.sort rel;
                 lt : GRing.IntegralDomain.sort rel;
                 norm : (GRing.IntegralDomain.sort ->
                        GRing.IntegralDomain.sort) }

    (** val le :
        GRing.IntegralDomain.coq_type -> of_ -> GRing.IntegralDomain.sort rel **)

    let le _ o =
      o.le

    (** val lt :
        GRing.IntegralDomain.coq_type -> of_ -> GRing.IntegralDomain.sort rel **)

    let lt _ o =
      o.lt

    (** val norm :
        GRing.IntegralDomain.coq_type -> of_ -> GRing.IntegralDomain.sort ->
        GRing.IntegralDomain.sort **)

    let norm _ o =
      o.norm

    (** val numMixin :
        GRing.IntegralDomain.coq_type -> of_ -> NumMixin.of_ **)

    let numMixin _ m =
      { NumMixin.le = m.le; NumMixin.lt = m.lt; NumMixin.norm = m.norm }
   end
 end
