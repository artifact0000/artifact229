open Eqtype
open Ssralg
open Ssrbool

type __ = Obj.t

val ring_display : unit

module Num :
 sig
  type normed_mixin_of =
    GRing.Zmodule.sort -> GRing.Zmodule.sort
    (* singleton inductive, whose constructor was NormedMixin *)

  module NumDomain :
   sig
    type 't class_of = { base : 't GRing.IntegralDomain.class_of;
                         order_mixin : Equality.sort
                                       Order.Order.POrder.mixin_of;
                         normed_mixin : normed_mixin_of }

    val base : 'a1 class_of -> 'a1 GRing.IntegralDomain.class_of

    val order_mixin :
      'a1 class_of -> Equality.sort Order.Order.POrder.mixin_of

    val order_base : 'a1 class_of -> 'a1 Order.Order.POrder.class_of

    type coq_type =
      __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    val coq_class : coq_type -> sort class_of

    val pack :
      'a1 GRing.IntegralDomain.class_of -> Equality.sort
      Order.Order.POrder.mixin_of -> normed_mixin_of ->
      GRing.IntegralDomain.coq_type -> 'a1 GRing.IntegralDomain.class_of ->
      Equality.sort Order.Order.POrder.mixin_of -> normed_mixin_of -> coq_type

    val porderType : coq_type -> Order.Order.POrder.coq_type

    val porder_zmodType : coq_type -> GRing.Zmodule.coq_type
   end

  module NumMixin :
   sig
    type of_ = { le : GRing.IntegralDomain.sort rel;
                 lt : GRing.IntegralDomain.sort rel;
                 norm : (GRing.IntegralDomain.sort ->
                        GRing.IntegralDomain.sort) }

    val le :
      GRing.IntegralDomain.coq_type -> of_ -> GRing.IntegralDomain.sort rel

    val lt :
      GRing.IntegralDomain.coq_type -> of_ -> GRing.IntegralDomain.sort rel

    val norm :
      GRing.IntegralDomain.coq_type -> of_ -> GRing.IntegralDomain.sort ->
      GRing.IntegralDomain.sort

    val ltPOrderMixin :
      GRing.IntegralDomain.coq_type -> of_ -> Order.Order.LtPOrderMixin.of_

    val normedZmodMixin :
      GRing.IntegralDomain.coq_type -> of_ -> normed_mixin_of
   end

  module RealLeMixin :
   sig
    type of_ = { le : GRing.IntegralDomain.sort rel;
                 lt : GRing.IntegralDomain.sort rel;
                 norm : (GRing.IntegralDomain.sort ->
                        GRing.IntegralDomain.sort) }

    val le :
      GRing.IntegralDomain.coq_type -> of_ -> GRing.IntegralDomain.sort rel

    val lt :
      GRing.IntegralDomain.coq_type -> of_ -> GRing.IntegralDomain.sort rel

    val norm :
      GRing.IntegralDomain.coq_type -> of_ -> GRing.IntegralDomain.sort ->
      GRing.IntegralDomain.sort

    val numMixin : GRing.IntegralDomain.coq_type -> of_ -> NumMixin.of_
   end
 end
