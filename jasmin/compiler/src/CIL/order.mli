open Eqtype
open Ssrbool

type __ = Obj.t

module Order :
 sig
  module POrder :
   sig
    type 't0 mixin_of = { le : Equality.sort rel; lt : Equality.sort rel }

    val le : 'a1 Equality.mixin_of -> 'a1 mixin_of -> Equality.sort rel

    val lt : 'a1 Equality.mixin_of -> 'a1 mixin_of -> Equality.sort rel

    type 't class_of = { base : 't Choice.Choice.class_of; mixin : 't mixin_of }

    val base : 'a1 class_of -> 'a1 Choice.Choice.class_of

    val mixin : 'a1 class_of -> 'a1 mixin_of

    type coq_type =
      __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    val coq_class : unit -> coq_type -> sort class_of

    val pack :
      unit -> Choice.Choice.coq_type -> 'a1 Choice.Choice.class_of -> 'a1
      mixin_of -> coq_type
   end

  val le : unit -> POrder.coq_type -> POrder.sort rel

  val lt : unit -> POrder.coq_type -> POrder.sort rel

  module LePOrderMixin :
   sig
    type of_ = { le : Equality.sort rel; lt : Equality.sort rel }

    val le : Equality.coq_type -> of_ -> Equality.sort rel

    val lt : Equality.coq_type -> of_ -> Equality.sort rel

    val porderMixin :
      Equality.coq_type -> of_ -> Equality.sort POrder.mixin_of
   end

  module LtPOrderMixin :
   sig
    type of_ = { le : Equality.sort rel; lt : Equality.sort rel }

    val le : Equality.coq_type -> of_ -> Equality.sort rel

    val lt : Equality.coq_type -> of_ -> Equality.sort rel

    val lePOrderMixin : Equality.coq_type -> of_ -> LePOrderMixin.of_
   end
 end
