open Eqtype
open Ssrbool

type __ = Obj.t

module Order =
 struct
  module POrder =
   struct
    type 't0 mixin_of = { le : Equality.sort rel; lt : Equality.sort rel }

    (** val le :
        'a1 Equality.mixin_of -> 'a1 mixin_of -> Equality.sort rel **)

    let le _ m =
      m.le

    (** val lt :
        'a1 Equality.mixin_of -> 'a1 mixin_of -> Equality.sort rel **)

    let lt _ m =
      m.lt

    type 't class_of = { base : 't Choice.Choice.class_of; mixin : 't mixin_of }

    (** val base : 'a1 class_of -> 'a1 Choice.Choice.class_of **)

    let base c =
      c.base

    (** val mixin : 'a1 class_of -> 'a1 mixin_of **)

    let mixin c =
      c.mixin

    type coq_type =
      __ class_of
      (* singleton inductive, whose constructor was Pack *)

    type sort = __

    (** val coq_class : unit -> coq_type -> sort class_of **)

    let coq_class _ cT =
      cT

    (** val pack :
        unit -> Choice.Choice.coq_type -> 'a1 Choice.Choice.class_of -> 'a1
        mixin_of -> coq_type **)

    let pack _ _ b m =
      { base = (Obj.magic b); mixin = (Obj.magic m) }
   end

  (** val le : unit -> POrder.coq_type -> POrder.sort rel **)

  let le disp t =
    (POrder.coq_class disp t).POrder.mixin.POrder.le

  (** val lt : unit -> POrder.coq_type -> POrder.sort rel **)

  let lt disp t =
    (POrder.coq_class disp t).POrder.mixin.POrder.lt

  module LePOrderMixin =
   struct
    type of_ = { le : Equality.sort rel; lt : Equality.sort rel }

    (** val le : Equality.coq_type -> of_ -> Equality.sort rel **)

    let le _ o =
      o.le

    (** val lt : Equality.coq_type -> of_ -> Equality.sort rel **)

    let lt _ o =
      o.lt

    (** val porderMixin :
        Equality.coq_type -> of_ -> Equality.sort POrder.mixin_of **)

    let porderMixin _ m =
      { POrder.le = m.le; POrder.lt = m.lt }
   end

  module LtPOrderMixin =
   struct
    type of_ = { le : Equality.sort rel; lt : Equality.sort rel }

    (** val le : Equality.coq_type -> of_ -> Equality.sort rel **)

    let le _ o =
      o.le

    (** val lt : Equality.coq_type -> of_ -> Equality.sort rel **)

    let lt _ o =
      o.lt

    (** val lePOrderMixin : Equality.coq_type -> of_ -> LePOrderMixin.of_ **)

    let lePOrderMixin _ m =
      { LePOrderMixin.le = m.le; LePOrderMixin.lt = m.lt }
   end
 end
