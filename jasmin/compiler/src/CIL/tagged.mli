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

module Tagged :
 functor (C:TaggedCore) ->
 sig
  type t = C.t

  val tag : t -> Uint63.t

  val t_eqb : t -> t -> bool

  val t_eq_axiom : t Equality.axiom

  val t_eqMixin : t Equality.mixin_of

  val t_eqType : Equality.coq_type

  val cmp : t -> t -> comparison

  module CmpT :
   sig
    val t : Equality.coq_type

    val cmp : Equality.sort -> Equality.sort -> comparison
   end

  module Mt :
   MAP

  module St :
   sig
    module Ordered :
     sig
      type t = Equality.sort

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> bool
     end

    module Raw :
     sig
      type elt = Equality.sort

      type tree =
      | Leaf
      | Node of Int.Z_as_Int.t * tree * Equality.sort * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : Equality.sort -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux : Equality.sort list -> tree -> Equality.sort list

      val elements : tree -> Equality.sort list

      val rev_elements_aux : Equality.sort list -> tree -> Equality.sort list

      val rev_elements : tree -> Equality.sort list

      val cardinal : tree -> nat

      val maxdepth : tree -> nat

      val mindepth : tree -> nat

      val for_all : (elt -> bool) -> tree -> bool

      val exists_ : (elt -> bool) -> tree -> bool

      type enumeration =
      | End
      | More of elt * tree * enumeration

      val cons : tree -> enumeration -> enumeration

      val compare_more :
        Equality.sort -> (enumeration -> comparison) -> enumeration ->
        comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl : (tree -> bool) -> Equality.sort -> tree -> bool

      val subsetr : (tree -> bool) -> Equality.sort -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val height : t -> Int.Z_as_Int.t

      val singleton : Equality.sort -> tree

      val create : t -> Equality.sort -> t -> tree

      val assert_false : t -> Equality.sort -> t -> tree

      val bal : t -> Equality.sort -> t -> tree

      val add : Equality.sort -> tree -> tree

      val join : tree -> elt -> t -> t

      val remove_min : tree -> elt -> t -> t * elt

      val merge : tree -> tree -> tree

      val remove : Equality.sort -> tree -> tree

      val concat : tree -> tree -> tree

      type triple = { t_left : t; t_in : bool; t_right : t }

      val t_left : triple -> t

      val t_in : triple -> bool

      val t_right : triple -> t

      val split : Equality.sort -> tree -> triple

      val inter : tree -> tree -> tree

      val diff : tree -> tree -> tree

      val union : tree -> tree -> tree

      val filter : (elt -> bool) -> tree -> tree

      val partition : (elt -> bool) -> t -> t * t

      val ltb_tree : Equality.sort -> tree -> bool

      val gtb_tree : Equality.sort -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = Equality.sort

            val compare : Equality.sort -> Equality.sort -> comparison

            val eq_dec : Equality.sort -> Equality.sort -> bool
           end

          module TO :
           sig
            type t = Equality.sort

            val compare : Equality.sort -> Equality.sort -> comparison

            val eq_dec : Equality.sort -> Equality.sort -> bool
           end
         end

        val eq_dec : Equality.sort -> Equality.sort -> bool

        val lt_dec : Equality.sort -> Equality.sort -> bool

        val eqb : Equality.sort -> Equality.sort -> bool
       end

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = Equality.sort

              val compare : Equality.sort -> Equality.sort -> comparison

              val eq_dec : Equality.sort -> Equality.sort -> bool
             end

            module TO :
             sig
              type t = Equality.sort

              val compare : Equality.sort -> Equality.sort -> comparison

              val eq_dec : Equality.sort -> Equality.sort -> bool
             end
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      type coq_R_bal =
      | R_bal_0 of t * Equality.sort * t
      | R_bal_1 of t * Equality.sort * t * Int.Z_as_Int.t * tree
         * Equality.sort * tree
      | R_bal_2 of t * Equality.sort * t * Int.Z_as_Int.t * tree
         * Equality.sort * tree
      | R_bal_3 of t * Equality.sort * t * Int.Z_as_Int.t * tree
         * Equality.sort * tree * Int.Z_as_Int.t * tree * Equality.sort * 
         tree
      | R_bal_4 of t * Equality.sort * t
      | R_bal_5 of t * Equality.sort * t * Int.Z_as_Int.t * tree
         * Equality.sort * tree
      | R_bal_6 of t * Equality.sort * t * Int.Z_as_Int.t * tree
         * Equality.sort * tree
      | R_bal_7 of t * Equality.sort * t * Int.Z_as_Int.t * tree
         * Equality.sort * tree * Int.Z_as_Int.t * tree * Equality.sort * 
         tree
      | R_bal_8 of t * Equality.sort * t

      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree
         * Equality.sort * tree * (t * elt) * coq_R_remove_min * t * 
         elt

      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
         * tree
      | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
         * tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * 
         elt

      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
         * tree
      | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
         * tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * 
         elt

      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
         * tree
      | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
         * tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * 
         bool * t * tree * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
         * tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * 
         bool * t * tree * coq_R_inter * tree * coq_R_inter

      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * tree
      | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
         * tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * 
         bool * t * tree * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
         * tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * 
         bool * t * tree * coq_R_diff * tree * coq_R_diff

      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
         * tree
      | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
         * tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * 
         bool * t * tree * coq_R_union * tree * coq_R_union
     end

    module E :
     sig
      type t = Equality.sort

      val compare : Equality.sort -> Equality.sort -> comparison

      val eq_dec : Equality.sort -> Equality.sort -> bool
     end

    type elt = Equality.sort

    type t_ = Raw.t
      (* singleton inductive, whose constructor was Mkt *)

    val this : t_ -> Raw.t

    type t = t_

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val remove : elt -> t -> t

    val singleton : elt -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val empty : t

    val is_empty : t -> bool

    val elements : t -> elt list

    val choose : t -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val cardinal : t -> nat

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val eq_dec : t -> t -> bool

    val compare : t -> t -> comparison

    val min_elt : t -> elt option

    val max_elt : t -> elt option
   end

  module StP :
   sig
    module MP :
     sig
      module Dec :
       sig
        module F :
         sig
          val eqb : Equality.sort -> Equality.sort -> bool
         end

        module MSetLogicalFacts :
         sig
         end

        module MSetDecideAuxiliary :
         sig
         end

        module MSetDecideTestCases :
         sig
         end
       end

      module FM :
       sig
        val eqb : Equality.sort -> Equality.sort -> bool
       end

      val coq_In_dec : St.elt -> St.t -> bool

      val of_list : St.elt list -> St.t

      val to_list : St.t -> St.elt list

      val fold_rec :
        (St.elt -> 'a1 -> 'a1) -> 'a1 -> St.t -> (St.t -> __ -> 'a2) ->
        (St.elt -> 'a1 -> St.t -> St.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_bis :
        (St.elt -> 'a1 -> 'a1) -> 'a1 -> St.t -> (St.t -> St.t -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2 -> (St.elt -> 'a1 -> St.t -> __ -> __ -> 'a2 ->
        'a2) -> 'a2

      val fold_rec_nodep :
        (St.elt -> 'a1 -> 'a1) -> 'a1 -> St.t -> 'a2 -> (St.elt -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (St.elt -> 'a1 -> 'a1) -> 'a1 -> (St.t -> St.t -> 'a1 -> __ -> 'a2 ->
        'a2) -> 'a2 -> (St.elt -> 'a1 -> St.t -> __ -> 'a2 -> 'a2) -> St.t ->
        'a2

      val fold_rel :
        (St.elt -> 'a1 -> 'a1) -> (St.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
        St.t -> 'a3 -> (St.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (St.t -> __ -> 'a1) -> (St.t -> St.t -> 'a1 -> St.elt -> __ -> __ ->
        'a1) -> St.t -> 'a1

      val set_induction_bis :
        (St.t -> St.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (St.elt -> St.t -> __ ->
        'a1 -> 'a1) -> St.t -> 'a1

      val cardinal_inv_2 : St.t -> nat -> St.elt

      val cardinal_inv_2b : St.t -> St.elt
     end

    val choose_mem_3 : St.t -> St.elt

    val set_rec :
      (St.t -> St.t -> __ -> 'a1 -> 'a1) -> (St.t -> St.elt -> __ -> 'a1 ->
      'a1) -> 'a1 -> St.t -> 'a1

    val for_all_mem_4 : (St.elt -> bool) -> St.t -> St.elt

    val exists_mem_4 : (St.elt -> bool) -> St.t -> St.elt

    val sum : (St.elt -> nat) -> St.t -> nat
   end

  module StD :
   sig
    module F :
     sig
      val eqb : Equality.sort -> Equality.sort -> bool
     end

    module MSetLogicalFacts :
     sig
     end

    module MSetDecideAuxiliary :
     sig
     end

    module MSetDecideTestCases :
     sig
     end
   end
 end
