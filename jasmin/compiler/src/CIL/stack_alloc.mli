open BinInt
open BinNums
open Bool
open Datatypes
open Byteset
open Compiler_util
open Eqtype
open Expr
open Gen_map
open Global
open Memory_model
open Pseudo_operator
open Seq
open Slh_lowering
open Slh_ops
open Sopn
open Ssralg
open Ssrbool
open Ssrfun
open Ssrnat
open Type
open Utils0
open Var0
open Warray_
open Word0
open Word_ssrZ
open Wsize
open Xseq

type __ = Obj.t

module E :
 sig
  val pass : char list

  val stk_error_gen : bool -> var_i -> pp_error -> pp_error_loc

  val stk_error : var_i -> pp_error -> pp_error_loc

  val stk_ierror : var_i -> pp_error -> pp_error_loc

  val stk_ierror_basic : var_i -> char list -> pp_error_loc

  val stk_error_no_var_gen : bool -> char list -> pp_error_loc

  val stk_error_no_var : char list -> pp_error_loc

  val stk_ierror_no_var : char list -> pp_error_loc
 end

val size_of : stype -> coq_Z

type slot = Var.var

type region = { r_slot : slot; r_align : wsize; r_writable : bool }

val region_beq : region -> region -> bool

val region_same : region -> region -> bool

val region_axiom : region Equality.axiom

val region_eqMixin : region Equality.mixin_of

val region_eqType : Equality.coq_type

module CmpR :
 sig
  val t : Equality.coq_type

  val cmp : Equality.sort -> Equality.sort -> comparison
 end

module Mr :
 sig
  module K :
   sig
    val t : Equality.coq_type

    val cmp : Equality.sort -> Equality.sort -> comparison
   end

  module Ordered :
   sig
    type t = Equality.sort

    val compare :
      Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare

    val eq_dec : Equality.sort -> Equality.sort -> bool
   end

  module Map :
   sig
    module E :
     sig
      type t = Equality.sort

      val compare :
        Equality.sort -> Equality.sort -> Equality.sort
        OrderedType.coq_Compare

      val eq_dec : Equality.sort -> Equality.sort -> bool
     end

    module Raw :
     sig
      type key = Equality.sort

      type 'elt tree =
      | Leaf
      | Node of 'elt tree * key * 'elt * 'elt tree * Int.Z_as_Int.t

      val tree_rect :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Int.Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

      val tree_rec :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Int.Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

      val height : 'a1 tree -> Int.Z_as_Int.t

      val cardinal : 'a1 tree -> nat

      val empty : 'a1 tree

      val is_empty : 'a1 tree -> bool

      val mem : Equality.sort -> 'a1 tree -> bool

      val find : Equality.sort -> 'a1 tree -> 'a1 option

      val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

      val remove_min :
        'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

      val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

      val remove : Equality.sort -> 'a1 tree -> 'a1 tree

      val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                           t_right : 'elt tree }

      val t_left : 'a1 triple -> 'a1 tree

      val t_opt : 'a1 triple -> 'a1 option

      val t_right : 'a1 triple -> 'a1 tree

      val split : Equality.sort -> 'a1 tree -> 'a1 triple

      val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

      val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

      val elements : 'a1 tree -> (key * 'a1) list

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      type 'elt enumeration =
      | End
      | More of key * 'elt * 'elt tree * 'elt enumeration

      val enumeration_rect :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2

      val enumeration_rec :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2

      val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

      val equal_more :
        ('a1 -> 'a1 -> bool) -> Equality.sort -> 'a1 -> ('a1 enumeration ->
        bool) -> 'a1 enumeration -> bool

      val equal_cont :
        ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
        enumeration -> bool

      val equal_end : 'a1 enumeration -> bool

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

      val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

      val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

      val map2_opt :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
        'a3 tree

      module Proofs :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = Equality.sort
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = Equality.sort
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : Equality.sort -> Equality.sort -> bool

            val lt_dec : Equality.sort -> Equality.sort -> bool

            val eqb : Equality.sort -> Equality.sort -> bool
           end
         end

        module L :
         sig
          module MX :
           sig
            module TO :
             sig
              type t = Equality.sort
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : Equality.sort -> Equality.sort -> bool

            val lt_dec : Equality.sort -> Equality.sort -> bool

            val eqb : Equality.sort -> Equality.sort -> bool
           end

          module PX :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = Equality.sort
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : Equality.sort -> Equality.sort -> bool

              val lt_dec : Equality.sort -> Equality.sort -> bool

              val eqb : Equality.sort -> Equality.sort -> bool
             end
           end

          type key = Equality.sort

          type 'elt t = (Equality.sort * 'elt) list

          val empty : 'a1 t

          val is_empty : 'a1 t -> bool

          val mem : key -> 'a1 t -> bool

          val find : key -> 'a1 t -> 'a1 option

          val add : key -> 'a1 -> 'a1 t -> 'a1 t

          val remove : key -> 'a1 t -> 'a1 t

          val elements : 'a1 t -> 'a1 t

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

          val option_cons :
            key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

          val map2_l :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

          val map2_r :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3
            t

          val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

          val map2_alt :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
            (key * 'a3) list

          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
            option -> 'a3 option
         end

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt tree
        | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * bool * 'elt coq_R_mem
        | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t
        | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * bool * 'elt coq_R_mem

        val coq_R_mem_rect :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2)
          -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
          'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2)
          -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
          'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

        type 'elt coq_R_find =
        | R_find_0 of 'elt tree
        | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find
        | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t
        | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find

        val coq_R_find_rect :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val coq_R_find_rec :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

        type 'elt coq_R_bal =
        | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Int.Z_as_Int.t
        | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Int.Z_as_Int.t
        | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 
           'elt * 'elt tree * Int.Z_as_Int.t
        | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Int.Z_as_Int.t
        | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Int.Z_as_Int.t
        | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 
           'elt * 'elt tree * Int.Z_as_Int.t
        | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

        val coq_R_bal_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> __ ->
          'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2)
          -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ ->
          __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
          -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __
          -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
          __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key
          -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2) -> ('a1 tree
          -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

        val coq_R_bal_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> __ ->
          'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2)
          -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ ->
          __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
          -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __
          -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
          __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key
          -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2) -> ('a1 tree
          -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

        type 'elt coq_R_add =
        | R_add_0 of 'elt tree
        | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_add
        | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t
        | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
          tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2)
          -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
          tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2)
          -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

        type 'elt coq_R_remove_min =
        | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
        | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
           * key * 'elt * 'elt tree * Int.Z_as_Int.t
           * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min * 'elt tree
           * (key * 'elt)

        val coq_R_remove_min_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) ->
          'a1 coq_R_remove_min -> 'a2

        val coq_R_remove_min_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) ->
          'a1 coq_R_remove_min -> 'a2

        type 'elt coq_R_merge =
        | R_merge_0 of 'elt tree * 'elt tree
        | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Int.Z_as_Int.t
        | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

        val coq_R_merge_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
          'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
          -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
          coq_R_merge -> 'a2

        val coq_R_merge_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
          'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
          -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
          coq_R_merge -> 'a2

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt tree
        | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_remove
        | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t
        | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_remove

        val coq_R_remove_rect :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

        type 'elt coq_R_concat =
        | R_concat_0 of 'elt tree * 'elt tree
        | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Int.Z_as_Int.t
        | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt tree * (key * 'elt)

        val coq_R_concat_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
          'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

        val coq_R_concat_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
          'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

        type 'elt coq_R_split =
        | R_split_0 of 'elt tree
        | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree
        | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t
        | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree

        val coq_R_split_rect :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option ->
          'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
          -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
          option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
          coq_R_split -> 'a2

        val coq_R_split_rec :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option ->
          'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
          -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
          option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
          coq_R_split -> 'a2

        type ('elt, 'x) coq_R_map_option =
        | R_map_option_0 of 'elt tree
        | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
           * 'x tree * ('elt, 'x) coq_R_map_option
        | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 
           'x tree * ('elt, 'x) coq_R_map_option

        val coq_R_map_option_rect :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
          'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2
          tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
          'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3

        val coq_R_map_option_rec :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
          'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2
          tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
          'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3

        type ('elt, 'x0, 'x) coq_R_map2_opt =
        | R_map2_opt_0 of 'elt tree * 'x0 tree
        | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Int.Z_as_Int.t
        | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Int.Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
           * Int.Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 
           'x tree * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt
        | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Int.Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
           * Int.Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt

        val coq_R_map2_opt_rect :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree
          -> key -> 'a2 -> 'a2 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree ->
          'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2,
          'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree ->
          key -> 'a2 -> 'a2 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree -> 'a2
          option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2,
          'a3) coq_R_map2_opt -> 'a4

        val coq_R_map2_opt_rec :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree
          -> key -> 'a2 -> 'a2 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree ->
          'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2,
          'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree ->
          key -> 'a2 -> 'a2 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree -> 'a2
          option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2,
          'a3) coq_R_map2_opt -> 'a4

        val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

        val flatten_e : 'a1 enumeration -> (key * 'a1) list
       end
     end

    type 'elt bst =
      'elt Raw.tree
      (* singleton inductive, whose constructor was Bst *)

    val this : 'a1 bst -> 'a1 Raw.tree

    type 'elt t = 'elt bst

    type key = Equality.sort

    val empty : 'a1 t

    val is_empty : 'a1 t -> bool

    val add : key -> 'a1 -> 'a1 t -> 'a1 t

    val remove : key -> 'a1 t -> 'a1 t

    val mem : key -> 'a1 t -> bool

    val find : key -> 'a1 t -> 'a1 option

    val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

    val elements : 'a1 t -> (key * 'a1) list

    val cardinal : 'a1 t -> nat

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
   end

  module Facts :
   sig
    val eqb : Equality.sort -> Equality.sort -> bool

    val coq_In_dec : 'a1 Map.t -> Map.key -> bool
   end

  type 't t = 't Map.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val get : 'a1 t -> Equality.sort -> 'a1 option

  val set : 'a1 t -> Equality.sort -> 'a1 -> 'a1 Map.t

  val remove : 'a1 t -> Equality.sort -> 'a1 Map.t

  val map : ('a1 -> 'a2) -> 'a1 Map.t -> 'a2 Map.t

  val mapi : (Map.key -> 'a1 -> 'a2) -> 'a1 Map.t -> 'a2 Map.t

  val raw_map2 :
    (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1
    Map.Raw.tree -> 'a2 Map.Raw.tree -> 'a3 Map.Raw.tree

  val elements : 'a1 Map.t -> (Map.key * 'a1) list

  val fold : (Map.key -> 'a1 -> 'a2 -> 'a2) -> 'a1 Map.t -> 'a2 -> 'a2

  val all_t : (Equality.sort -> 'a1 -> bool) -> 'a1 Map.Raw.tree -> bool

  val has_t : (Equality.sort -> 'a1 -> bool) -> 'a1 Map.Raw.tree -> bool

  val incl_t :
    (Equality.sort -> 'a1 -> bool) -> (Equality.sort -> 'a1 -> 'a2 -> bool)
    -> 'a1 Map.Raw.tree -> 'a2 Map.Raw.tree -> bool

  val all : (Equality.sort -> 'a1 -> bool) -> 'a1 t -> bool

  val has : (Equality.sort -> 'a1 -> bool) -> 'a1 t -> bool

  val incl_def :
    (Equality.sort -> 'a1 -> bool) -> (Equality.sort -> 'a1 -> 'a2 -> bool)
    -> 'a1 Map.bst -> 'a2 Map.bst -> bool

  val incl :
    (Equality.sort -> 'a1 -> 'a2 -> bool) -> 'a1 Map.bst -> 'a2 Map.bst ->
    bool

  val in_codom : Equality.coq_type -> Equality.sort -> Equality.sort t -> bool

  val map2 :
    (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2
    t -> 'a3 t

  val filter_map : (Equality.sort -> 'a1 -> 'a2 option) -> 'a1 t -> 'a2 t

  val is_emptyP : 'a1 t -> reflect

  val elementsP :
    Equality.coq_type -> (Equality.sort * Equality.sort) -> Equality.sort t
    -> reflect
 end

type zone = { z_ofs : coq_Z; z_len : coq_Z }

val internal_Z_beq : coq_Z -> coq_Z -> bool

val zone_beq : zone -> zone -> bool

val zone_eq_axiom : zone Equality.axiom

val zone_eqMixin : zone Equality.mixin_of

val zone_eqType : Equality.coq_type

val disjoint_zones : zone -> zone -> bool

type sub_region = { sr_region : region; sr_zone : zone }

val sub_region_beq : sub_region -> sub_region -> bool

val sub_region_eq_axiom : sub_region Equality.axiom

val sub_region_eqMixin : sub_region Equality.mixin_of

val sub_region_eqType : Equality.coq_type

type ptr_kind_init =
| PIdirect of Var.var * zone * v_scope
| PIregptr of Var.var
| PIstkptr of Var.var * zone * Var.var

type ptr_kind =
| Pdirect of Var.var * coq_Z * wsize * zone * v_scope
| Pregptr of Var.var
| Pstkptr of Var.var * coq_Z * wsize * zone * Var.var

type param_info = { pp_ptr : Var.var; pp_writable : bool; pp_align : wsize }

type pos_map = { vrip : Var.var; vrsp : Var.var; vxlen : Var.var;
                 globals : (coq_Z * wsize) Mvar.t; locals : ptr_kind Mvar.t;
                 vnew : SvExtra.Sv.t }

val check_align : var_i -> sub_region -> wsize -> (pp_error_loc, unit) result

val writable : var_i -> region -> (pp_error_loc, unit) result

module Region :
 sig
  type bytes_map = ByteSet.t Mvar.t

  type region_map = { var_region : sub_region Mvar.t;
                      region_var : bytes_map Mr.t }

  val var_region : region_map -> sub_region Mvar.t

  val region_var : region_map -> bytes_map Mr.t

  val empty_bytes_map : ByteSet.t Mvar.t

  val empty : region_map

  val get_sub_region :
    region_map -> var_i -> (pp_error_loc, sub_region) result

  val get_bytes_map : region -> ByteSet.t Mvar.t Mr.t -> bytes_map

  val get_bytes : Var.var -> bytes_map -> ByteSet.t

  val interval_of_zone : zone -> interval

  val get_var_bytes : ByteSet.t Mvar.t Mr.t -> region -> Var.var -> ByteSet.t

  val sub_zone_at_ofs : zone -> coq_Z option -> coq_Z -> zone

  val sub_region_at_ofs : sub_region -> coq_Z option -> coq_Z -> sub_region

  val check_valid :
    region_map -> var_i -> coq_Z option -> coq_Z -> (pp_error_loc,
    sub_region * sub_region) result

  val clear_bytes : interval -> ByteSet.t -> ByteSet.t

  val clear_bytes_map : interval -> bytes_map -> ByteSet.t Mvar.Map.t

  val set_pure_bytes :
    ByteSet.t Mvar.t Mr.t -> Var.var -> sub_region -> coq_Z option -> coq_Z
    -> ByteSet.t Mvar.t Mr.Map.t

  val set_bytes :
    ByteSet.t Mvar.t Mr.t -> var_i -> sub_region -> coq_Z option -> coq_Z ->
    (pp_error_loc, ByteSet.t Mvar.t Mr.Map.t) result

  val set_sub_region :
    region_map -> var_i -> sub_region -> coq_Z option -> coq_Z ->
    (pp_error_loc, region_map) result

  val sub_region_stkptr : slot -> wsize -> zone -> sub_region

  val set_stack_ptr :
    coq_PointerData -> region_map -> slot -> wsize -> zone -> Var.var ->
    region_map

  val check_stack_ptr :
    coq_PointerData -> ByteSet.t Mvar.t Mr.t -> slot -> wsize -> zone ->
    Var.var -> bool

  val set_word :
    region_map -> var_i -> sub_region -> wsize -> (pp_error_loc, region_map)
    result

  val set_arr_word :
    region_map -> var_i -> coq_Z option -> wsize -> (pp_error_loc,
    region_map) result

  val set_arr_call :
    region_map -> var_i -> sub_region -> (pp_error_loc, region_map) result

  val set_move_bytes :
    ByteSet.t Mvar.t Mr.t -> Var.var -> sub_region -> ByteSet.t Mvar.t
    Mr.Map.t

  val set_move_sub : region_map -> Var.var -> sub_region -> region_map

  val set_arr_sub :
    region_map -> var_i -> coq_Z -> coq_Z -> Equality.sort -> (pp_error_loc,
    region_map) result

  val set_move : region_map -> Var.var -> sub_region -> region_map

  val set_arr_init : region_map -> Var.var -> sub_region -> region_map

  val incl_bytes_map : region -> bytes_map -> bytes_map -> bool

  val incl : region_map -> region_map -> bool

  val merge_bytes :
    Var.var -> ByteSet.t option -> ByteSet.t option -> ByteSet.t option

  val merge_bytes_map :
    region -> bytes_map option -> bytes_map option -> ByteSet.t Mvar.t option

  val merge : region_map -> region_map -> region_map
 end

val mul : coq_PointerData -> pexpr -> pexpr -> pexpr

val add : coq_PointerData -> pexpr -> pexpr -> pexpr

val mk_ofs : coq_PointerData -> arr_access -> wsize -> pexpr -> coq_Z -> pexpr

val mk_ofsi : arr_access -> wsize -> pexpr -> coq_Z option

val assert_check : bool -> bool -> 'a1 -> ('a1, unit) result

type vptr_kind =
| VKglob of (coq_Z * wsize)
| VKptr of ptr_kind

type 'asm_op stack_alloc_params = { sap_mov_ofs : (lval -> assgn_tag ->
                                                  vptr_kind -> pexpr -> coq_Z
                                                  -> 'asm_op instr_r option);
                                    sap_immediate : (var_i -> coq_Z ->
                                                    'asm_op instr_r);
                                    sap_swap : (assgn_tag -> var_i -> var_i
                                               -> var_i -> var_i -> 'asm_op
                                               instr_r) }

type mov_kind =
| MK_LEA
| MK_MOV

val mk_mov : vptr_kind -> mov_kind

val get_global : pos_map -> var_i -> (pp_error_loc, coq_Z * wsize) result

val get_local : pos_map -> Var.var -> ptr_kind option

val check_diff : pos_map -> var_i -> (pp_error_loc, unit) result

val check_var : pos_map -> var_i -> (pp_error_loc, unit) result

val with_var : var_i -> Var.var -> var_i

val base_ptr : pos_map -> v_scope -> Var.var

val addr_from_pk :
  pos_map -> var_i -> ptr_kind -> (pp_error_loc, var_i * coq_Z) result

val addr_from_vpk :
  pos_map -> var_i -> vptr_kind -> (pp_error_loc, var_i * coq_Z) result

val mk_addr_ptr :
  coq_PointerData -> pos_map -> var_i -> arr_access -> wsize -> ptr_kind ->
  pexpr -> (pp_error_loc, var_i * pexpr) result

val mk_addr :
  coq_PointerData -> pos_map -> var_i -> arr_access -> wsize -> vptr_kind ->
  pexpr -> (pp_error_loc, var_i * pexpr) result

val get_var_kind : pos_map -> gvar -> (pp_error_loc, vptr_kind option) result

val sub_region_full : Var.var -> region -> sub_region

val sub_region_glob : slot -> wsize -> sub_region

val check_vpk :
  Region.region_map -> var_i -> vptr_kind -> coq_Z option -> coq_Z ->
  (pp_error_loc, sub_region * sub_region) result

val check_vpk_word :
  Region.region_map -> var_i -> vptr_kind -> coq_Z option -> wsize ->
  (pp_error_loc, unit) result

val alloc_e :
  coq_PointerData -> pos_map -> Region.region_map -> pexpr -> (pp_error_loc,
  pexpr) result

val alloc_es :
  coq_PointerData -> pos_map -> Region.region_map -> pexpr list ->
  (pp_error_loc, pexpr list) result

val sub_region_direct : slot -> wsize -> Equality.sort -> zone -> sub_region

val sub_region_stack : slot -> wsize -> zone -> sub_region

val sub_region_pk : var_i -> ptr_kind -> (pp_error_loc, sub_region) result

val alloc_lval :
  coq_PointerData -> pos_map -> Region.region_map -> lval -> stype ->
  (pp_error_loc, Region.region_map * lval) result

val nop : 'a1 asmOp -> 'a1 instr_r

val is_nop :
  coq_PointerData -> (((slot * wsize) * zone) * Var.var) option ->
  Region.region_map -> Var.var -> sub_region -> bool

val get_addr :
  coq_PointerData -> 'a1 asmOp -> 'a1 stack_alloc_params ->
  (((slot * wsize) * zone) * Var.var) option -> Region.region_map -> Var.var
  -> lval -> assgn_tag -> sub_region -> vptr_kind -> pexpr -> coq_Z ->
  Region.region_map * 'a1 instr_r option

val get_ofs_sub :
  arr_access -> wsize -> var_i -> pexpr -> (pp_error_loc, coq_Z) result

val get_Lvar_sub :
  lval -> (pp_error_loc, var_i * (coq_Z * coq_Z) option) result

val get_Pvar_sub :
  pexpr -> (pp_error_loc, gvar * (coq_Z * coq_Z) option) result

val is_stack_ptr :
  vptr_kind -> ((((Var.var * coq_Z) * wsize) * zone) * Var.var) option

val mk_addr_pexpr :
  coq_PointerData -> pos_map -> ByteSet.t Mvar.t Mr.t -> var_i -> vptr_kind
  -> (pp_error_loc, pexpr * coq_Z) result

val alloc_array_move :
  coq_PointerData -> 'a1 asmOp -> 'a1 stack_alloc_params -> pos_map ->
  Region.region_map -> lval -> assgn_tag -> pexpr -> (pp_error_loc,
  Region.region_map * 'a1 instr_r) result

val is_protect_ptr_fail :
  'a1 asmOp -> lval list -> 'a1 sopn -> pexpr list ->
  ((lval * pexpr) * pexpr) option

val lower_protect_ptr_fail :
  coq_PointerData -> 'a1 asmOp -> 'a1 sh_params -> instr_info -> lval list ->
  assgn_tag -> pexpr list -> 'a1 instr_r cexec

val alloc_protect_ptr :
  coq_PointerData -> 'a1 asmOp -> 'a1 sh_params -> pos_map ->
  Region.region_map -> instr_info -> lval -> assgn_tag -> pexpr -> pexpr ->
  (pp_error_loc, Region.region_map * 'a1 instr_r) result

val alloc_array_move_init :
  coq_PointerData -> 'a1 asmOp -> 'a1 stack_alloc_params -> pos_map ->
  Region.region_map -> lval -> assgn_tag -> pexpr -> (pp_error_loc,
  Region.region_map * 'a1 instr_r) result

val bad_lval_number : pp_error_loc

val alloc_lvals :
  coq_PointerData -> pos_map -> Region.region_map -> lval list -> stype list
  -> (pp_error_loc, Region.region_map * lval list) result

val loop2 :
  'a1 asmOp -> instr_info -> (Region.region_map ->
  ((Region.region_map * Region.region_map) * (pexpr * ('a1 instr list
  list * 'a1 instr list list))) cexec) -> nat -> Region.region_map ->
  (pp_error_loc, Region.region_map * (pexpr * ('a1 instr list list * 'a1
  instr list list))) result

type stk_alloc_oracle_t = { sao_align : wsize; sao_size : coq_Z;
                            sao_ioff : coq_Z; sao_extra_size : coq_Z;
                            sao_max_size : coq_Z; sao_max_call_depth : 
                            coq_Z; sao_params : param_info option list;
                            sao_return : nat option list;
                            sao_slots : ((Var.var * wsize) * coq_Z) list;
                            sao_alloc : (Var.var * ptr_kind_init) list;
                            sao_to_save : (Var.var * coq_Z) list;
                            sao_rsp : saved_stack;
                            sao_return_address : return_address_location }

val sao_frame_size : stk_alloc_oracle_t -> coq_Z

val get_Pvar : pexpr -> (pp_error_loc, gvar) result

val set_clear_bytes :
  ByteSet.t Mvar.t Mr.t -> sub_region -> coq_Z option -> coq_Z -> ByteSet.t
  Mvar.t Mr.Map.t

val set_clear_pure :
  Region.region_map -> sub_region -> coq_Z option -> coq_Z ->
  Region.region_map

val set_clear :
  Region.region_map -> var_i -> sub_region -> coq_Z option -> coq_Z ->
  (pp_error_loc, Region.region_map) result

val alloc_call_arg_aux :
  pos_map -> Region.region_map -> Region.region_map -> param_info option ->
  pexpr -> (pp_error_loc, Region.region_map * ((bool * sub_region)
  option * pexpr)) result

val alloc_call_args_aux :
  pos_map -> Region.region_map -> param_info option list -> pexpr list ->
  (pp_error_loc, Region.region_map * ((bool * sub_region) option * pexpr)
  list) result

val disj_sub_regions : sub_region -> sub_region -> bool

val check_all_disj :
  sub_region list -> sub_region list -> ((bool * sub_region) option * pexpr)
  list -> bool

val alloc_call_args :
  pos_map -> Region.region_map -> param_info option list -> pexpr list ->
  (pp_error_loc, Region.region_map * ((bool * sub_region) option * pexpr)
  list) result

val check_lval_reg_call : pos_map -> lval -> (pp_error_loc, unit) result

val get_regptr : pos_map -> var_i -> (pp_error_loc, var_i) result

val alloc_lval_call :
  coq_PointerData -> pos_map -> ((bool * sub_region) option * pexpr) list ->
  Region.region_map -> lval -> nat option -> (pp_error_loc,
  Region.region_map * lval) result

val alloc_call_res :
  coq_PointerData -> pos_map -> Region.region_map -> ((bool * sub_region)
  option * pexpr) list -> nat option list -> lval list -> (pp_error_loc,
  Region.region_map * lval list) result

val alloc_call :
  coq_PointerData -> 'a1 asmOp -> bool -> pos_map -> (funname ->
  stk_alloc_oracle_t) -> stk_alloc_oracle_t -> Region.region_map -> lval list
  -> funname -> pexpr list -> (pp_error_loc, Region.region_map * 'a1 instr_r)
  result

val alloc_syscall :
  coq_PointerData -> 'a1 asmOp -> 'a1 stack_alloc_params -> pos_map ->
  instr_info -> Region.region_map -> lval list ->
  BinNums.positive Syscall_t.syscall_t -> pexpr list -> (pp_error_loc,
  Region.region_map * 'a1 instr list) result

val is_swap_array : 'a1 asmOp -> 'a1 sopn -> bool

val alloc_array_swap :
  'a1 asmOp -> 'a1 stack_alloc_params -> pos_map -> Region.region_map -> lval
  list -> assgn_tag -> pexpr list -> (pp_error_loc, Region.region_map * 'a1
  instr_r) result

val alloc_i :
  coq_PointerData -> coq_MSFsize -> 'a1 asmOp -> bool -> 'a1 sh_params -> 'a1
  stack_alloc_params -> pos_map -> (funname -> stk_alloc_oracle_t) ->
  stk_alloc_oracle_t -> Region.region_map -> 'a1 instr ->
  (Region.region_map * 'a1 instr list) cexec

val init_stack_layout :
  (coq_Z * wsize) Mvar.t -> stk_alloc_oracle_t -> (pp_error_loc,
  (coq_Z * wsize) Mvar.t) result

val add_alloc :
  coq_PointerData -> (coq_Z * wsize) Mvar.t -> (coq_Z * wsize) Mvar.t ->
  (Var.var * ptr_kind_init) -> ((ptr_kind
  Mvar.t * Region.region_map) * SvExtra.Sv.t) -> (pp_error_loc, (ptr_kind
  Mvar.Map.t * Region.region_map) * SvExtra.Sv.t) result

val init_local_map :
  coq_PointerData -> SvExtra.Sv.elt -> SvExtra.Sv.elt -> SvExtra.Sv.elt ->
  (coq_Z * wsize) Mvar.t -> (coq_Z * wsize) Mvar.t -> stk_alloc_oracle_t ->
  (pp_error_loc, (ptr_kind Mvar.t * Region.region_map) * SvExtra.Sv.t) result

val check_result :
  pos_map -> Region.region_map -> Equality.sort option list -> var_i list ->
  nat option -> var_i -> (pp_error_loc, var_i) result

val check_all_writable_regions_returned :
  sub_region option list -> nat option list -> bool

val check_results :
  pos_map -> Region.region_map -> Equality.sort option list -> var_i list ->
  nat option list -> var_i list -> (pp_error_loc, var_i list) result

val init_param :
  coq_PointerData -> (coq_Z * wsize) Mvar.t -> (coq_Z * wsize) Mvar.t ->
  ((SvExtra.Sv.t * ptr_kind Mvar.t) * Region.region_map) -> param_info option
  -> var_i -> (pp_error_loc, ((SvExtra.Sv.t * ptr_kind
  Mvar.Map.t) * Region.region_map) * (sub_region option * var_i)) result

val init_params :
  coq_PointerData -> (coq_Z * wsize) Mvar.t -> (coq_Z * wsize) Mvar.t ->
  SvExtra.Sv.t -> ptr_kind Mvar.t -> Region.region_map -> param_info option
  list -> var_i list -> (pp_error_loc, ((SvExtra.Sv.t * ptr_kind
  Mvar.t) * Region.region_map) * (sub_region option * var_i) list) result

val alloc_fd_aux :
  coq_PointerData -> coq_MSFsize -> 'a1 asmOp -> bool -> 'a1 sh_params -> 'a1
  stack_alloc_params -> sprog_extra -> (coq_Z * wsize) Mvar.t ->
  (Ident.Ident.name -> stype -> Ident.Ident.ident) -> (funname ->
  stk_alloc_oracle_t) -> stk_alloc_oracle_t -> ('a1, unit) _fundef -> 'a1
  _ufundef cexec

val alloc_fd :
  coq_PointerData -> coq_MSFsize -> 'a1 asmOp -> bool -> 'a1 sh_params -> 'a1
  stack_alloc_params -> sprog_extra -> (coq_Z * wsize) Mvar.t ->
  (Ident.Ident.name -> stype -> Ident.Ident.ident) -> (funname ->
  stk_alloc_oracle_t) -> funname -> ('a1, unit) _fundef -> (pp_error_loc, 'a1
  sfundef) result

val ptake : positive -> 'a1 list -> 'a1 list -> ('a1 list * 'a1 list) option

val ztake : coq_Z -> 'a1 list -> ('a1 list * 'a1 list) option

val check_glob :
  GRing.ComRing.sort list -> glob_value -> (pp_error_loc, unit) result

val size_glob : glob_value -> coq_Z

val init_map :
  ((Var.var * wsize) * coq_Z) list -> GRing.ComRing.sort list -> glob_decl
  list -> (coq_Z * wsize) Mvar.t cexec

val alloc_prog :
  coq_PointerData -> coq_MSFsize -> 'a1 asmOp -> bool -> 'a1 sh_params -> 'a1
  stack_alloc_params -> (Ident.Ident.name -> stype -> Ident.Ident.ident) ->
  Ident.Ident.ident -> Ident.Ident.ident -> GRing.ComRing.sort list ->
  ((Var.var * wsize) * coq_Z) list -> (funname -> stk_alloc_oracle_t) -> 'a1
  _uprog -> 'a1 _sprog cexec
