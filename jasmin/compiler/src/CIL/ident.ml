open Bool
open Datatypes
open PrimInt63
open Eqtype
open Gen_map
open Wsize

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module type CORE_IDENT =
 sig
  type t

  val tag : t -> Uint63.t

  type name

  val id_name : t -> name

  val id_kind : t -> v_kind

  val name_of_string : char list -> name

  val string_of_name : name -> char list

  val spill_to_mmx : t -> bool
 end

module Cident =
 struct
  type t = CoreIdent.Cident.t

  (** val tag : t -> Uint63.t **)

  let tag = CoreIdent.Cident.tag

  (** val tagI : __ **)

  let tagI =
    __

  type name = CoreIdent.Cident.name

  (** val id_name : t -> name **)

  let id_name = CoreIdent.Cident.id_name

  (** val id_kind : t -> v_kind **)

  let id_kind = CoreIdent.Cident.id_kind

  (** val name_of_string : char list -> Uint63.t **)

  let name_of_string = CoreIdent.Cident.name_of_string

  (** val string_of_name : name -> char list **)

  let string_of_name = CoreIdent.Cident.string_of_name

  (** val spill_to_mmx : t -> bool **)

  let spill_to_mmx = CoreIdent.Cident.spill_to_mmx
 end

module Tident = Tagged.Tagged(Cident)

(** val ident_eqType : Equality.coq_type **)

let ident_eqType =
  { Equality.op = (fun x y ->
    PrimInt63.eqb (Cident.tag (Obj.magic x)) (Cident.tag (Obj.magic y)));
    Equality.mixin_of__1 = (Obj.magic Tident.t_eq_axiom) }

module WrapIdent =
 struct
  type t = CoreIdent.Cident.t

  type name = CoreIdent.Cident.name
 end

module type IDENT =
 sig
  type ident = WrapIdent.t

  module Mid :
   MAP
 end

module Ident =
 struct
  type ident = WrapIdent.t

  type name = WrapIdent.name

  (** val id_name : ident -> name **)

  let id_name =
    Cident.id_name

  (** val id_kind : ident -> v_kind **)

  let id_kind =
    Cident.id_kind

  module Mid = Tident.Mt

  (** val name_of_string : char list -> name **)

  let name_of_string =
    Cident.name_of_string

  (** val string_of_name : name -> char list **)

  let string_of_name =
    Cident.string_of_name

  (** val spill_to_mmx : ident -> bool **)

  let spill_to_mmx =
    Cident.spill_to_mmx
 end
