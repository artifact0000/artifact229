open BinInt
open BinNums
open Bool
open Datatypes
open Div
open Eqtype
open Global
open Seq
open Sopn
open Ssralg
open Ssrbool
open Ssrfun
open Type
open Utils0
open Var0
open Warray_
open Word0
open Word_ssrZ
open Wsize

type __ = Obj.t

type cmp_kind =
| Cmp_int
| Cmp_w of signedness * wsize

type op_kind =
| Op_int
| Op_w of wsize

type sop1 =
| Oword_of_int of wsize
| Oint_of_word of wsize
| Osignext of wsize * wsize
| Ozeroext of wsize * wsize
| Onot
| Olnot of wsize
| Oneg of op_kind

type sop2 =
| Obeq
| Oand
| Oor
| Oadd of op_kind
| Omul of op_kind
| Osub of op_kind
| Odiv of cmp_kind
| Omod of cmp_kind
| Oland of wsize
| Olor of wsize
| Olxor of wsize
| Olsr of wsize
| Olsl of op_kind
| Oasr of op_kind
| Oror of wsize
| Orol of wsize
| Oeq of op_kind
| Oneq of op_kind
| Olt of cmp_kind
| Ole of cmp_kind
| Ogt of cmp_kind
| Oge of cmp_kind
| Ovadd of velem * wsize
| Ovsub of velem * wsize
| Ovmul of velem * wsize
| Ovlsr of velem * wsize
| Ovlsl of velem * wsize
| Ovasr of velem * wsize

type combine_flags =
| CF_LT of signedness
| CF_LE of signedness
| CF_EQ
| CF_NEQ
| CF_GE of signedness
| CF_GT of signedness

type opN =
| Opack of wsize * pelem
| Ocombine_flags of combine_flags

(** val internal_op_kind_beq : op_kind -> op_kind -> bool **)

let internal_op_kind_beq x y =
  match x with
  | Op_int -> (match y with
               | Op_int -> true
               | Op_w _ -> false)
  | Op_w x0 -> (match y with
                | Op_int -> false
                | Op_w x1 -> wsize_beq x0 x1)

(** val sop1_beq : sop1 -> sop1 -> bool **)

let sop1_beq x y =
  match x with
  | Oword_of_int x0 ->
    (match y with
     | Oword_of_int x1 -> wsize_beq x0 x1
     | _ -> false)
  | Oint_of_word x0 ->
    (match y with
     | Oint_of_word x1 -> wsize_beq x0 x1
     | _ -> false)
  | Osignext (x0, x1) ->
    (match y with
     | Osignext (x2, x3) -> (&&) (wsize_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | Ozeroext (x0, x1) ->
    (match y with
     | Ozeroext (x2, x3) -> (&&) (wsize_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | Onot -> (match y with
             | Onot -> true
             | _ -> false)
  | Olnot x0 -> (match y with
                 | Olnot x1 -> wsize_beq x0 x1
                 | _ -> false)
  | Oneg x0 ->
    (match y with
     | Oneg x1 -> internal_op_kind_beq x0 x1
     | _ -> false)

(** val sop1_eq_dec : sop1 -> sop1 -> bool **)

let sop1_eq_dec x y =
  let b = sop1_beq x y in if b then true else false

(** val sop1_eq_axiom : sop1 Equality.axiom **)

let sop1_eq_axiom =
  eq_axiom_of_scheme sop1_beq

(** val sop1_eqMixin : sop1 Equality.mixin_of **)

let sop1_eqMixin =
  { Equality.op = sop1_beq; Equality.mixin_of__1 = sop1_eq_axiom }

(** val sop1_eqType : Equality.coq_type **)

let sop1_eqType =
  Obj.magic sop1_eqMixin

(** val internal_velem_beq : velem -> velem -> bool **)

let internal_velem_beq x y =
  match x with
  | VE8 -> (match y with
            | VE8 -> true
            | _ -> false)
  | VE16 -> (match y with
             | VE16 -> true
             | _ -> false)
  | VE32 -> (match y with
             | VE32 -> true
             | _ -> false)
  | VE64 -> (match y with
             | VE64 -> true
             | _ -> false)

(** val internal_signedness_beq : signedness -> signedness -> bool **)

let internal_signedness_beq x y =
  match x with
  | Signed -> (match y with
               | Signed -> true
               | Unsigned -> false)
  | Unsigned -> (match y with
                 | Signed -> false
                 | Unsigned -> true)

(** val internal_cmp_kind_beq : cmp_kind -> cmp_kind -> bool **)

let internal_cmp_kind_beq x y =
  match x with
  | Cmp_int -> (match y with
                | Cmp_int -> true
                | Cmp_w (_, _) -> false)
  | Cmp_w (x0, x1) ->
    (match y with
     | Cmp_int -> false
     | Cmp_w (x2, x3) ->
       (&&) (internal_signedness_beq x0 x2) (wsize_beq x1 x3))

(** val sop2_beq : sop2 -> sop2 -> bool **)

let sop2_beq x y =
  match x with
  | Obeq -> (match y with
             | Obeq -> true
             | _ -> false)
  | Oand -> (match y with
             | Oand -> true
             | _ -> false)
  | Oor -> (match y with
            | Oor -> true
            | _ -> false)
  | Oadd x0 ->
    (match y with
     | Oadd x1 -> internal_op_kind_beq x0 x1
     | _ -> false)
  | Omul x0 ->
    (match y with
     | Omul x1 -> internal_op_kind_beq x0 x1
     | _ -> false)
  | Osub x0 ->
    (match y with
     | Osub x1 -> internal_op_kind_beq x0 x1
     | _ -> false)
  | Odiv x0 ->
    (match y with
     | Odiv x1 -> internal_cmp_kind_beq x0 x1
     | _ -> false)
  | Omod x0 ->
    (match y with
     | Omod x1 -> internal_cmp_kind_beq x0 x1
     | _ -> false)
  | Oland x0 -> (match y with
                 | Oland x1 -> wsize_beq x0 x1
                 | _ -> false)
  | Olor x0 -> (match y with
                | Olor x1 -> wsize_beq x0 x1
                | _ -> false)
  | Olxor x0 -> (match y with
                 | Olxor x1 -> wsize_beq x0 x1
                 | _ -> false)
  | Olsr x0 -> (match y with
                | Olsr x1 -> wsize_beq x0 x1
                | _ -> false)
  | Olsl x0 ->
    (match y with
     | Olsl x1 -> internal_op_kind_beq x0 x1
     | _ -> false)
  | Oasr x0 ->
    (match y with
     | Oasr x1 -> internal_op_kind_beq x0 x1
     | _ -> false)
  | Oror x0 -> (match y with
                | Oror x1 -> wsize_beq x0 x1
                | _ -> false)
  | Orol x0 -> (match y with
                | Orol x1 -> wsize_beq x0 x1
                | _ -> false)
  | Oeq x0 -> (match y with
               | Oeq x1 -> internal_op_kind_beq x0 x1
               | _ -> false)
  | Oneq x0 ->
    (match y with
     | Oneq x1 -> internal_op_kind_beq x0 x1
     | _ -> false)
  | Olt x0 ->
    (match y with
     | Olt x1 -> internal_cmp_kind_beq x0 x1
     | _ -> false)
  | Ole x0 ->
    (match y with
     | Ole x1 -> internal_cmp_kind_beq x0 x1
     | _ -> false)
  | Ogt x0 ->
    (match y with
     | Ogt x1 -> internal_cmp_kind_beq x0 x1
     | _ -> false)
  | Oge x0 ->
    (match y with
     | Oge x1 -> internal_cmp_kind_beq x0 x1
     | _ -> false)
  | Ovadd (x0, x1) ->
    (match y with
     | Ovadd (x2, x3) -> (&&) (internal_velem_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | Ovsub (x0, x1) ->
    (match y with
     | Ovsub (x2, x3) -> (&&) (internal_velem_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | Ovmul (x0, x1) ->
    (match y with
     | Ovmul (x2, x3) -> (&&) (internal_velem_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | Ovlsr (x0, x1) ->
    (match y with
     | Ovlsr (x2, x3) -> (&&) (internal_velem_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | Ovlsl (x0, x1) ->
    (match y with
     | Ovlsl (x2, x3) -> (&&) (internal_velem_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | Ovasr (x0, x1) ->
    (match y with
     | Ovasr (x2, x3) -> (&&) (internal_velem_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)

(** val sop2_eq_dec : sop2 -> sop2 -> bool **)

let sop2_eq_dec x y =
  let b = sop2_beq x y in if b then true else false

(** val sop2_eq_axiom : sop2 Equality.axiom **)

let sop2_eq_axiom =
  eq_axiom_of_scheme sop2_beq

(** val sop2_eqMixin : sop2 Equality.mixin_of **)

let sop2_eqMixin =
  { Equality.op = sop2_beq; Equality.mixin_of__1 = sop2_eq_axiom }

(** val sop2_eqType : Equality.coq_type **)

let sop2_eqType =
  Obj.magic sop2_eqMixin

(** val internal_combine_flags_beq :
    combine_flags -> combine_flags -> bool **)

let internal_combine_flags_beq x y =
  match x with
  | CF_LT x0 ->
    (match y with
     | CF_LT x1 -> internal_signedness_beq x0 x1
     | _ -> false)
  | CF_LE x0 ->
    (match y with
     | CF_LE x1 -> internal_signedness_beq x0 x1
     | _ -> false)
  | CF_EQ -> (match y with
              | CF_EQ -> true
              | _ -> false)
  | CF_NEQ -> (match y with
               | CF_NEQ -> true
               | _ -> false)
  | CF_GE x0 ->
    (match y with
     | CF_GE x1 -> internal_signedness_beq x0 x1
     | _ -> false)
  | CF_GT x0 ->
    (match y with
     | CF_GT x1 -> internal_signedness_beq x0 x1
     | _ -> false)

(** val internal_pelem_beq : pelem -> pelem -> bool **)

let internal_pelem_beq x y =
  match x with
  | PE1 -> (match y with
            | PE1 -> true
            | _ -> false)
  | PE2 -> (match y with
            | PE2 -> true
            | _ -> false)
  | PE4 -> (match y with
            | PE4 -> true
            | _ -> false)
  | PE8 -> (match y with
            | PE8 -> true
            | _ -> false)
  | PE16 -> (match y with
             | PE16 -> true
             | _ -> false)
  | PE32 -> (match y with
             | PE32 -> true
             | _ -> false)
  | PE64 -> (match y with
             | PE64 -> true
             | _ -> false)
  | PE128 -> (match y with
              | PE128 -> true
              | _ -> false)

(** val opN_beq : opN -> opN -> bool **)

let opN_beq x y =
  match x with
  | Opack (x0, x1) ->
    (match y with
     | Opack (x2, x3) -> (&&) (wsize_beq x0 x2) (internal_pelem_beq x1 x3)
     | Ocombine_flags _ -> false)
  | Ocombine_flags x0 ->
    (match y with
     | Opack (_, _) -> false
     | Ocombine_flags x1 -> internal_combine_flags_beq x0 x1)

(** val opN_eq_dec : opN -> opN -> bool **)

let opN_eq_dec x y =
  let b = opN_beq x y in if b then true else false

(** val opN_eq_axiom : opN Equality.axiom **)

let opN_eq_axiom =
  eq_axiom_of_scheme opN_beq

(** val opN_eqMixin : opN Equality.mixin_of **)

let opN_eqMixin =
  { Equality.op = opN_beq; Equality.mixin_of__1 = opN_eq_axiom }

(** val opN_eqType : Equality.coq_type **)

let opN_eqType =
  Obj.magic opN_eqMixin

(** val type_of_op1 : sop1 -> stype * stype **)

let type_of_op1 = function
| Oword_of_int sz -> (Coq_sint, (Coq_sword sz))
| Oint_of_word sz -> ((Coq_sword sz), Coq_sint)
| Osignext (szo, szi) -> ((Coq_sword szi), (Coq_sword szo))
| Ozeroext (szo, szi) -> ((Coq_sword szi), (Coq_sword szo))
| Onot -> (Coq_sbool, Coq_sbool)
| Olnot sz -> let t0 = Coq_sword sz in (t0, t0)
| Oneg o0 ->
  (match o0 with
   | Op_int -> (Coq_sint, Coq_sint)
   | Op_w sz -> let t0 = Coq_sword sz in (t0, t0))

(** val type_of_op2 : sop2 -> (stype * stype) * stype **)

let type_of_op2 = function
| Oadd o0 ->
  (match o0 with
   | Op_int -> ((Coq_sint, Coq_sint), Coq_sint)
   | Op_w s -> let t0 = Coq_sword s in ((t0, t0), t0))
| Omul o0 ->
  (match o0 with
   | Op_int -> ((Coq_sint, Coq_sint), Coq_sint)
   | Op_w s -> let t0 = Coq_sword s in ((t0, t0), t0))
| Osub o0 ->
  (match o0 with
   | Op_int -> ((Coq_sint, Coq_sint), Coq_sint)
   | Op_w s -> let t0 = Coq_sword s in ((t0, t0), t0))
| Odiv c ->
  (match c with
   | Cmp_int -> ((Coq_sint, Coq_sint), Coq_sint)
   | Cmp_w (_, s) -> let t0 = Coq_sword s in ((t0, t0), t0))
| Omod c ->
  (match c with
   | Cmp_int -> ((Coq_sint, Coq_sint), Coq_sint)
   | Cmp_w (_, s) -> let t0 = Coq_sword s in ((t0, t0), t0))
| Oland s -> let t0 = Coq_sword s in ((t0, t0), t0)
| Olor s -> let t0 = Coq_sword s in ((t0, t0), t0)
| Olxor s -> let t0 = Coq_sword s in ((t0, t0), t0)
| Olsr s -> let t0 = Coq_sword s in ((t0, (Coq_sword U8)), t0)
| Olsl o0 ->
  (match o0 with
   | Op_int -> ((Coq_sint, Coq_sint), Coq_sint)
   | Op_w s -> let t0 = Coq_sword s in ((t0, (Coq_sword U8)), t0))
| Oasr o0 ->
  (match o0 with
   | Op_int -> ((Coq_sint, Coq_sint), Coq_sint)
   | Op_w s -> let t0 = Coq_sword s in ((t0, (Coq_sword U8)), t0))
| Oror s -> let t0 = Coq_sword s in ((t0, (Coq_sword U8)), t0)
| Orol s -> let t0 = Coq_sword s in ((t0, (Coq_sword U8)), t0)
| Oeq o0 ->
  (match o0 with
   | Op_int -> ((Coq_sint, Coq_sint), Coq_sbool)
   | Op_w s -> let t0 = Coq_sword s in ((t0, t0), Coq_sbool))
| Oneq o0 ->
  (match o0 with
   | Op_int -> ((Coq_sint, Coq_sint), Coq_sbool)
   | Op_w s -> let t0 = Coq_sword s in ((t0, t0), Coq_sbool))
| Olt c ->
  (match c with
   | Cmp_int -> ((Coq_sint, Coq_sint), Coq_sbool)
   | Cmp_w (_, s) -> let t0 = Coq_sword s in ((t0, t0), Coq_sbool))
| Ole c ->
  (match c with
   | Cmp_int -> ((Coq_sint, Coq_sint), Coq_sbool)
   | Cmp_w (_, s) -> let t0 = Coq_sword s in ((t0, t0), Coq_sbool))
| Ogt c ->
  (match c with
   | Cmp_int -> ((Coq_sint, Coq_sint), Coq_sbool)
   | Cmp_w (_, s) -> let t0 = Coq_sword s in ((t0, t0), Coq_sbool))
| Oge c ->
  (match c with
   | Cmp_int -> ((Coq_sint, Coq_sint), Coq_sbool)
   | Cmp_w (_, s) -> let t0 = Coq_sword s in ((t0, t0), Coq_sbool))
| Ovadd (_, s) -> let t0 = Coq_sword s in ((t0, t0), t0)
| Ovsub (_, s) -> let t0 = Coq_sword s in ((t0, t0), t0)
| Ovmul (_, s) -> let t0 = Coq_sword s in ((t0, t0), t0)
| Ovlsr (_, s) -> let t0 = Coq_sword s in ((t0, (Coq_sword U8)), t0)
| Ovlsl (_, s) -> let t0 = Coq_sword s in ((t0, (Coq_sword U8)), t0)
| Ovasr (_, s) -> let t0 = Coq_sword s in ((t0, (Coq_sword U8)), t0)
| _ -> ((Coq_sbool, Coq_sbool), Coq_sbool)

(** val tin_combine_flags : stype list **)

let tin_combine_flags =
  Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))

(** val type_of_opN : opN -> stype list * stype **)

let type_of_opN = function
| Opack (ws, p) ->
  let n = divn (nat_of_wsize ws) (nat_of_pelem p) in
  ((nseq n Coq_sint), (Coq_sword ws))
| Ocombine_flags _ -> (tin_combine_flags, Coq_sbool)

module type TAG =
 sig
  type t

  val witness : t
 end

module VarInfo =
 struct
  type t = Location.t

  (** val witness : t **)

  let witness = Location._dummy
 end

type var_info = Location.t

(** val dummy_var_info : var_info **)

let dummy_var_info =
  VarInfo.witness

type var_i = { v_var : Var.var; v_info : var_info }

(** val v_var : var_i -> Var.var **)

let v_var v =
  v.v_var

(** val v_info : var_i -> var_info **)

let v_info v =
  v.v_info

(** val mk_var_i : Var.var -> var_i **)

let mk_var_i x =
  { v_var = x; v_info = dummy_var_info }

type v_scope =
| Slocal
| Sglob

(** val v_scope_beq : v_scope -> v_scope -> bool **)

let v_scope_beq x y =
  match x with
  | Slocal -> (match y with
               | Slocal -> true
               | Sglob -> false)
  | Sglob -> (match y with
              | Slocal -> false
              | Sglob -> true)

(** val v_scope_eq_dec : v_scope -> v_scope -> bool **)

let v_scope_eq_dec x y =
  let b = v_scope_beq x y in if b then true else false

(** val v_scope_eq_axiom : v_scope Equality.axiom **)

let v_scope_eq_axiom =
  eq_axiom_of_scheme v_scope_beq

(** val v_scope_eqMixin : v_scope Equality.mixin_of **)

let v_scope_eqMixin =
  { Equality.op = v_scope_beq; Equality.mixin_of__1 = v_scope_eq_axiom }

(** val v_scope_eqType : Equality.coq_type **)

let v_scope_eqType =
  Obj.magic v_scope_eqMixin

type gvar = { gv : var_i; gs : v_scope }

(** val gv : gvar -> var_i **)

let gv g =
  g.gv

(** val gs : gvar -> v_scope **)

let gs g =
  g.gs

(** val mk_gvar : var_i -> gvar **)

let mk_gvar x =
  { gv = x; gs = Sglob }

(** val mk_lvar : var_i -> gvar **)

let mk_lvar x =
  { gv = x; gs = Slocal }

(** val is_lvar : gvar -> bool **)

let is_lvar x =
  eq_op v_scope_eqType (Obj.magic x.gs) (Obj.magic Slocal)

(** val is_glob : gvar -> bool **)

let is_glob x =
  eq_op v_scope_eqType (Obj.magic x.gs) (Obj.magic Sglob)

type pexpr =
| Pconst of coq_Z
| Pbool of bool
| Parr_init of positive
| Pvar of gvar
| Pget of arr_access * wsize * gvar * pexpr
| Psub of arr_access * wsize * positive * gvar * pexpr
| Pload of wsize * var_i * pexpr
| Papp1 of sop1 * pexpr
| Papp2 of sop2 * pexpr * pexpr
| PappN of opN * pexpr list
| Pif of stype * pexpr * pexpr * pexpr

(** val coq_Plvar : var_i -> pexpr **)

let coq_Plvar x =
  Pvar (mk_lvar x)

(** val enot : pexpr -> pexpr **)

let enot e =
  Papp1 (Onot, e)

(** val eor : pexpr -> pexpr -> pexpr **)

let eor e1 e2 =
  Papp2 (Oor, e1, e2)

(** val eand : pexpr -> pexpr -> pexpr **)

let eand e1 e2 =
  Papp2 (Oand, e1, e2)

(** val eeq : pexpr -> pexpr -> pexpr **)

let eeq e1 e2 =
  Papp2 (Obeq, e1, e2)

(** val eneq : pexpr -> pexpr -> pexpr **)

let eneq e1 e2 =
  enot (eeq e1 e2)

(** val cf_of_condition : sop2 -> (combine_flags * wsize) option **)

let cf_of_condition = function
| Oeq o -> (match o with
            | Op_int -> None
            | Op_w ws -> Some (CF_EQ, ws))
| Oneq o -> (match o with
             | Op_int -> None
             | Op_w ws -> Some (CF_NEQ, ws))
| Olt c ->
  (match c with
   | Cmp_int -> None
   | Cmp_w (s, ws) -> Some ((CF_LT s), ws))
| Ole c ->
  (match c with
   | Cmp_int -> None
   | Cmp_w (s, ws) -> Some ((CF_LE s), ws))
| Ogt c ->
  (match c with
   | Cmp_int -> None
   | Cmp_w (s, ws) -> Some ((CF_GT s), ws))
| Oge c ->
  (match c with
   | Cmp_int -> None
   | Cmp_w (s, ws) -> Some ((CF_GE s), ws))
| _ -> None

(** val pexpr_of_cf : combine_flags -> Var.var list -> pexpr **)

let pexpr_of_cf cf flags =
  let eflags = map (fun x -> coq_Plvar (mk_var_i x)) flags in
  PappN ((Ocombine_flags cf), eflags)

module Coq__1 = struct
 type lval =
 | Lnone of var_info * stype
 | Lvar of var_i
 | Lmem of wsize * var_i * pexpr
 | Laset of arr_access * wsize * var_i * pexpr
 | Lasub of arr_access * wsize * positive * var_i * pexpr
end
include Coq__1

(** val get_pvar : pexpr -> Var.var exec **)

let get_pvar = function
| Pvar g ->
  let { gv = x; gs = gs0 } = g in
  (match gs0 with
   | Slocal -> Ok x.v_var
   | Sglob -> type_error)
| _ -> type_error

(** val get_lvar : lval -> Var.var exec **)

let get_lvar = function
| Lvar x0 -> Ok x0.v_var
| _ -> type_error

(** val coq_Lnone_b : var_info -> lval **)

let coq_Lnone_b vi =
  Lnone (vi, Coq_sbool)

type dir =
| UpTo
| DownTo

(** val dir_beq : dir -> dir -> bool **)

let dir_beq x y =
  match x with
  | UpTo -> (match y with
             | UpTo -> true
             | DownTo -> false)
  | DownTo -> (match y with
               | UpTo -> false
               | DownTo -> true)

(** val dir_eq_dec : dir -> dir -> bool **)

let dir_eq_dec x y =
  let b = dir_beq x y in if b then true else false

(** val dir_eq_axiom : dir Equality.axiom **)

let dir_eq_axiom =
  eq_axiom_of_scheme dir_beq

(** val dir_eqMixin : dir Equality.mixin_of **)

let dir_eqMixin =
  { Equality.op = dir_beq; Equality.mixin_of__1 = dir_eq_axiom }

(** val dir_eqType : Equality.coq_type **)

let dir_eqType =
  Obj.magic dir_eqMixin

type range = (dir * pexpr) * pexpr

(** val wrange : dir -> coq_Z -> coq_Z -> coq_Z list **)

let wrange d n1 n2 =
  let n = Z.to_nat (Z.sub n2 n1) in
  (match d with
   | UpTo -> map (fun i -> Z.add n1 (Z.of_nat i)) (iota O n)
   | DownTo -> map (fun i -> Z.sub n2 (Z.of_nat i)) (iota O n))

module type InstrInfoT =
 sig
  type t

  val witness : t

  val with_location : t -> t

  val is_inline : t -> bool

  val update_after_call : t -> bool
 end

module InstrInfo =
 struct
  type t = IInfo.t

  (** val witness : t **)

  let witness = IInfo.dummy

  (** val with_location : t -> t **)

  let with_location = IInfo.with_location

  (** val is_inline : t -> bool **)

  let is_inline = IInfo.is_inline

  (** val update_after_call : t -> bool **)

  let update_after_call = IInfo.update_after_call
 end

type instr_info = IInfo.t

(** val dummy_instr_info : instr_info **)

let dummy_instr_info =
  InstrInfo.witness

(** val ii_with_location : instr_info -> instr_info **)

let ii_with_location =
  InstrInfo.with_location

(** val ii_is_inline : instr_info -> bool **)

let ii_is_inline =
  InstrInfo.is_inline

(** val ii_update_after_call : instr_info -> bool **)

let ii_update_after_call =
  InstrInfo.update_after_call

type assgn_tag =
| AT_none
| AT_keep
| AT_rename
| AT_inline
| AT_phinode

(** val assgn_tag_beq : assgn_tag -> assgn_tag -> bool **)

let assgn_tag_beq x y =
  match x with
  | AT_none -> (match y with
                | AT_none -> true
                | _ -> false)
  | AT_keep -> (match y with
                | AT_keep -> true
                | _ -> false)
  | AT_rename -> (match y with
                  | AT_rename -> true
                  | _ -> false)
  | AT_inline -> (match y with
                  | AT_inline -> true
                  | _ -> false)
  | AT_phinode -> (match y with
                   | AT_phinode -> true
                   | _ -> false)

(** val assgn_tag_eq_dec : assgn_tag -> assgn_tag -> bool **)

let assgn_tag_eq_dec x y =
  let b = assgn_tag_beq x y in if b then true else false

(** val assgn_tag_eq_axiom : assgn_tag Equality.axiom **)

let assgn_tag_eq_axiom =
  eq_axiom_of_scheme assgn_tag_beq

(** val assgn_tag_eqMixin : assgn_tag Equality.mixin_of **)

let assgn_tag_eqMixin =
  { Equality.op = assgn_tag_beq; Equality.mixin_of__1 = assgn_tag_eq_axiom }

(** val assgn_tag_eqType : Equality.coq_type **)

let assgn_tag_eqType =
  Obj.magic assgn_tag_eqMixin

type align =
| Align
| NoAlign

type 'asm_op instr_r =
| Cassgn of lval * assgn_tag * stype * pexpr
| Copn of lval list * assgn_tag * 'asm_op sopn * pexpr list
| Csyscall of lval list * BinNums.positive Syscall_t.syscall_t * pexpr list
| Cif of pexpr * 'asm_op instr list * 'asm_op instr list
| Cfor of var_i * range * 'asm_op instr list
| Cwhile of align * 'asm_op instr list * pexpr * 'asm_op instr list
| Ccall of lval list * funname * pexpr list
and 'asm_op instr =
| MkI of instr_info * 'asm_op instr_r

(** val cmd_rect_aux :
    'a1 asmOp -> 'a3 -> ('a1 instr -> 'a1 instr list -> 'a2 -> 'a3 -> 'a3) ->
    ('a1 instr -> 'a2) -> 'a1 instr list -> 'a3 **)

let rec cmd_rect_aux asmop hnil hcons instr_rect = function
| [] -> hnil
| i :: c0 ->
  hcons i c0 (instr_rect i) (cmd_rect_aux asmop hnil hcons instr_rect c0)

(** val instr_Rect :
    'a1 asmOp -> ('a1 instr_r -> instr_info -> 'a2 -> 'a3) -> 'a4 -> ('a1
    instr -> 'a1 instr list -> 'a3 -> 'a4 -> 'a4) -> (lval -> assgn_tag ->
    stype -> pexpr -> 'a2) -> (lval list -> assgn_tag -> 'a1 sopn -> pexpr
    list -> 'a2) -> (lval list -> BinNums.positive Syscall_t.syscall_t ->
    pexpr list -> 'a2) -> (pexpr -> 'a1 instr list -> 'a1 instr list -> 'a4
    -> 'a4 -> 'a2) -> (var_i -> dir -> pexpr -> pexpr -> 'a1 instr list ->
    'a4 -> 'a2) -> (align -> 'a1 instr list -> pexpr -> 'a1 instr list -> 'a4
    -> 'a4 -> 'a2) -> (lval list -> funname -> pexpr list -> 'a2) -> 'a1
    instr -> 'a3 **)

let instr_Rect asmop hmk hnil hcons hasgn hopn hsyscall hif hfor hwhile hcall =
  let rec instr_Rect0 = function
  | MkI (ii, i0) -> hmk i0 ii (instr_r_Rect0 i0)
  and instr_r_Rect0 = function
  | Cassgn (x, tg, ty, e) -> hasgn x tg ty e
  | Copn (xs, t0, o, es) -> hopn xs t0 o es
  | Csyscall (xs, o, es) -> hsyscall xs o es
  | Cif (e, c1, c2) ->
    hif e c1 c2 (cmd_rect_aux asmop hnil hcons instr_Rect0 c1)
      (cmd_rect_aux asmop hnil hcons instr_Rect0 c2)
  | Cfor (i0, r, c) ->
    let (p, hi) = r in
    let (dir0, lo) = p in
    hfor i0 dir0 lo hi c (cmd_rect_aux asmop hnil hcons instr_Rect0 c)
  | Cwhile (a, c, e, c') ->
    hwhile a c e c' (cmd_rect_aux asmop hnil hcons instr_Rect0 c)
      (cmd_rect_aux asmop hnil hcons instr_Rect0 c')
  | Ccall (xs, f, es) -> hcall xs f es
  in instr_Rect0

(** val instr_r_Rect :
    'a1 asmOp -> ('a1 instr_r -> instr_info -> 'a2 -> 'a3) -> 'a4 -> ('a1
    instr -> 'a1 instr list -> 'a3 -> 'a4 -> 'a4) -> (lval -> assgn_tag ->
    stype -> pexpr -> 'a2) -> (lval list -> assgn_tag -> 'a1 sopn -> pexpr
    list -> 'a2) -> (lval list -> BinNums.positive Syscall_t.syscall_t ->
    pexpr list -> 'a2) -> (pexpr -> 'a1 instr list -> 'a1 instr list -> 'a4
    -> 'a4 -> 'a2) -> (var_i -> dir -> pexpr -> pexpr -> 'a1 instr list ->
    'a4 -> 'a2) -> (align -> 'a1 instr list -> pexpr -> 'a1 instr list -> 'a4
    -> 'a4 -> 'a2) -> (lval list -> funname -> pexpr list -> 'a2) -> 'a1
    instr_r -> 'a2 **)

let instr_r_Rect asmop hmk hnil hcons hasgn hopn hsyscall hif hfor hwhile hcall =
  let rec instr_Rect0 = function
  | MkI (ii, i0) -> hmk i0 ii (instr_r_Rect0 i0)
  and instr_r_Rect0 = function
  | Cassgn (x, tg, ty, e) -> hasgn x tg ty e
  | Copn (xs, t0, o, es) -> hopn xs t0 o es
  | Csyscall (xs, o, es) -> hsyscall xs o es
  | Cif (e, c1, c2) ->
    hif e c1 c2 (cmd_rect_aux asmop hnil hcons instr_Rect0 c1)
      (cmd_rect_aux asmop hnil hcons instr_Rect0 c2)
  | Cfor (i0, r, c) ->
    let (p, hi) = r in
    let (dir0, lo) = p in
    hfor i0 dir0 lo hi c (cmd_rect_aux asmop hnil hcons instr_Rect0 c)
  | Cwhile (a, c, e, c') ->
    hwhile a c e c' (cmd_rect_aux asmop hnil hcons instr_Rect0 c)
      (cmd_rect_aux asmop hnil hcons instr_Rect0 c')
  | Ccall (xs, f, es) -> hcall xs f es
  in instr_r_Rect0

(** val cmd_rect :
    'a1 asmOp -> ('a1 instr_r -> instr_info -> 'a2 -> 'a3) -> 'a4 -> ('a1
    instr -> 'a1 instr list -> 'a3 -> 'a4 -> 'a4) -> (lval -> assgn_tag ->
    stype -> pexpr -> 'a2) -> (lval list -> assgn_tag -> 'a1 sopn -> pexpr
    list -> 'a2) -> (lval list -> BinNums.positive Syscall_t.syscall_t ->
    pexpr list -> 'a2) -> (pexpr -> 'a1 instr list -> 'a1 instr list -> 'a4
    -> 'a4 -> 'a2) -> (var_i -> dir -> pexpr -> pexpr -> 'a1 instr list ->
    'a4 -> 'a2) -> (align -> 'a1 instr list -> pexpr -> 'a1 instr list -> 'a4
    -> 'a4 -> 'a2) -> (lval list -> funname -> pexpr list -> 'a2) -> 'a1
    instr list -> 'a4 **)

let cmd_rect asmop hmk hnil hcons hasgn hopn hsyscall hif hfor hwhile hcall =
  cmd_rect_aux asmop hnil hcons
    (instr_Rect asmop hmk hnil hcons hasgn hopn hsyscall hif hfor hwhile
      hcall)

module FunInfo =
 struct
  type t = positive

  (** val witness : t **)

  let witness =
    Coq_xH
 end

type fun_info = FInfo.t

type progT =
| Build_progT

type extra_fun_t = __

type extra_prog_t = __

type extra_val_t = __

type ('asm_op, 'extra_fun_t) _fundef = { f_info : fun_info;
                                         f_tyin : stype list;
                                         f_params : var_i list;
                                         f_body : 'asm_op instr list;
                                         f_tyout : stype list;
                                         f_res : var_i list;
                                         f_extra : 'extra_fun_t }

(** val f_info : 'a1 asmOp -> ('a1, 'a2) _fundef -> fun_info **)

let f_info _ x =
  x.f_info

(** val f_tyin : 'a1 asmOp -> ('a1, 'a2) _fundef -> stype list **)

let f_tyin _ x =
  x.f_tyin

(** val f_params : 'a1 asmOp -> ('a1, 'a2) _fundef -> var_i list **)

let f_params _ x =
  x.f_params

(** val f_body : 'a1 asmOp -> ('a1, 'a2) _fundef -> 'a1 instr list **)

let f_body _ x =
  x.f_body

(** val f_tyout : 'a1 asmOp -> ('a1, 'a2) _fundef -> stype list **)

let f_tyout _ x =
  x.f_tyout

(** val f_res : 'a1 asmOp -> ('a1, 'a2) _fundef -> var_i list **)

let f_res _ x =
  x.f_res

(** val f_extra : 'a1 asmOp -> ('a1, 'a2) _fundef -> 'a2 **)

let f_extra _ x =
  x.f_extra

type ('asm_op, 'extra_fun_t) _fun_decl =
  funname * ('asm_op, 'extra_fun_t) _fundef

type ('asm_op, 'extra_fun_t, 'extra_prog_t) _prog = { p_funcs : ('asm_op,
                                                                'extra_fun_t)
                                                                _fun_decl list;
                                                      p_globs : glob_decl list;
                                                      p_extra : 'extra_prog_t }

(** val p_funcs :
    'a1 asmOp -> ('a1, 'a2, 'a3) _prog -> ('a1, 'a2) _fun_decl list **)

let p_funcs _ x =
  x.p_funcs

(** val p_globs : 'a1 asmOp -> ('a1, 'a2, 'a3) _prog -> glob_decl list **)

let p_globs _ x =
  x.p_globs

(** val p_extra : 'a1 asmOp -> ('a1, 'a2, 'a3) _prog -> 'a3 **)

let p_extra _ x =
  x.p_extra

type 'asm_op fundef = ('asm_op, extra_fun_t) _fundef

type function_signature = stype list * stype list

(** val signature_of_fundef :
    'a1 asmOp -> progT -> 'a1 fundef -> function_signature **)

let signature_of_fundef _ _ fd =
  (fd.f_tyin, fd.f_tyout)

type 'asm_op fun_decl = funname * 'asm_op fundef

type 'asm_op prog = ('asm_op, extra_fun_t, extra_prog_t) _prog

(** val coq_Build_prog :
    'a1 asmOp -> progT -> ('a1, extra_fun_t) _fun_decl list -> glob_decl list
    -> extra_prog_t -> 'a1 prog **)

let coq_Build_prog _ _ p_funcs0 p_globs0 p_extra0 =
  { p_funcs = p_funcs0; p_globs = p_globs0; p_extra = p_extra0 }

(** val progUnit : progT **)

let progUnit =
  Build_progT

type 'asm_op ufundef = 'asm_op fundef

type 'asm_op ufun_decl = 'asm_op fun_decl

type 'asm_op ufun_decls = 'asm_op fun_decl list

type 'asm_op uprog = 'asm_op prog

type 'asm_op _ufundef = ('asm_op, unit) _fundef

type 'asm_op _ufun_decl = ('asm_op, unit) _fun_decl

type 'asm_op _ufun_decls = ('asm_op, unit) _fun_decl list

type 'asm_op _uprog = ('asm_op, unit, unit) _prog

(** val to_uprog : 'a1 asmOp -> 'a1 _uprog -> 'a1 uprog **)

let to_uprog _ p =
  Obj.magic p

type saved_stack =
| SavedStackNone
| SavedStackReg of Var.var
| SavedStackStk of coq_Z

(** val saved_stack_beq : saved_stack -> saved_stack -> bool **)

let saved_stack_beq x y =
  match x with
  | SavedStackNone -> (match y with
                       | SavedStackNone -> true
                       | _ -> false)
  | SavedStackReg v1 ->
    (match y with
     | SavedStackReg v2 -> eq_op Var.var_eqType (Obj.magic v1) (Obj.magic v2)
     | _ -> false)
  | SavedStackStk z1 ->
    (match y with
     | SavedStackStk z2 -> eq_op coq_Z_eqType (Obj.magic z1) (Obj.magic z2)
     | _ -> false)

(** val saved_stack_eq_axiom : saved_stack Equality.axiom **)

let saved_stack_eq_axiom __top_assumption_ =
  let _evar_0_ = fun __top_assumption_0 ->
    let _evar_0_ = ReflectT in
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = fun _ -> ReflectF in
    (match __top_assumption_0 with
     | SavedStackNone -> _evar_0_
     | SavedStackReg v -> _evar_0_0 v
     | SavedStackStk z -> _evar_0_1 z)
  in
  let _evar_0_0 = fun v1 __top_assumption_0 ->
    let _evar_0_0 = ReflectF in
    let _evar_0_1 = fun v2 ->
      iffP (eq_op Var.var_eqType v1 v2) (eqP Var.var_eqType v1 v2)
    in
    let _evar_0_2 = fun _ -> ReflectF in
    (match __top_assumption_0 with
     | SavedStackNone -> _evar_0_0
     | SavedStackReg v -> Obj.magic _evar_0_1 v
     | SavedStackStk z -> _evar_0_2 z)
  in
  let _evar_0_1 = fun z1 __top_assumption_0 ->
    let _evar_0_1 = ReflectF in
    let _evar_0_2 = fun _ -> ReflectF in
    let _evar_0_3 = fun z2 ->
      iffP (eq_op coq_Z_eqType z1 z2) (eqP coq_Z_eqType z1 z2)
    in
    (match __top_assumption_0 with
     | SavedStackNone -> _evar_0_1
     | SavedStackReg v -> _evar_0_2 v
     | SavedStackStk z -> Obj.magic _evar_0_3 z)
  in
  (match __top_assumption_ with
   | SavedStackNone -> _evar_0_
   | SavedStackReg v -> Obj.magic _evar_0_0 v
   | SavedStackStk z -> Obj.magic _evar_0_1 z)

(** val saved_stack_eqMixin : saved_stack Equality.mixin_of **)

let saved_stack_eqMixin =
  { Equality.op = saved_stack_beq; Equality.mixin_of__1 =
    saved_stack_eq_axiom }

(** val saved_stack_eqType : Equality.coq_type **)

let saved_stack_eqType =
  Obj.magic saved_stack_eqMixin

type return_address_location =
| RAnone
| RAreg of Var.var * Var.var option
| RAstack of Var.var option * coq_Z * Var.var option

(** val is_RAnone : return_address_location -> bool **)

let is_RAnone = function
| RAnone -> true
| _ -> false

(** val is_RAstack : return_address_location -> bool **)

let is_RAstack = function
| RAstack (_, _, _) -> true
| _ -> false

(** val is_RAstack_None : return_address_location -> bool **)

let is_RAstack_None = function
| RAstack (o, _, _) -> (match o with
                        | Some _ -> false
                        | None -> true)
| _ -> false

(** val return_address_location_beq :
    return_address_location -> return_address_location -> bool **)

let return_address_location_beq r1 r2 =
  match r1 with
  | RAnone -> (match r2 with
               | RAnone -> true
               | _ -> false)
  | RAreg (x1, o1) ->
    (match r2 with
     | RAreg (x2, o2) ->
       (&&) (eq_op Var.var_eqType (Obj.magic x1) (Obj.magic x2))
         (eq_op (option_eqType Var.var_eqType) (Obj.magic o1) (Obj.magic o2))
     | _ -> false)
  | RAstack (lr1, z1, o1) ->
    (match r2 with
     | RAstack (lr2, z2, o2) ->
       (&&)
         (eq_op (option_eqType Var.var_eqType) (Obj.magic lr1)
           (Obj.magic lr2))
         ((&&) (eq_op coq_Z_eqType (Obj.magic z1) (Obj.magic z2))
           (eq_op (option_eqType Var.var_eqType) (Obj.magic o1)
             (Obj.magic o2)))
     | _ -> false)

(** val return_address_location_eq_axiom :
    return_address_location Equality.axiom **)

let return_address_location_eq_axiom _top_assumption_ =
  let _evar_0_ = fun __top_assumption_ ->
    let _evar_0_ = ReflectT in
    let _evar_0_0 = fun _ _ -> ReflectF in
    let _evar_0_1 = fun _ _ _ -> ReflectF in
    (match __top_assumption_ with
     | RAnone -> _evar_0_
     | RAreg (v, o) -> _evar_0_0 v o
     | RAstack (o, z, o0) -> _evar_0_1 o z o0)
  in
  let _evar_0_0 = fun x1 o1 __top_assumption_ ->
    let _evar_0_0 = ReflectF in
    let _evar_0_1 = fun x2 o2 ->
      iffP
        ((&&) (eq_op Var.var_eqType x1 x2)
          (eq_op (option_eqType Var.var_eqType) o1 o2))
        (andP (eq_op Var.var_eqType x1 x2)
          (eq_op (option_eqType Var.var_eqType) o1 o2))
    in
    let _evar_0_2 = fun _ _ _ -> ReflectF in
    (match __top_assumption_ with
     | RAnone -> _evar_0_0
     | RAreg (v, o) -> Obj.magic _evar_0_1 v o
     | RAstack (o, z, o0) -> _evar_0_2 o z o0)
  in
  let _evar_0_1 = fun lr1 z1 o1 __top_assumption_ ->
    let _evar_0_1 = ReflectF in
    let _evar_0_2 = fun _ _ -> ReflectF in
    let _evar_0_3 = fun lr2 z2 o2 ->
      iffP
        ((&&) (eq_op (option_eqType Var.var_eqType) lr1 lr2)
          ((&&) (eq_op coq_Z_eqType z1 z2)
            (eq_op (option_eqType Var.var_eqType) o1 o2)))
        (and3P (eq_op (option_eqType Var.var_eqType) lr1 lr2)
          (eq_op coq_Z_eqType z1 z2)
          (eq_op (option_eqType Var.var_eqType) o1 o2))
    in
    (match __top_assumption_ with
     | RAnone -> _evar_0_1
     | RAreg (v, o) -> _evar_0_2 v o
     | RAstack (o, z, o0) -> Obj.magic _evar_0_3 o z o0)
  in
  (match _top_assumption_ with
   | RAnone -> _evar_0_
   | RAreg (v, o) -> Obj.magic _evar_0_0 v o
   | RAstack (o, z, o0) -> Obj.magic _evar_0_1 o z o0)

(** val return_address_location_eqMixin :
    return_address_location Equality.mixin_of **)

let return_address_location_eqMixin =
  { Equality.op = return_address_location_beq; Equality.mixin_of__1 =
    return_address_location_eq_axiom }

(** val return_address_location_eqType : Equality.coq_type **)

let return_address_location_eqType =
  Obj.magic return_address_location_eqMixin

type stk_fun_extra = { sf_align : wsize; sf_stk_sz : coq_Z;
                       sf_stk_ioff : coq_Z; sf_stk_extra_sz : coq_Z;
                       sf_stk_max : coq_Z; sf_max_call_depth : coq_Z;
                       sf_to_save : (Var.var * coq_Z) list;
                       sf_save_stack : saved_stack;
                       sf_return_address : return_address_location }

(** val sf_align : stk_fun_extra -> wsize **)

let sf_align s =
  s.sf_align

(** val sf_stk_sz : stk_fun_extra -> coq_Z **)

let sf_stk_sz s =
  s.sf_stk_sz

(** val sf_stk_ioff : stk_fun_extra -> coq_Z **)

let sf_stk_ioff s =
  s.sf_stk_ioff

(** val sf_stk_extra_sz : stk_fun_extra -> coq_Z **)

let sf_stk_extra_sz s =
  s.sf_stk_extra_sz

(** val sf_stk_max : stk_fun_extra -> coq_Z **)

let sf_stk_max s =
  s.sf_stk_max

(** val sf_max_call_depth : stk_fun_extra -> coq_Z **)

let sf_max_call_depth s =
  s.sf_max_call_depth

(** val sf_to_save : stk_fun_extra -> (Var.var * coq_Z) list **)

let sf_to_save s =
  s.sf_to_save

(** val sf_save_stack : stk_fun_extra -> saved_stack **)

let sf_save_stack s =
  s.sf_save_stack

(** val sf_return_address : stk_fun_extra -> return_address_location **)

let sf_return_address s =
  s.sf_return_address

type sprog_extra = { sp_rsp : Ident.Ident.ident; sp_rip : Ident.Ident.ident;
                     sp_globs : GRing.ComRing.sort list }

(** val sp_rsp : sprog_extra -> Ident.Ident.ident **)

let sp_rsp s =
  s.sp_rsp

(** val sp_rip : sprog_extra -> Ident.Ident.ident **)

let sp_rip s =
  s.sp_rip

(** val sp_globs : sprog_extra -> GRing.ComRing.sort list **)

let sp_globs s =
  s.sp_globs

(** val progStack : coq_PointerData -> progT **)

let progStack _ =
  Build_progT

type 'asm_op sfundef = 'asm_op fundef

type 'asm_op sfun_decl = 'asm_op fun_decl

type 'asm_op sfun_decls = 'asm_op fun_decl list

type 'asm_op sprog = 'asm_op prog

type 'asm_op _sfundef = ('asm_op, stk_fun_extra) _fundef

type 'asm_op _sfun_decl = ('asm_op, stk_fun_extra) _fun_decl

type 'asm_op _sfun_decls = ('asm_op, stk_fun_extra) _fun_decl list

type 'asm_op _sprog = ('asm_op, stk_fun_extra, sprog_extra) _prog

(** val to_sprog : coq_PointerData -> 'a1 asmOp -> 'a1 _sprog -> 'a1 sprog **)

let to_sprog _ _ p =
  Obj.magic p

(** val with_body :
    'a1 asmOp -> ('a1, 'a2) _fundef -> 'a1 instr list -> ('a1, 'a2) _fundef **)

let with_body _ fd body =
  { f_info = fd.f_info; f_tyin = fd.f_tyin; f_params = fd.f_params; f_body =
    body; f_tyout = fd.f_tyout; f_res = fd.f_res; f_extra = fd.f_extra }

(** val swith_extra :
    coq_PointerData -> 'a1 asmOp -> coq_PointerData -> 'a1 ufundef ->
    extra_fun_t -> 'a1 sfundef **)

let swith_extra _ _ _ fd f_extra0 =
  { f_info = fd.f_info; f_tyin = fd.f_tyin; f_params = fd.f_params; f_body =
    fd.f_body; f_tyout = fd.f_tyout; f_res = fd.f_res; f_extra = f_extra0 }

(** val is_const : pexpr -> coq_Z option **)

let is_const = function
| Pconst n -> Some n
| _ -> None

(** val is_bool : pexpr -> bool option **)

let is_bool = function
| Pbool b -> Some b
| _ -> None

(** val is_Papp2 : pexpr -> ((sop2 * pexpr) * pexpr) option **)

let is_Papp2 = function
| Papp2 (op0, e0, e1) -> Some ((op0, e0), e1)
| _ -> None

(** val is_array_init : pexpr -> bool **)

let is_array_init = function
| Parr_init _ -> true
| _ -> false

(** val cast_w : wsize -> pexpr -> pexpr **)

let rec cast_w ws e = match e with
| Papp1 (s, e') ->
  (match s with
   | Oint_of_word ws' ->
     if cmp_le wsize_cmp ws ws' then e' else Papp1 ((Oword_of_int ws), e)
   | Oneg o ->
     (match o with
      | Op_int -> Papp1 ((Oneg (Op_w ws)), (cast_w ws e'))
      | Op_w _ -> Papp1 ((Oword_of_int ws), e))
   | _ -> Papp1 ((Oword_of_int ws), e))
| Papp2 (s, e1, e2) ->
  (match s with
   | Oadd o ->
     (match o with
      | Op_int -> Papp2 ((Oadd (Op_w ws)), (cast_w ws e1), (cast_w ws e2))
      | Op_w _ -> Papp1 ((Oword_of_int ws), e))
   | Omul o ->
     (match o with
      | Op_int -> Papp2 ((Omul (Op_w ws)), (cast_w ws e1), (cast_w ws e2))
      | Op_w _ -> Papp1 ((Oword_of_int ws), e))
   | Osub o ->
     (match o with
      | Op_int -> Papp2 ((Osub (Op_w ws)), (cast_w ws e1), (cast_w ws e2))
      | Op_w _ -> Papp1 ((Oword_of_int ws), e))
   | _ -> Papp1 ((Oword_of_int ws), e))
| _ -> Papp1 ((Oword_of_int ws), e)

(** val cast_ptr : coq_PointerData -> pexpr -> pexpr **)

let cast_ptr pd =
  cast_w (coq_Uptr pd)

(** val cast_const : coq_PointerData -> coq_Z -> pexpr **)

let cast_const pd z =
  cast_ptr pd (Pconst z)

(** val eword_of_int : wsize -> coq_Z -> pexpr **)

let eword_of_int ws x =
  Papp1 ((Oword_of_int ws), (Pconst x))

(** val wconst : wsize -> GRing.ComRing.sort -> pexpr **)

let wconst sz n =
  Papp1 ((Oword_of_int sz), (Pconst (wunsigned sz n)))

(** val is_wconst : wsize -> pexpr -> GRing.ComRing.sort option **)

let is_wconst sz = function
| Papp1 (s, e0) ->
  (match s with
   | Oword_of_int sz' ->
     if cmp_le wsize_cmp sz sz'
     then Ssrfun.Option.bind (fun n -> Some (wrepr sz n)) (is_const e0)
     else None
   | _ -> None)
| _ -> None

(** val is_wconst_of_size : Equality.sort -> pexpr -> coq_Z option **)

let is_wconst_of_size sz = function
| Papp1 (s, p) ->
  (match s with
   | Oword_of_int sz' ->
     (match p with
      | Pconst z ->
        if eq_op wsize_eqType (Obj.magic sz') sz then Some z else None
      | _ -> None)
   | _ -> None)
| _ -> None

(** val vrv_rec : SvExtra.Sv.t -> lval -> SvExtra.Sv.t **)

let vrv_rec s = function
| Lvar x -> SvExtra.Sv.add (Obj.magic x.v_var) s
| Laset (_, _, x, _) -> SvExtra.Sv.add (Obj.magic x.v_var) s
| Lasub (_, _, _, x, _) -> SvExtra.Sv.add (Obj.magic x.v_var) s
| _ -> s

(** val vrvs_rec : SvExtra.Sv.t -> lval list -> SvExtra.Sv.t **)

let vrvs_rec s rv =
  foldl vrv_rec s rv

(** val vrv : lval -> SvExtra.Sv.t **)

let vrv =
  vrv_rec SvExtra.Sv.empty

(** val vrvs : lval list -> SvExtra.Sv.t **)

let vrvs =
  vrvs_rec SvExtra.Sv.empty

(** val lv_write_mem : lval -> bool **)

let lv_write_mem = function
| Lmem (_, _, _) -> true
| _ -> false

(** val write_i_rec :
    'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr_r -> SvExtra.Sv.t **)

let write_i_rec _ =
  let rec write_i_rec0 s = function
  | Cassgn (x, _, _, _) -> vrv_rec s x
  | Copn (xs, _, _, _) -> vrvs_rec s xs
  | Csyscall (xs, _, _) -> vrvs_rec s xs
  | Cif (_, c1, c2) -> foldl write_I_rec0 (foldl write_I_rec0 s c2) c1
  | Cfor (x, _, c) ->
    foldl write_I_rec0 (SvExtra.Sv.add (Obj.magic x.v_var) s) c
  | Cwhile (_, c, _, c') -> foldl write_I_rec0 (foldl write_I_rec0 s c') c
  | Ccall (x, _, _) -> vrvs_rec s x
  and write_I_rec0 s = function
  | MkI (_, i0) -> write_i_rec0 s i0
  in write_i_rec0

(** val write_I_rec :
    'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr -> SvExtra.Sv.t **)

let write_I_rec _ =
  let rec write_i_rec0 s = function
  | Cassgn (x, _, _, _) -> vrv_rec s x
  | Copn (xs, _, _, _) -> vrvs_rec s xs
  | Csyscall (xs, _, _) -> vrvs_rec s xs
  | Cif (_, c1, c2) -> foldl write_I_rec0 (foldl write_I_rec0 s c2) c1
  | Cfor (x, _, c) ->
    foldl write_I_rec0 (SvExtra.Sv.add (Obj.magic x.v_var) s) c
  | Cwhile (_, c, _, c') -> foldl write_I_rec0 (foldl write_I_rec0 s c') c
  | Ccall (x, _, _) -> vrvs_rec s x
  and write_I_rec0 s = function
  | MkI (_, i0) -> write_i_rec0 s i0
  in write_I_rec0

(** val write_i : 'a1 asmOp -> 'a1 instr_r -> SvExtra.Sv.t **)

let write_i asmop i =
  write_i_rec asmop SvExtra.Sv.empty i

(** val write_I : 'a1 asmOp -> 'a1 instr -> SvExtra.Sv.t **)

let write_I asmop i =
  write_I_rec asmop SvExtra.Sv.empty i

(** val write_c_rec :
    'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr list -> SvExtra.Sv.t **)

let write_c_rec asmop s c =
  foldl (write_I_rec asmop) s c

(** val write_c : 'a1 asmOp -> 'a1 instr list -> SvExtra.Sv.t **)

let write_c asmop c =
  write_c_rec asmop SvExtra.Sv.empty c

(** val use_mem : pexpr -> bool **)

let rec use_mem = function
| Pget (_, _, _, e0) -> use_mem e0
| Psub (_, _, _, _, e0) -> use_mem e0
| Pload (_, _, _) -> true
| Papp1 (_, e0) -> use_mem e0
| Papp2 (_, e1, e2) -> (||) (use_mem e1) (use_mem e2)
| PappN (_, es) -> has use_mem es
| Pif (_, e0, e1, e2) -> (||) ((||) (use_mem e0) (use_mem e1)) (use_mem e2)
| _ -> false

(** val read_gvar : gvar -> SvExtra.Sv.t **)

let read_gvar x =
  if is_lvar x
  then SvExtra.Sv.singleton (Obj.magic x.gv.v_var)
  else SvExtra.Sv.empty

(** val read_e_rec : SvExtra.Sv.t -> pexpr -> SvExtra.Sv.t **)

let rec read_e_rec s = function
| Pvar x -> SvExtra.Sv.union (read_gvar x) s
| Pget (_, _, x, e0) -> read_e_rec (SvExtra.Sv.union (read_gvar x) s) e0
| Psub (_, _, _, x, e0) -> read_e_rec (SvExtra.Sv.union (read_gvar x) s) e0
| Pload (_, x, e0) -> read_e_rec (SvExtra.Sv.add (Obj.magic x.v_var) s) e0
| Papp1 (_, e0) -> read_e_rec s e0
| Papp2 (_, e1, e2) -> read_e_rec (read_e_rec s e2) e1
| PappN (_, es) -> foldl read_e_rec s es
| Pif (_, t0, e1, e2) -> read_e_rec (read_e_rec (read_e_rec s e2) e1) t0
| _ -> s

(** val read_e : pexpr -> SvExtra.Sv.t **)

let read_e =
  read_e_rec SvExtra.Sv.empty

(** val read_es_rec : SvExtra.Sv.t -> pexpr list -> SvExtra.Sv.t **)

let read_es_rec =
  foldl read_e_rec

(** val read_es : pexpr list -> SvExtra.Sv.t **)

let read_es =
  read_es_rec SvExtra.Sv.empty

(** val read_rv_rec : SvExtra.Sv.t -> lval -> SvExtra.Sv.t **)

let read_rv_rec s = function
| Lmem (_, x, e) -> read_e_rec (SvExtra.Sv.add (Obj.magic x.v_var) s) e
| Laset (_, _, x, e) -> read_e_rec (SvExtra.Sv.add (Obj.magic x.v_var) s) e
| Lasub (_, _, _, x, e) -> read_e_rec (SvExtra.Sv.add (Obj.magic x.v_var) s) e
| _ -> s

(** val read_rv : lval -> SvExtra.Sv.t **)

let read_rv =
  read_rv_rec SvExtra.Sv.empty

(** val read_rvs_rec : SvExtra.Sv.t -> lval list -> SvExtra.Sv.t **)

let read_rvs_rec =
  foldl read_rv_rec

(** val read_rvs : lval list -> SvExtra.Sv.t **)

let read_rvs =
  read_rvs_rec SvExtra.Sv.empty

(** val read_i_rec :
    'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr_r -> SvExtra.Sv.t **)

let read_i_rec _ =
  let rec read_i_rec0 s = function
  | Cassgn (x, _, _, e) -> read_rv_rec (read_e_rec s e) x
  | Copn (xs, _, _, es) -> read_es_rec (read_rvs_rec s xs) es
  | Csyscall (xs, _, es) -> read_es_rec (read_rvs_rec s xs) es
  | Cif (b, c1, c2) ->
    let s0 = foldl read_I_rec0 s c1 in
    let s1 = foldl read_I_rec0 s0 c2 in read_e_rec s1 b
  | Cfor (_, r, c) ->
    let (p, e2) = r in
    let (_, e1) = p in
    let s0 = foldl read_I_rec0 s c in read_e_rec (read_e_rec s0 e2) e1
  | Cwhile (_, c, e, c') ->
    let s0 = foldl read_I_rec0 s c in
    let s1 = foldl read_I_rec0 s0 c' in read_e_rec s1 e
  | Ccall (xs, _, es) -> read_es_rec (read_rvs_rec s xs) es
  and read_I_rec0 s = function
  | MkI (_, i0) -> read_i_rec0 s i0
  in read_i_rec0

(** val read_I_rec :
    'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr -> SvExtra.Sv.t **)

let read_I_rec _ =
  let rec read_i_rec0 s = function
  | Cassgn (x, _, _, e) -> read_rv_rec (read_e_rec s e) x
  | Copn (xs, _, _, es) -> read_es_rec (read_rvs_rec s xs) es
  | Csyscall (xs, _, es) -> read_es_rec (read_rvs_rec s xs) es
  | Cif (b, c1, c2) ->
    let s0 = foldl read_I_rec0 s c1 in
    let s1 = foldl read_I_rec0 s0 c2 in read_e_rec s1 b
  | Cfor (_, r, c) ->
    let (p, e2) = r in
    let (_, e1) = p in
    let s0 = foldl read_I_rec0 s c in read_e_rec (read_e_rec s0 e2) e1
  | Cwhile (_, c, e, c') ->
    let s0 = foldl read_I_rec0 s c in
    let s1 = foldl read_I_rec0 s0 c' in read_e_rec s1 e
  | Ccall (xs, _, es) -> read_es_rec (read_rvs_rec s xs) es
  and read_I_rec0 s = function
  | MkI (_, i0) -> read_i_rec0 s i0
  in read_I_rec0

(** val read_c_rec :
    'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr list -> SvExtra.Sv.t **)

let read_c_rec asmop =
  foldl (read_I_rec asmop)

(** val read_i : 'a1 asmOp -> 'a1 instr_r -> SvExtra.Sv.t **)

let read_i asmop =
  read_i_rec asmop SvExtra.Sv.empty

(** val read_I : 'a1 asmOp -> 'a1 instr -> SvExtra.Sv.t **)

let read_I asmop =
  read_I_rec asmop SvExtra.Sv.empty

(** val read_c : 'a1 asmOp -> 'a1 instr list -> SvExtra.Sv.t **)

let read_c asmop =
  read_c_rec asmop SvExtra.Sv.empty

(** val vars_I : 'a1 asmOp -> 'a1 instr -> SvExtra.Sv.t **)

let vars_I asmop i =
  SvExtra.Sv.union (read_I asmop i) (write_I asmop i)

(** val vars_c : 'a1 asmOp -> 'a1 instr list -> SvExtra.Sv.t **)

let vars_c asmop c =
  SvExtra.Sv.union (read_c asmop c) (write_c asmop c)

(** val vars_lval : lval -> SvExtra.Sv.t **)

let vars_lval l =
  SvExtra.Sv.union (read_rv l) (vrv l)

(** val vars_lvals : lval list -> SvExtra.Sv.t **)

let vars_lvals ls =
  SvExtra.Sv.union (read_rvs ls) (vrvs ls)

(** val vars_l : var_i list -> SvExtra.Sv.t **)

let rec vars_l = function
| [] -> SvExtra.Sv.empty
| h :: q -> SvExtra.Sv.add (Obj.magic h.v_var) (vars_l q)

(** val vars_fd : 'a1 asmOp -> progT -> 'a1 fundef -> SvExtra.Sv.t **)

let vars_fd asmop _ fd =
  SvExtra.Sv.union (vars_l fd.f_params)
    (SvExtra.Sv.union (vars_l fd.f_res) (vars_c asmop fd.f_body))

(** val vars_p : 'a1 asmOp -> progT -> 'a1 fun_decl list -> SvExtra.Sv.t **)

let vars_p asmop pT p =
  foldr (fun f x ->
    let (_, fd) = f in SvExtra.Sv.union x (vars_fd asmop pT fd))
    SvExtra.Sv.empty p

(** val eq_gvar : gvar -> gvar -> bool **)

let eq_gvar x x' =
  (&&) (eq_op v_scope_eqType (Obj.magic x.gs) (Obj.magic x'.gs))
    (eq_op Var.var_eqType (Obj.magic x.gv.v_var) (Obj.magic x'.gv.v_var))

(** val eq_expr : pexpr -> pexpr -> bool **)

let rec eq_expr e e' =
  match e with
  | Pconst z ->
    (match e' with
     | Pconst z' -> eq_op coq_Z_eqType (Obj.magic z) (Obj.magic z')
     | _ -> false)
  | Pbool b ->
    (match e' with
     | Pbool b' -> eq_op bool_eqType (Obj.magic b) (Obj.magic b')
     | _ -> false)
  | Parr_init n ->
    (match e' with
     | Parr_init n' -> eq_op pos_eqType (Obj.magic n) (Obj.magic n')
     | _ -> false)
  | Pvar x -> (match e' with
               | Pvar x' -> eq_gvar x x'
               | _ -> false)
  | Pget (aa, w, x, e0) ->
    (match e' with
     | Pget (aa', w', x', e'0) ->
       (&&)
         ((&&)
           ((&&) (eq_op arr_access_eqType (Obj.magic aa) (Obj.magic aa'))
             (eq_op wsize_eqType (Obj.magic w) (Obj.magic w')))
           (eq_gvar x x')) (eq_expr e0 e'0)
     | _ -> false)
  | Psub (aa, w, len, x, e0) ->
    (match e' with
     | Psub (aa', w', len', x', e'0) ->
       (&&)
         ((&&)
           ((&&)
             ((&&) (eq_op arr_access_eqType (Obj.magic aa) (Obj.magic aa'))
               (eq_op wsize_eqType (Obj.magic w) (Obj.magic w')))
             (eq_op pos_eqType (Obj.magic len) (Obj.magic len')))
           (eq_gvar x x')) (eq_expr e0 e'0)
     | _ -> false)
  | Pload (w, x, e0) ->
    (match e' with
     | Pload (w', x', e'0) ->
       (&&)
         ((&&) (eq_op wsize_eqType (Obj.magic w) (Obj.magic w'))
           (eq_op Var.var_eqType (Obj.magic x.v_var) (Obj.magic x'.v_var)))
         (eq_expr e0 e'0)
     | _ -> false)
  | Papp1 (o, e0) ->
    (match e' with
     | Papp1 (o', e'0) ->
       (&&) (eq_op sop1_eqType (Obj.magic o) (Obj.magic o')) (eq_expr e0 e'0)
     | _ -> false)
  | Papp2 (o, e1, e2) ->
    (match e' with
     | Papp2 (o', e1', e2') ->
       (&&)
         ((&&) (eq_op sop2_eqType (Obj.magic o) (Obj.magic o'))
           (eq_expr e1 e1')) (eq_expr e2 e2')
     | _ -> false)
  | PappN (o, es) ->
    (match e' with
     | PappN (o', es') ->
       (&&) (eq_op opN_eqType (Obj.magic o) (Obj.magic o'))
         (all2 eq_expr es es')
     | _ -> false)
  | Pif (t0, e0, e1, e2) ->
    (match e' with
     | Pif (t', e'0, e1', e2') ->
       (&&)
         ((&&)
           ((&&) (eq_op stype_eqType (Obj.magic t0) (Obj.magic t'))
             (eq_expr e0 e'0)) (eq_expr e1 e1')) (eq_expr e2 e2')
     | _ -> false)

(** val to_lvals : Var.var list -> lval list **)

let to_lvals l =
  map (fun x -> Lvar (mk_var_i x)) l

(** val is_false : pexpr -> bool **)

let is_false = function
| Pbool b -> if b then false else true
| _ -> false

(** val is_zero : Equality.sort -> pexpr -> bool **)

let is_zero sz = function
| Papp1 (s, p) ->
  (match s with
   | Oword_of_int sz' ->
     (match p with
      | Pconst z ->
        (match z with
         | Z0 -> eq_op wsize_eqType (Obj.magic sz') sz
         | _ -> false)
      | _ -> false)
   | _ -> false)
| _ -> false

(** val instr_of_copn_args :
    'a1 asmOp -> assgn_tag -> ((lval list * 'a1 sopn) * pexpr list) -> 'a1
    instr_r **)

let instr_of_copn_args _ tg args =
  Copn ((fst (fst args)), tg, (snd (fst args)), (snd args))

(** val gen_use_vars :
    'a1 asmOp -> internal_reason -> Var.var list -> stype list -> 'a1 instr_r **)

let gen_use_vars _ ir vs tout =
  let les = map (fun t0 -> Lnone (dummy_var_info, t0)) tout in
  let op0 = Ouse_vars (ir, (map Var.vtype vs), tout) in
  let res = map (fun v -> Pvar (mk_lvar (mk_var_i v))) vs in
  Copn (les, AT_keep, (Ointernal op0), res)

(** val use_vars_get_reg :
    'a1 asmOp -> coq_PointerData -> internal_reason -> 'a1 instr_r **)

let use_vars_get_reg asmop pd ir =
  gen_use_vars asmop ir [] ((Coq_sword (coq_Uptr pd)) :: [])

(** val use_vars_use_one :
    'a1 asmOp -> internal_reason -> Var.var -> 'a1 instr_r **)

let use_vars_use_one asmop ir x =
  gen_use_vars asmop ir (x :: []) []

module type OpnArgs =
 sig
  type lval

  type rval

  val lvar : var_i -> lval

  val lmem : coq_PointerData -> wsize -> var_i -> coq_Z -> lval

  val rvar : var_i -> rval

  val rconst : wsize -> coq_Z -> rval
 end

module CopnArgs =
 struct
  type lval = Coq__1.lval

  type rval = pexpr

  (** val lvar : var_i -> Coq__1.lval **)

  let lvar x =
    Lvar x

  (** val lmem : coq_PointerData -> wsize -> var_i -> coq_Z -> Coq__1.lval **)

  let lmem x ws x0 z =
    Lmem (ws, x0, (cast_const x z))

  (** val rvar : var_i -> pexpr **)

  let rvar x =
    Pvar (mk_lvar x)

  (** val rconst : wsize -> coq_Z -> pexpr **)

  let rconst ws z =
    cast_w ws (Pconst z)
 end
