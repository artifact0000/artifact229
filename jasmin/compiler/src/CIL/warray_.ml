open BinInt
open BinNums
open BinPos
open Bool
open Datatypes
open Eqtype
open Gen_map
open Memory_model
open Seq
open Ssralg
open Ssrbool
open Ssrfun
open Ssrnat
open Utils0
open Word0
open Word_ssrZ
open Wsize

let __ = let rec f _ = Obj.repr f in Obj.repr f

type arr_access =
| AAdirect
| AAscale

(** val arr_access_beq : arr_access -> arr_access -> bool **)

let arr_access_beq x y =
  match x with
  | AAdirect -> (match y with
                 | AAdirect -> true
                 | AAscale -> false)
  | AAscale -> (match y with
                | AAdirect -> false
                | AAscale -> true)

(** val arr_access_eq_dec : arr_access -> arr_access -> bool **)

let arr_access_eq_dec x y =
  let b = arr_access_beq x y in if b then true else false

(** val arr_access_eq_axiom : arr_access Equality.axiom **)

let arr_access_eq_axiom =
  eq_axiom_of_scheme arr_access_beq

(** val arr_access_eqMixin : arr_access Equality.mixin_of **)

let arr_access_eqMixin =
  { Equality.op = arr_access_beq; Equality.mixin_of__1 = arr_access_eq_axiom }

(** val arr_access_eqType : Equality.coq_type **)

let arr_access_eqType =
  Obj.magic arr_access_eqMixin

(** val arr_size : wsize -> positive -> coq_Z **)

let arr_size ws len =
  Z.mul (wsize_size ws) (Zpos len)

(** val mk_scale : arr_access -> wsize -> coq_Z **)

let mk_scale aa ws =
  match aa with
  | AAdirect -> Zpos Coq_xH
  | AAscale -> wsize_size ws

module WArray =
 struct
  type array =
    GRing.ComRing.sort Mz.t
    (* singleton inductive, whose constructor was Build_array *)

  (** val arr_data : positive -> array -> GRing.ComRing.sort Mz.t **)

  let arr_data _ a =
    a

  (** val empty : positive -> array **)

  let empty _ =
    Mz.empty

  (** val coq_PointerZ : pointer_op **)

  let coq_PointerZ =
    { add = (fun x y -> Obj.magic Z.add x y); sub = (fun x y ->
      Z.sub (Obj.magic x) (Obj.magic y)); p_to_z = (fun x -> Obj.magic x) }

  (** val in_bound : positive -> array -> coq_Z -> bool **)

  let in_bound s _ p =
    (&&) (Z.leb Z0 p) (Z.ltb p (Zpos s))

  (** val in_boundP : positive -> array -> coq_Z -> reflect **)

  let in_boundP s _ p =
    iffP ((&&) (Z.leb Z0 p) (Z.ltb p (Zpos s)))
      (andP (Z.leb Z0 p) (Z.ltb p (Zpos s)))

  (** val is_init : positive -> array -> Equality.sort -> bool **)

  let is_init s m i =
    match Mz.get (arr_data s m) i with
    | Some _ -> true
    | None -> false

  (** val get8 :
      positive -> array -> Equality.sort -> (error, GRing.Zmodule.sort) result **)

  let get8 s m i =
    if in_bound s m (Obj.magic i)
    then if is_init s m i
         then Ok
                (Ssrfun.Option.default
                  (GRing.zero (GRing.ComRing.zmodType (word U8)))
                  (Mz.get (arr_data s m) i))
         else let s0 = ErrAddrUndef in Error s0
    else let s0 = ErrOob in Error s0

  (** val set8 :
      positive -> array -> Equality.sort -> GRing.ComRing.sort -> (error,
      array) result **)

  let set8 s m i v =
    if in_bound s m (Obj.magic i)
    then Ok (Mz.set (arr_data s m) i v)
    else let s0 = ErrOob in Error s0

  (** val valid8P :
      positive -> array -> Equality.sort -> GRing.ComRing.sort -> reflect **)

  let valid8P s m p _ =
    let _evar_0_ = ReflectT in
    let _evar_0_0 = ReflectF in
    if in_bound s m (Obj.magic p) then _evar_0_ else _evar_0_0

  (** val array_CM : positive -> array coreMem **)

  let array_CM s =
    { get = (get8 s); set = (set8 s); valid8 = (Obj.magic in_bound s);
      Memory_model.valid8P = (valid8P s) }

  (** val in_range : positive -> Equality.sort -> wsize -> bool **)

  let in_range s p ws =
    (&&) (Z.leb Z0 (Obj.magic p))
      (Z.leb (Z.add (Obj.magic p) (wsize_size ws)) (Zpos s))

  (** val in_rangeP : positive -> coq_Z -> wsize -> reflect **)

  let in_rangeP s p ws =
    let _evar_0_ = fun _ -> ReflectT in
    let _evar_0_0 = fun _ -> ReflectF in
    (match andP (Z.leb Z0 p) (Z.leb (Z.add p (wsize_size ws)) (Zpos s)) with
     | ReflectT -> _evar_0_ __
     | ReflectF -> _evar_0_0 __)

  (** val get :
      positive -> arr_access -> wsize -> array -> coq_Z -> GRing.ComRing.sort
      exec **)

  let get len aa ws a p =
    CoreMem.read coq_Z_eqType coq_PointerZ (array_CM len) a
      (Obj.magic Z.mul p (mk_scale aa ws)) ws

  (** val set :
      positive -> wsize -> array -> arr_access -> coq_Z -> GRing.ComRing.sort
      -> array exec **)

  let set len ws a aa p v =
    CoreMem.write coq_Z_eqType coq_PointerZ (array_CM len) a
      (Obj.magic Z.mul p (mk_scale aa ws)) ws v

  (** val fcopy :
      wsize -> positive -> array -> array -> coq_Z -> coq_Z -> (error, array)
      result **)

  let fcopy ws len a t0 i j =
    foldM (fun i0 t1 ->
      match get len AAscale ws a i0 with
      | Ok x -> set len ws t1 AAscale i0 x
      | Error s -> Error s) t0 (ziota i j)

  (** val copy : wsize -> positive -> array -> (error, array) result **)

  let copy ws p a =
    fcopy ws (Z.to_pos (arr_size ws p)) a (empty (Z.to_pos (arr_size ws p)))
      Z0 (Zpos p)

  (** val fill : positive -> GRing.ComRing.sort list -> array exec **)

  let fill len l =
    if eq_op nat_eqType (Obj.magic Pos.to_nat len) (Obj.magic size l)
    then (match foldM (fun w pt ->
                  match set len U8 (snd pt) AAscale (fst pt) w with
                  | Ok x -> Ok ((Z.add (fst pt) (Zpos Coq_xH)), x)
                  | Error s -> Error s) (Z0, (empty len)) l with
          | Ok x -> Ok (snd x)
          | Error s -> Error s)
    else let s = ErrType in Error s

  (** val get_sub_data :
      arr_access -> wsize -> positive -> GRing.ComRing.sort Mz.t -> coq_Z ->
      GRing.ComRing.sort Mz.t **)

  let get_sub_data aa ws len a p =
    let size0 = arr_size ws len in
    let start = Z.mul p (mk_scale aa ws) in
    foldr (fun i data ->
      match Mz.get a (Obj.magic Z.add start i) with
      | Some w -> Mz.set data (Obj.magic i) w
      | None -> Mz.remove data (Obj.magic i)) Mz.empty (ziota Z0 size0)

  (** val get_sub :
      positive -> arr_access -> wsize -> positive -> array -> coq_Z -> array
      exec **)

  let get_sub lena aa ws len a p =
    let size0 = arr_size ws len in
    let start = Z.mul p (mk_scale aa ws) in
    if (&&) (Z.leb Z0 start) (Z.leb (Z.add start size0) (Zpos lena))
    then Ok (get_sub_data aa ws len (arr_data lena a) p)
    else Error ErrOob

  (** val set_sub_data :
      arr_access -> wsize -> positive -> GRing.ComRing.sort Mz.t -> coq_Z ->
      GRing.ComRing.sort Mz.t -> GRing.ComRing.sort Mz.t **)

  let set_sub_data aa ws len a p b =
    let size0 = arr_size ws len in
    let start = Z.mul p (mk_scale aa ws) in
    foldr (fun i data ->
      match Mz.get b (Obj.magic i) with
      | Some w -> Mz.set data (Obj.magic Z.add start i) w
      | None -> Mz.remove data (Obj.magic Z.add start i)) a (ziota Z0 size0)

  (** val set_sub :
      positive -> arr_access -> wsize -> positive -> array -> coq_Z -> array
      -> array exec **)

  let set_sub lena aa ws len a p b =
    let size0 = arr_size ws len in
    let start = Z.mul p (mk_scale aa ws) in
    if (&&) (Z.leb Z0 start) (Z.leb (Z.add start size0) (Zpos lena))
    then Ok
           (set_sub_data aa ws len (arr_data lena a) p
             (arr_data (Z.to_pos (arr_size ws len)) b))
    else Error ErrOob

  (** val cast : positive -> positive -> array -> (error, array) result **)

  let cast len len' a =
    if eq_op pos_eqType (Obj.magic len') (Obj.magic len)
    then Ok (arr_data len a)
    else type_error

  (** val of_list : wsize -> GRing.ComRing.sort list -> array **)

  let of_list ws l =
    let do8 = fun mz w ->
      let (m, z) = mz in ((Mz.set m (Obj.magic z) w), (Z.succ z))
    in
    let dow = fun mz w -> foldl do8 mz (LE.encode ws w) in
    let (m, _) = foldl dow (Mz.empty, Z0) l in m
 end
