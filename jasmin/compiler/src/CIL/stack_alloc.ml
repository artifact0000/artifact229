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

module E =
 struct
  (** val pass : char list **)

  let pass =
    's'::('t'::('a'::('c'::('k'::(' '::('a'::('l'::('l'::('o'::('c'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))

  (** val stk_error_gen : bool -> var_i -> pp_error -> pp_error_loc **)

  let stk_error_gen internal x msg =
    { pel_msg = msg; pel_fn = None; pel_fi = None; pel_ii = None; pel_vi =
      (Some x.v_info); pel_pass = (Some pass); pel_internal = internal }

  (** val stk_error : var_i -> pp_error -> pp_error_loc **)

  let stk_error =
    stk_error_gen false

  (** val stk_ierror : var_i -> pp_error -> pp_error_loc **)

  let stk_ierror =
    stk_error_gen true

  (** val stk_ierror_basic : var_i -> char list -> pp_error_loc **)

  let stk_ierror_basic x msg =
    stk_ierror x
      (pp_box ((PPEstring
        msg) :: ((pp_nobox ((PPEstring ('('::[])) :: ((PPEvar
                   x.v_var) :: ((PPEstring (')'::[])) :: [])))) :: [])))

  (** val stk_error_no_var_gen : bool -> char list -> pp_error_loc **)

  let stk_error_no_var_gen internal msg =
    { pel_msg = (PPEstring msg); pel_fn = None; pel_fi = None; pel_ii = None;
      pel_vi = None; pel_pass = (Some pass); pel_internal = internal }

  (** val stk_error_no_var : char list -> pp_error_loc **)

  let stk_error_no_var =
    stk_error_no_var_gen false

  (** val stk_ierror_no_var : char list -> pp_error_loc **)

  let stk_ierror_no_var =
    stk_error_no_var_gen true
 end

(** val size_of : stype -> coq_Z **)

let size_of = function
| Coq_sarr n -> Zpos n
| Coq_sword sz -> wsize_size sz
| _ -> Zpos Coq_xH

type slot = Var.var

type region = { r_slot : slot; r_align : wsize; r_writable : bool }

(** val region_beq : region -> region -> bool **)

let region_beq r1 r2 =
  (&&) (eq_op Var.var_eqType (Obj.magic r1.r_slot) (Obj.magic r2.r_slot))
    ((&&) (eq_op wsize_eqType (Obj.magic r1.r_align) (Obj.magic r2.r_align))
      (eq_op bool_eqType (Obj.magic r1.r_writable) (Obj.magic r2.r_writable)))

(** val region_same : region -> region -> bool **)

let region_same r1 r2 =
  eq_op Var.var_eqType (Obj.magic r1.r_slot) (Obj.magic r2.r_slot)

(** val region_axiom : region Equality.axiom **)

let region_axiom __top_assumption_ =
  let _evar_0_ = fun xs1 xa1 xw1 __top_assumption_0 ->
    let _evar_0_ = fun xs2 xa2 xw2 ->
      iffP
        ((&&) (eq_op Var.var_eqType (Obj.magic xs1) (Obj.magic xs2))
          ((&&) (eq_op wsize_eqType (Obj.magic xa1) (Obj.magic xa2))
            (eq_op bool_eqType (Obj.magic xw1) (Obj.magic xw2))))
        (and3P (eq_op Var.var_eqType (Obj.magic xs1) (Obj.magic xs2))
          (eq_op wsize_eqType (Obj.magic xa1) (Obj.magic xa2))
          (eq_op bool_eqType (Obj.magic xw1) (Obj.magic xw2)))
    in
    let { r_slot = r_slot0; r_align = r_align0; r_writable = r_writable0 } =
      __top_assumption_0
    in
    _evar_0_ r_slot0 r_align0 r_writable0
  in
  let { r_slot = r_slot0; r_align = r_align0; r_writable = r_writable0 } =
    __top_assumption_
  in
  _evar_0_ r_slot0 r_align0 r_writable0

(** val region_eqMixin : region Equality.mixin_of **)

let region_eqMixin =
  { Equality.op = region_beq; Equality.mixin_of__1 = region_axiom }

(** val region_eqType : Equality.coq_type **)

let region_eqType =
  Obj.magic region_eqMixin

module CmpR =
 struct
  (** val t : Equality.coq_type **)

  let t =
    Equality.clone region_eqType (Obj.magic region_eqMixin) (fun x -> x)

  (** val cmp : Equality.sort -> Equality.sort -> comparison **)

  let cmp r1 r2 =
    match bool_cmp (Obj.magic r1).r_writable (Obj.magic r2).r_writable with
    | Eq ->
      (match wsize_cmp (Obj.magic r1).r_align (Obj.magic r2).r_align with
       | Eq -> Var.var_cmp (Obj.magic r1).r_slot (Obj.magic r2).r_slot
       | x -> x)
    | x -> x
 end

module Mr = Mmake(CmpR)

type zone = { z_ofs : coq_Z; z_len : coq_Z }

(** val internal_Z_beq : coq_Z -> coq_Z -> bool **)

let internal_Z_beq x y =
  match x with
  | Z0 -> (match y with
           | Z0 -> true
           | _ -> false)
  | Zpos x0 ->
    (match y with
     | Zpos x1 -> internal_positive_beq x0 x1
     | _ -> false)
  | Zneg x0 ->
    (match y with
     | Zneg x1 -> internal_positive_beq x0 x1
     | _ -> false)

(** val zone_beq : zone -> zone -> bool **)

let zone_beq x y =
  let { z_ofs = z_ofs0; z_len = z_len0 } = x in
  let { z_ofs = z_ofs1; z_len = z_len1 } = y in
  (&&) (internal_Z_beq z_ofs0 z_ofs1) (internal_Z_beq z_len0 z_len1)

(** val zone_eq_axiom : zone Equality.axiom **)

let zone_eq_axiom =
  eq_axiom_of_scheme zone_beq

(** val zone_eqMixin : zone Equality.mixin_of **)

let zone_eqMixin =
  { Equality.op = zone_beq; Equality.mixin_of__1 = zone_eq_axiom }

(** val zone_eqType : Equality.coq_type **)

let zone_eqType =
  Obj.magic zone_eqMixin

(** val disjoint_zones : zone -> zone -> bool **)

let disjoint_zones z1 z2 =
  (||) (cmp_le Z.compare (Z.add z1.z_ofs z1.z_len) z2.z_ofs)
    (cmp_le Z.compare (Z.add z2.z_ofs z2.z_len) z1.z_ofs)

type sub_region = { sr_region : region; sr_zone : zone }

(** val sub_region_beq : sub_region -> sub_region -> bool **)

let sub_region_beq sr1 sr2 =
  (&&)
    (eq_op region_eqType (Obj.magic sr1.sr_region) (Obj.magic sr2.sr_region))
    (eq_op zone_eqType (Obj.magic sr1.sr_zone) (Obj.magic sr2.sr_zone))

(** val sub_region_eq_axiom : sub_region Equality.axiom **)

let sub_region_eq_axiom __top_assumption_ =
  let _evar_0_ = fun mp1 sub1 __top_assumption_0 ->
    let _evar_0_ = fun mp2 sub2 ->
      iffP
        ((&&) (eq_op region_eqType (Obj.magic mp1) (Obj.magic mp2))
          (eq_op zone_eqType (Obj.magic sub1) (Obj.magic sub2)))
        (andP (eq_op region_eqType (Obj.magic mp1) (Obj.magic mp2))
          (eq_op zone_eqType (Obj.magic sub1) (Obj.magic sub2)))
    in
    let { sr_region = sr_region0; sr_zone = sr_zone0 } = __top_assumption_0 in
    _evar_0_ sr_region0 sr_zone0
  in
  let { sr_region = sr_region0; sr_zone = sr_zone0 } = __top_assumption_ in
  _evar_0_ sr_region0 sr_zone0

(** val sub_region_eqMixin : sub_region Equality.mixin_of **)

let sub_region_eqMixin =
  { Equality.op = sub_region_beq; Equality.mixin_of__1 = sub_region_eq_axiom }

(** val sub_region_eqType : Equality.coq_type **)

let sub_region_eqType =
  Obj.magic sub_region_eqMixin

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

(** val check_align :
    var_i -> sub_region -> wsize -> (pp_error_loc, unit) result **)

let check_align x sr ws =
  if cmp_le wsize_cmp ws sr.sr_region.r_align
  then if eq_op coq_Z_eqType
            (Obj.magic Z.coq_land sr.sr_zone.z_ofs
              (Z.sub (wsize_size ws) (Zpos Coq_xH))) (Obj.magic Z0)
       then Ok ()
       else Error
              (E.stk_ierror_basic x
                ('u'::('n'::('a'::('l'::('i'::('g'::('n'::('e'::('d'::(' '::('s'::('u'::('b'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::[])))))))))))))))))))))
  else let s =
         E.stk_ierror_basic x
           ('u'::('n'::('a'::('l'::('i'::('g'::('n'::('e'::('d'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::[]))))))))))))))))
       in
       Error s

(** val writable : var_i -> region -> (pp_error_loc, unit) result **)

let writable x r =
  if r.r_writable
  then Ok ()
  else Error
         (E.stk_error x
           (pp_box ((PPEstring
             ('c'::('a'::('n'::('n'::('o'::('t'::(' '::('w'::('r'::('i'::('t'::('e'::(' '::('t'::('o'::(' '::('t'::('h'::('e'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))) :: ((PPEvar
             x.v_var) :: ((PPEstring
             ('t'::('a'::('r'::('g'::('e'::('t'::('t'::('i'::('n'::('g'::[]))))))))))) :: ((PPEvar
             r.r_slot) :: []))))))

module Region =
 struct
  type bytes_map = ByteSet.t Mvar.t

  type region_map = { var_region : sub_region Mvar.t;
                      region_var : bytes_map Mr.t }

  (** val var_region : region_map -> sub_region Mvar.t **)

  let var_region r =
    r.var_region

  (** val region_var : region_map -> bytes_map Mr.t **)

  let region_var r =
    r.region_var

  (** val empty_bytes_map : ByteSet.t Mvar.t **)

  let empty_bytes_map =
    Mvar.empty

  (** val empty : region_map **)

  let empty =
    { var_region = Mvar.empty; region_var = Mr.empty }

  (** val get_sub_region :
      region_map -> var_i -> (pp_error_loc, sub_region) result **)

  let get_sub_region rmap x =
    match Mvar.get rmap.var_region (Obj.magic x.v_var) with
    | Some sr -> Ok sr
    | None ->
      Error
        (E.stk_error x
          (pp_box ((PPEstring
            ('n'::('o'::(' '::('r'::('e'::('g'::('i'::('o'::('n'::(' '::('a'::('s'::('s'::('o'::('c'::('i'::('a'::('t'::('e'::('d'::(' '::('t'::('o'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))))))))))))) :: ((PPEvar
            x.v_var) :: []))))

  (** val get_bytes_map : region -> ByteSet.t Mvar.t Mr.t -> bytes_map **)

  let get_bytes_map r rv =
    Ssrfun.Option.default empty_bytes_map (Mr.get rv (Obj.magic r))

  (** val get_bytes : Var.var -> bytes_map -> ByteSet.t **)

  let get_bytes x bytes_map0 =
    Ssrfun.Option.default ByteSet.empty (Mvar.get bytes_map0 (Obj.magic x))

  (** val interval_of_zone : zone -> interval **)

  let interval_of_zone z =
    { imin = z.z_ofs; imax = (Z.add z.z_ofs z.z_len) }

  (** val get_var_bytes :
      ByteSet.t Mvar.t Mr.t -> region -> Var.var -> ByteSet.t **)

  let get_var_bytes rv r x =
    let bm = get_bytes_map r rv in get_bytes x bm

  (** val sub_zone_at_ofs : zone -> coq_Z option -> coq_Z -> zone **)

  let sub_zone_at_ofs z ofs len =
    match ofs with
    | Some ofs0 -> { z_ofs = (Z.add z.z_ofs ofs0); z_len = len }
    | None -> z

  (** val sub_region_at_ofs :
      sub_region -> coq_Z option -> coq_Z -> sub_region **)

  let sub_region_at_ofs sr ofs len =
    { sr_region = sr.sr_region; sr_zone =
      (sub_zone_at_ofs sr.sr_zone ofs len) }

  (** val check_valid :
      region_map -> var_i -> coq_Z option -> coq_Z -> (pp_error_loc,
      sub_region * sub_region) result **)

  let check_valid rmap x ofs len =
    match get_sub_region rmap x with
    | Ok x0 ->
      let bytes = get_var_bytes rmap.region_var x0.sr_region x.v_var in
      let sr' = sub_region_at_ofs x0 ofs len in
      let isub_ofs = interval_of_zone sr'.sr_zone in
      if ByteSet.mem bytes isub_ofs
      then Ok (x0, sr')
      else let s =
             E.stk_error x
               (pp_box ((PPEstring
                 ('t'::('h'::('e'::(' '::('r'::('e'::('g'::('i'::('o'::('n'::(' '::('a'::('s'::('s'::('o'::('c'::('i'::('a'::('t'::('e'::('d'::(' '::('t'::('o'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))))))))))))) :: ((PPEvar
                 x.v_var) :: ((PPEstring
                 ('i'::('s'::(' '::('p'::('a'::('r'::('t'::('i'::('a'::('l'::[]))))))))))) :: []))))
           in
           Error s
    | Error s -> Error s

  (** val clear_bytes : interval -> ByteSet.t -> ByteSet.t **)

  let clear_bytes i bytes =
    ByteSet.remove bytes i

  (** val clear_bytes_map : interval -> bytes_map -> ByteSet.t Mvar.Map.t **)

  let clear_bytes_map i bm =
    Mvar.map (clear_bytes i) bm

  (** val set_pure_bytes :
      ByteSet.t Mvar.t Mr.t -> Var.var -> sub_region -> coq_Z option -> coq_Z
      -> ByteSet.t Mvar.t Mr.Map.t **)

  let set_pure_bytes rv x sr ofs len =
    let z = sr.sr_zone in
    let z1 = sub_zone_at_ofs z ofs len in
    let i = interval_of_zone z1 in
    let bm = get_bytes_map sr.sr_region rv in
    let bytes =
      match ofs with
      | Some _ -> ByteSet.add i (get_bytes x bm)
      | None -> get_bytes x bm
    in
    let bm0 = clear_bytes_map i bm in
    let bm1 = Mvar.set bm0 (Obj.magic x) bytes in
    Mr.set rv (Obj.magic sr.sr_region) bm1

  (** val set_bytes :
      ByteSet.t Mvar.t Mr.t -> var_i -> sub_region -> coq_Z option -> coq_Z
      -> (pp_error_loc, ByteSet.t Mvar.t Mr.Map.t) result **)

  let set_bytes rv x sr ofs len =
    match writable x sr.sr_region with
    | Ok _ -> Ok (set_pure_bytes rv x.v_var sr ofs len)
    | Error s -> Error s

  (** val set_sub_region :
      region_map -> var_i -> sub_region -> coq_Z option -> coq_Z ->
      (pp_error_loc, region_map) result **)

  let set_sub_region rmap x sr ofs len =
    match set_bytes rmap.region_var x sr ofs len with
    | Ok x0 ->
      Ok { var_region = (Mvar.set rmap.var_region (Obj.magic x.v_var) sr);
        region_var = x0 }
    | Error s -> Error s

  (** val sub_region_stkptr : slot -> wsize -> zone -> sub_region **)

  let sub_region_stkptr s ws z =
    let r = { r_slot = s; r_align = ws; r_writable = true } in
    { sr_region = r; sr_zone = z }

  (** val set_stack_ptr :
      coq_PointerData -> region_map -> slot -> wsize -> zone -> Var.var ->
      region_map **)

  let set_stack_ptr pd rmap s ws z x' =
    let sr = sub_region_stkptr s ws z in
    let rv =
      set_pure_bytes rmap.region_var x' sr (Some Z0)
        (wsize_size (coq_Uptr pd))
    in
    { var_region = rmap.var_region; region_var = rv }

  (** val check_stack_ptr :
      coq_PointerData -> ByteSet.t Mvar.t Mr.t -> slot -> wsize -> zone ->
      Var.var -> bool **)

  let check_stack_ptr pd rmap s ws z x' =
    let sr = sub_region_stkptr s ws z in
    let z0 = sub_zone_at_ofs z (Some Z0) (wsize_size (coq_Uptr pd)) in
    let i = interval_of_zone z0 in
    let bytes = get_var_bytes rmap sr.sr_region x' in ByteSet.mem bytes i

  (** val set_word :
      region_map -> var_i -> sub_region -> wsize -> (pp_error_loc,
      region_map) result **)

  let set_word rmap x sr ws =
    match check_align x sr ws with
    | Ok _ -> set_sub_region rmap x sr (Some Z0) (size_of (Var.vtype x.v_var))
    | Error s -> Error s

  (** val set_arr_word :
      region_map -> var_i -> coq_Z option -> wsize -> (pp_error_loc,
      region_map) result **)

  let set_arr_word rmap x ofs ws =
    match get_sub_region rmap x with
    | Ok x0 ->
      (match check_align x x0 ws with
       | Ok _ -> set_sub_region rmap x x0 ofs (wsize_size ws)
       | Error s -> Error s)
    | Error s -> Error s

  (** val set_arr_call :
      region_map -> var_i -> sub_region -> (pp_error_loc, region_map) result **)

  let set_arr_call rmap x sr =
    set_sub_region rmap x sr (Some Z0) (size_of (Var.vtype x.v_var))

  (** val set_move_bytes :
      ByteSet.t Mvar.t Mr.t -> Var.var -> sub_region -> ByteSet.t Mvar.t
      Mr.Map.t **)

  let set_move_bytes rv x sr =
    let bm = get_bytes_map sr.sr_region rv in
    let bytes = get_bytes x bm in
    let bm0 =
      Mvar.set bm (Obj.magic x)
        (ByteSet.add (interval_of_zone sr.sr_zone) bytes)
    in
    Mr.set rv (Obj.magic sr.sr_region) bm0

  (** val set_move_sub : region_map -> Var.var -> sub_region -> region_map **)

  let set_move_sub rmap x sr =
    let rv = set_move_bytes rmap.region_var x sr in
    { var_region = rmap.var_region; region_var = rv }

  (** val set_arr_sub :
      region_map -> var_i -> coq_Z -> coq_Z -> Equality.sort ->
      (pp_error_loc, region_map) result **)

  let set_arr_sub rmap x ofs len sr_from =
    match get_sub_region rmap x with
    | Ok x0 ->
      let sr' = sub_region_at_ofs x0 (Some ofs) len in
      if eq_op sub_region_eqType (Obj.magic sr') sr_from
      then Ok (set_move_sub rmap x.v_var sr')
      else let s =
             E.stk_ierror x
               (pp_box ((PPEstring
                 ('t'::('h'::('e'::(' '::('a'::('s'::('s'::('i'::('g'::('n'::('m'::('e'::('n'::('t'::(' '::('t'::('o'::(' '::('s'::('u'::('b'::('-'::('a'::('r'::('r'::('a'::('y'::[])))))))))))))))))))))))))))) :: ((PPEvar
                 x.v_var) :: ((PPEstring
                 ('c'::('a'::('n'::('n'::('o'::('t'::(' '::('b'::('e'::(' '::('t'::('u'::('r'::('n'::('e'::('d'::(' '::('i'::('n'::('t'::('o'::(' '::('a'::(' '::('n'::('o'::('p'::(':'::(' '::('s'::('o'::('u'::('r'::('c'::('e'::(' '::('a'::('n'::('d'::(' '::('d'::('e'::('s'::('t'::('i'::('n'::('a'::('t'::('i'::('o'::('n'::(' '::('r'::('e'::('g'::('i'::('o'::('n'::('s'::(' '::('a'::('r'::('e'::(' '::('n'::('o'::('t'::(' '::('e'::('q'::('u'::('a'::('l'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []))))
           in
           Error s
    | Error s -> Error s

  (** val set_move : region_map -> Var.var -> sub_region -> region_map **)

  let set_move rmap x sr =
    let rv = set_move_bytes rmap.region_var x sr in
    { var_region = (Mvar.set rmap.var_region (Obj.magic x) sr); region_var =
    rv }

  (** val set_arr_init : region_map -> Var.var -> sub_region -> region_map **)

  let set_arr_init =
    set_move

  (** val incl_bytes_map : region -> bytes_map -> bytes_map -> bool **)

  let incl_bytes_map _ bm1 bm2 =
    Mvar.incl (fun _ -> ByteSet.subset) bm1 bm2

  (** val incl : region_map -> region_map -> bool **)

  let incl rmap1 rmap2 =
    (&&)
      (Mvar.incl (fun _ r1 r2 ->
        eq_op sub_region_eqType (Obj.magic r1) (Obj.magic r2))
        rmap1.var_region rmap2.var_region)
      (Mr.incl (Obj.magic incl_bytes_map) rmap1.region_var rmap2.region_var)

  (** val merge_bytes :
      Var.var -> ByteSet.t option -> ByteSet.t option -> ByteSet.t option **)

  let merge_bytes _ bytes1 bytes2 =
    match bytes1 with
    | Some bytes3 ->
      (match bytes2 with
       | Some bytes4 ->
         let bytes = ByteSet.inter bytes3 bytes4 in
         if ByteSet.is_empty bytes then None else Some bytes
       | None -> None)
    | None -> None

  (** val merge_bytes_map :
      region -> bytes_map option -> bytes_map option -> ByteSet.t Mvar.t
      option **)

  let merge_bytes_map _ bm1 bm2 =
    match bm1 with
    | Some bm3 ->
      (match bm2 with
       | Some bm4 ->
         let bm = Mvar.map2 (Obj.magic merge_bytes) bm3 bm4 in
         if Mvar.is_empty bm then None else Some bm
       | None -> None)
    | None -> None

  (** val merge : region_map -> region_map -> region_map **)

  let merge rmap1 rmap2 =
    { var_region =
      (Mvar.map2 (fun _ osr1 osr2 ->
        match osr1 with
        | Some sr1 ->
          (match osr2 with
           | Some sr2 ->
             if eq_op sub_region_eqType (Obj.magic sr1) (Obj.magic sr2)
             then osr1
             else None
           | None -> None)
        | None -> None) rmap1.var_region rmap2.var_region); region_var =
      (Mr.map2 (Obj.magic merge_bytes_map) rmap1.region_var rmap2.region_var) }
 end

(** val mul : coq_PointerData -> pexpr -> pexpr -> pexpr **)

let mul pd x x0 =
  Papp2 ((Omul (Op_w (coq_Uptr pd))), x, x0)

(** val add : coq_PointerData -> pexpr -> pexpr -> pexpr **)

let add pd x x0 =
  Papp2 ((Oadd (Op_w (coq_Uptr pd))), x, x0)

(** val mk_ofs :
    coq_PointerData -> arr_access -> wsize -> pexpr -> coq_Z -> pexpr **)

let mk_ofs pd aa ws e1 ofs =
  let sz = mk_scale aa ws in
  (match is_const e1 with
   | Some i -> cast_const pd (Z.add (Z.mul i sz) ofs)
   | None ->
     add pd (mul pd (cast_const pd sz) (cast_ptr pd e1)) (cast_const pd ofs))

(** val mk_ofsi : arr_access -> wsize -> pexpr -> coq_Z option **)

let mk_ofsi aa ws e1 =
  match is_const e1 with
  | Some i -> Some (Z.mul i (mk_scale aa ws))
  | None -> None

(** val assert_check : bool -> bool -> 'a1 -> ('a1, unit) result **)

let assert_check check b e =
  if check then if b then Ok () else Error e else Ok ()

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

(** val mk_mov : vptr_kind -> mov_kind **)

let mk_mov = function
| VKglob _ -> MK_LEA
| VKptr p ->
  (match p with
   | Pdirect (_, _, _, _, v0) ->
     (match v0 with
      | Slocal -> MK_MOV
      | Sglob -> MK_LEA)
   | _ -> MK_MOV)

(** val get_global :
    pos_map -> var_i -> (pp_error_loc, coq_Z * wsize) result **)

let get_global pmap x =
  match Mvar.get pmap.globals (Obj.magic x.v_var) with
  | Some z -> Ok z
  | None ->
    Error
      (E.stk_ierror_basic x
        ('u'::('n'::('a'::('l'::('l'::('o'::('c'::('a'::('t'::('e'::('d'::(' '::('g'::('l'::('o'::('b'::('a'::('l'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))))))))

(** val get_local : pos_map -> Var.var -> ptr_kind option **)

let get_local pmap x =
  Mvar.get pmap.locals (Obj.magic x)

(** val check_diff : pos_map -> var_i -> (pp_error_loc, unit) result **)

let check_diff pmap x =
  if SvExtra.Sv.mem (Obj.magic x.v_var) pmap.vnew
  then Error
         (E.stk_ierror_basic x
           ('t'::('h'::('e'::(' '::('c'::('o'::('d'::('e'::(' '::('w'::('r'::('i'::('t'::('e'::('s'::(' '::('t'::('o'::(' '::('o'::('n'::('e'::(' '::('o'::('f'::(' '::('t'::('h'::('e'::(' '::('n'::('e'::('w'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::('s'::[]))))))))))))))))))))))))))))))))))))))))))))
  else Ok ()

(** val check_var : pos_map -> var_i -> (pp_error_loc, unit) result **)

let check_var pmap x =
  match get_local pmap x.v_var with
  | Some _ ->
    Error
      (E.stk_error x
        (pp_box ((PPEvar x.v_var) :: ((PPEstring
          ('i'::('s'::(' '::('a'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(','::(' '::('b'::('u'::('t'::(' '::('a'::(' '::('r'::('e'::('g'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('i'::('s'::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))))))))))))))))))))))) :: []))))
  | None -> Ok ()

(** val with_var : var_i -> Var.var -> var_i **)

let with_var xi x =
  { v_var = x; v_info = xi.v_info }

(** val base_ptr : pos_map -> v_scope -> Var.var **)

let base_ptr pmap = function
| Slocal -> pmap.vrsp
| Sglob -> pmap.vrip

(** val addr_from_pk :
    pos_map -> var_i -> ptr_kind -> (pp_error_loc, var_i * coq_Z) result **)

let addr_from_pk pmap x = function
| Pdirect (_, ofs, _, z, sc) ->
  Ok ((with_var x (base_ptr pmap sc)), (Z.add ofs z.z_ofs))
| Pregptr p -> Ok ((with_var x p), Z0)
| Pstkptr (_, _, _, _, _) ->
  Error
    (E.stk_error x
      (pp_box ((PPEvar x.v_var) :: ((PPEstring
        ('i'::('s'::(' '::('a'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::(','::(' '::('i'::('t'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('a'::('p'::('p'::('e'::('a'::('r'::(' '::('i'::('n'::(' '::('a'::('n'::(' '::('e'::('x'::('p'::('r'::('e'::('s'::('s'::('i'::('o'::('n'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []))))

(** val addr_from_vpk :
    pos_map -> var_i -> vptr_kind -> (pp_error_loc, var_i * coq_Z) result **)

let addr_from_vpk pmap x = function
| VKglob zws -> Ok ((with_var x pmap.vrip), (fst zws))
| VKptr pk -> addr_from_pk pmap x pk

(** val mk_addr_ptr :
    coq_PointerData -> pos_map -> var_i -> arr_access -> wsize -> ptr_kind ->
    pexpr -> (pp_error_loc, var_i * pexpr) result **)

let mk_addr_ptr pd pmap x aa ws pk e1 =
  match addr_from_pk pmap x pk with
  | Ok x0 -> Ok ((fst x0), (mk_ofs pd aa ws e1 (snd x0)))
  | Error s -> Error s

(** val mk_addr :
    coq_PointerData -> pos_map -> var_i -> arr_access -> wsize -> vptr_kind
    -> pexpr -> (pp_error_loc, var_i * pexpr) result **)

let mk_addr pd pmap x aa ws vpk e1 =
  match addr_from_vpk pmap x vpk with
  | Ok x0 -> Ok ((fst x0), (mk_ofs pd aa ws e1 (snd x0)))
  | Error s -> Error s

(** val get_var_kind :
    pos_map -> gvar -> (pp_error_loc, vptr_kind option) result **)

let get_var_kind pmap x =
  let xv = x.gv in
  if is_glob x
  then (match get_global pmap xv with
        | Ok x0 -> Ok (Some (VKglob x0))
        | Error s -> Error s)
  else Ok (Ssrfun.Option.map (fun x0 -> VKptr x0) (get_local pmap xv.v_var))

(** val sub_region_full : Var.var -> region -> sub_region **)

let sub_region_full x r =
  let z = { z_ofs = Z0; z_len = (size_of (Var.vtype x)) } in
  { sr_region = r; sr_zone = z }

(** val sub_region_glob : slot -> wsize -> sub_region **)

let sub_region_glob x ws =
  let r = { r_slot = x; r_align = ws; r_writable = false } in
  sub_region_full x r

(** val check_vpk :
    Region.region_map -> var_i -> vptr_kind -> coq_Z option -> coq_Z ->
    (pp_error_loc, sub_region * sub_region) result **)

let check_vpk rmap x vpk ofs len =
  match vpk with
  | VKglob p ->
    let (_, ws) = p in
    let sr = sub_region_glob x.v_var ws in
    Ok (sr, (Region.sub_region_at_ofs sr ofs len))
  | VKptr _ -> Region.check_valid rmap x ofs len

(** val check_vpk_word :
    Region.region_map -> var_i -> vptr_kind -> coq_Z option -> wsize ->
    (pp_error_loc, unit) result **)

let check_vpk_word rmap x vpk ofs ws =
  match check_vpk rmap x vpk ofs (wsize_size ws) with
  | Ok x0 -> check_align x (fst x0) ws
  | Error s -> Error s

(** val alloc_e :
    coq_PointerData -> pos_map -> Region.region_map -> pexpr ->
    (pp_error_loc, pexpr) result **)

let rec alloc_e pd pmap rmap e = match e with
| Pvar x ->
  let xv = x.gv in
  (match get_var_kind pmap x with
   | Ok x0 ->
     (match x0 with
      | Some vpk ->
        (match is_word_type (Var.vtype xv.v_var) with
         | Some ws ->
           (match check_vpk_word rmap xv vpk (Some Z0) ws with
            | Ok _ ->
              (match mk_addr pd pmap xv AAdirect ws vpk (Pconst Z0) with
               | Ok x1 -> Ok (Pload (ws, (fst x1), (snd x1)))
               | Error s -> Error s)
            | Error s -> Error s)
         | None ->
           Error
             (E.stk_ierror_basic xv
               ('n'::('o'::('t'::(' '::('a'::(' '::('w'::('o'::('r'::('d'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('i'::('n'::(' '::('e'::('x'::('p'::('r'::('e'::('s'::('s'::('i'::('o'::('n'::[])))))))))))))))))))))))))))))))))))
      | None ->
        (match check_diff pmap xv with
         | Ok _ -> Ok e
         | Error s -> Error s))
   | Error s -> Error s)
| Pget (aa, ws, x, e1) ->
  let xv = x.gv in
  (match alloc_e pd pmap rmap e1 with
   | Ok x0 ->
     (match get_var_kind pmap x with
      | Ok x1 ->
        (match x1 with
         | Some vpk ->
           let ofs = mk_ofsi aa ws x0 in
           (match check_vpk_word rmap xv vpk ofs ws with
            | Ok _ ->
              (match mk_addr pd pmap xv aa ws vpk x0 with
               | Ok x2 -> Ok (Pload (ws, (fst x2), (snd x2)))
               | Error s -> Error s)
            | Error s -> Error s)
         | None ->
           (match check_diff pmap xv with
            | Ok _ -> Ok (Pget (aa, ws, x, x0))
            | Error s -> Error s))
      | Error s -> Error s)
   | Error s -> Error s)
| Psub (_, _, _, x, _) ->
  Error (E.stk_ierror_basic x.gv ('P'::('s'::('u'::('b'::[])))))
| Pload (ws, x, e1) ->
  (match check_var pmap x with
   | Ok _ ->
     (match check_diff pmap x with
      | Ok _ ->
        (match alloc_e pd pmap rmap e1 with
         | Ok x0 -> Ok (Pload (ws, x, x0))
         | Error s -> Error s)
      | Error s -> Error s)
   | Error s -> Error s)
| Papp1 (o, e1) ->
  (match alloc_e pd pmap rmap e1 with
   | Ok x -> Ok (Papp1 (o, x))
   | Error s -> Error s)
| Papp2 (o, e1, e2) ->
  (match alloc_e pd pmap rmap e1 with
   | Ok x ->
     (match alloc_e pd pmap rmap e2 with
      | Ok x0 -> Ok (Papp2 (o, x, x0))
      | Error s -> Error s)
   | Error s -> Error s)
| PappN (o, es) ->
  (match mapM (alloc_e pd pmap rmap) es with
   | Ok x -> Ok (PappN (o, x))
   | Error s -> Error s)
| Pif (t0, e0, e1, e2) ->
  (match alloc_e pd pmap rmap e0 with
   | Ok x ->
     (match alloc_e pd pmap rmap e1 with
      | Ok x0 ->
        (match alloc_e pd pmap rmap e2 with
         | Ok x1 -> Ok (Pif (t0, x, x0, x1))
         | Error s -> Error s)
      | Error s -> Error s)
   | Error s -> Error s)
| _ -> Ok e

(** val alloc_es :
    coq_PointerData -> pos_map -> Region.region_map -> pexpr list ->
    (pp_error_loc, pexpr list) result **)

let alloc_es pd pmap rmap =
  mapM (alloc_e pd pmap rmap)

(** val sub_region_direct :
    slot -> wsize -> Equality.sort -> zone -> sub_region **)

let sub_region_direct x align sc z =
  let r = { r_slot = x; r_align = align; r_writable =
    (negb (eq_op v_scope_eqType sc (Obj.magic Sglob))) }
  in
  { sr_region = r; sr_zone = z }

(** val sub_region_stack : slot -> wsize -> zone -> sub_region **)

let sub_region_stack x align z =
  sub_region_direct x align (Obj.magic Slocal) z

(** val sub_region_pk :
    var_i -> ptr_kind -> (pp_error_loc, sub_region) result **)

let sub_region_pk x = function
| Pdirect (x0, _, align, sub0, v) ->
  (match v with
   | Slocal -> Ok (sub_region_stack x0 align sub0)
   | Sglob ->
     Error
       (E.stk_ierror x
         (pp_box ((PPEvar x.v_var) :: ((PPEstring
           ('i'::('s'::(' '::('n'::('o'::('t'::(' '::('i'::('n'::(' '::('t'::('h'::('e'::(' '::('s'::('t'::('a'::('c'::('k'::[])))))))))))))))))))) :: [])))))
| _ ->
  Error
    (E.stk_ierror x
      (pp_box ((PPEvar x.v_var) :: ((PPEstring
        ('i'::('s'::(' '::('n'::('o'::('t'::(' '::('i'::('n'::(' '::('t'::('h'::('e'::(' '::('s'::('t'::('a'::('c'::('k'::[])))))))))))))))))))) :: []))))

(** val alloc_lval :
    coq_PointerData -> pos_map -> Region.region_map -> lval -> stype ->
    (pp_error_loc, Region.region_map * lval) result **)

let alloc_lval pd pmap rmap r ty =
  match r with
  | Lnone (_, _) -> Ok (rmap, r)
  | Lvar x ->
    (match get_local pmap x.v_var with
     | Some pk ->
       (match is_word_type (Var.vtype x.v_var) with
        | Some ws ->
          if subtype (Coq_sword ws) ty
          then (match mk_addr_ptr pd pmap x AAdirect ws pk (Pconst Z0) with
                | Ok x0 ->
                  (match sub_region_pk x pk with
                   | Ok x1 ->
                     let r0 = Lmem (ws, (fst x0), (snd x0)) in
                     (match Region.set_word rmap x x1 ws with
                      | Ok x2 -> Ok (x2, r0)
                      | Error s -> Error s)
                   | Error s -> Error s)
                | Error s -> Error s)
          else Error
                 (E.stk_ierror_basic x
                   ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('t'::('y'::('p'::('e'::(' '::('f'::('o'::('r'::(' '::('a'::('s'::('s'::('i'::('g'::('n'::('m'::('e'::('n'::('t'::[]))))))))))))))))))))))))))))
        | None ->
          Error
            (E.stk_ierror_basic x
              ('n'::('o'::('t'::(' '::('a'::(' '::('w'::('o'::('r'::('d'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('i'::('n'::(' '::('a'::('s'::('s'::('i'::('g'::('n'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))))))))))))))
     | None ->
       (match check_diff pmap x with
        | Ok _ -> Ok (rmap, r)
        | Error s -> Error s))
  | Lmem (ws, x, e1) ->
    (match check_var pmap x with
     | Ok _ ->
       (match check_diff pmap x with
        | Ok _ ->
          (match alloc_e pd pmap rmap e1 with
           | Ok x0 -> Ok (rmap, (Lmem (ws, x, x0)))
           | Error s -> Error s)
        | Error s -> Error s)
     | Error s -> Error s)
  | Laset (aa, ws, x, e1) ->
    (match alloc_e pd pmap rmap e1 with
     | Ok x0 ->
       (match get_local pmap x.v_var with
        | Some pk ->
          let ofs = mk_ofsi aa ws x0 in
          (match Region.set_arr_word rmap x ofs ws with
           | Ok x1 ->
             (match mk_addr_ptr pd pmap x aa ws pk x0 with
              | Ok x2 -> let r0 = Lmem (ws, (fst x2), (snd x2)) in Ok (x1, r0)
              | Error s -> Error s)
           | Error s -> Error s)
        | None ->
          (match check_diff pmap x with
           | Ok _ -> Ok (rmap, (Laset (aa, ws, x, x0)))
           | Error s -> Error s))
     | Error s -> Error s)
  | Lasub (_, _, _, x, _) ->
    Error (E.stk_ierror_basic x ('L'::('a'::('s'::('u'::('b'::[]))))))

(** val nop : 'a1 asmOp -> 'a1 instr_r **)

let nop asmop =
  Copn ([], AT_none, (sopn_nop asmop), [])

(** val is_nop :
    coq_PointerData -> (((slot * wsize) * zone) * Var.var) option ->
    Region.region_map -> Var.var -> sub_region -> bool **)

let is_nop pd is_spilling rmap x sry =
  match is_spilling with
  | Some y ->
    let (y0, f) = y in
    let (y1, z) = y0 in
    let (s, ws) = y1 in
    (match Mvar.get rmap.Region.var_region (Obj.magic x) with
     | Some srx ->
       (&&) (eq_op sub_region_eqType (Obj.magic srx) (Obj.magic sry))
         (Region.check_stack_ptr pd rmap.Region.region_var s ws z f)
     | None -> false)
  | None -> false

(** val get_addr :
    coq_PointerData -> 'a1 asmOp -> 'a1 stack_alloc_params ->
    (((slot * wsize) * zone) * Var.var) option -> Region.region_map ->
    Var.var -> lval -> assgn_tag -> sub_region -> vptr_kind -> pexpr -> coq_Z
    -> Region.region_map * 'a1 instr_r option **)

let get_addr pd asmop saparams is_spilling rmap x dx tag sry vpk y ofs =
  let ir =
    if is_nop pd is_spilling rmap x sry
    then Some (nop asmop)
    else saparams.sap_mov_ofs dx tag vpk y ofs
  in
  let rmap0 = Region.set_move rmap x sry in (rmap0, ir)

(** val get_ofs_sub :
    arr_access -> wsize -> var_i -> pexpr -> (pp_error_loc, coq_Z) result **)

let get_ofs_sub aa ws x e1 =
  match mk_ofsi aa ws e1 with
  | Some ofs -> Ok ofs
  | None ->
    Error
      (E.stk_ierror_basic x
        ('c'::('a'::('n'::('n'::('o'::('t'::(' '::('t'::('a'::('k'::('e'::('/'::('s'::('e'::('t'::(' '::('a'::(' '::('s'::('u'::('b'::('a'::('r'::('r'::('a'::('y'::(' '::('o'::('n'::(' '::('a'::(' '::('u'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('s'::('t'::('a'::('r'::('t'::('i'::('n'::('g'::(' '::('p'::('o'::('s'::('i'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val get_Lvar_sub :
    lval -> (pp_error_loc, var_i * (coq_Z * coq_Z) option) result **)

let get_Lvar_sub = function
| Lvar x -> Ok (x, None)
| Lasub (aa, ws, len, x, e1) ->
  (match get_ofs_sub aa ws x e1 with
   | Ok x0 -> Ok (x, (Some (x0, (arr_size ws len))))
   | Error s -> Error s)
| _ ->
  Error
    (E.stk_ierror_no_var
      ('g'::('e'::('t'::('_'::('L'::('v'::('a'::('r'::('_'::('s'::('u'::('b'::(':'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::('/'::('s'::('u'::('b'::('a'::('r'::('r'::('a'::('y'::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))))))))))))

(** val get_Pvar_sub :
    pexpr -> (pp_error_loc, gvar * (coq_Z * coq_Z) option) result **)

let get_Pvar_sub = function
| Pvar x -> Ok (x, None)
| Psub (aa, ws, len, x, e1) ->
  (match get_ofs_sub aa ws x.gv e1 with
   | Ok x0 -> Ok (x, (Some (x0, (arr_size ws len))))
   | Error s -> Error s)
| _ ->
  Error
    (E.stk_ierror_no_var
      ('g'::('e'::('t'::('_'::('P'::('v'::('a'::('r'::('_'::('s'::('u'::('b'::(':'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::('/'::('s'::('u'::('b'::('a'::('r'::('r'::('a'::('y'::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))))))))))))

(** val is_stack_ptr :
    vptr_kind -> ((((Var.var * coq_Z) * wsize) * zone) * Var.var) option **)

let is_stack_ptr = function
| VKglob _ -> None
| VKptr p ->
  (match p with
   | Pstkptr (s, ofs, ws, z, f) -> Some ((((s, ofs), ws), z), f)
   | _ -> None)

(** val mk_addr_pexpr :
    coq_PointerData -> pos_map -> ByteSet.t Mvar.t Mr.t -> var_i -> vptr_kind
    -> (pp_error_loc, pexpr * coq_Z) result **)

let mk_addr_pexpr pd pmap rmap x vpk =
  match is_stack_ptr vpk with
  | Some p ->
    let (p0, f) = p in
    let (p1, z) = p0 in
    let (p2, ws) = p1 in
    let (s, ofs) = p2 in
    if Region.check_stack_ptr pd rmap s ws z f
    then Ok ((Pload ((coq_Uptr pd), (with_var x pmap.vrsp),
           (cast_const pd (Z.add ofs z.z_ofs)))), Z0)
    else let s0 =
           E.stk_error x
             (pp_box ((PPEstring
               ('t'::('h'::('e'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::[])))))))))))))))))) :: ((PPEvar
               x.v_var) :: ((PPEstring
               ('i'::('s'::(' '::('n'::('o'::(' '::('l'::('o'::('n'::('g'::('e'::('r'::(' '::('v'::('a'::('l'::('i'::('d'::[]))))))))))))))))))) :: []))))
         in
         Error s0
  | None ->
    (match addr_from_vpk pmap x vpk with
     | Ok x0 -> Ok ((coq_Plvar (fst x0)), (snd x0))
     | Error s -> Error s)

(** val alloc_array_move :
    coq_PointerData -> 'a1 asmOp -> 'a1 stack_alloc_params -> pos_map ->
    Region.region_map -> lval -> assgn_tag -> pexpr -> (pp_error_loc,
    Region.region_map * 'a1 instr_r) result **)

let alloc_array_move pd asmop saparams pmap rmap r tag e =
  match get_Lvar_sub r with
  | Ok x ->
    (match get_Pvar_sub e with
     | Ok x0 ->
       let (x1, subx) = x in
       let (y, suby) = x0 in
       (match let vy = y.gv in
              (match get_var_kind pmap y with
               | Ok x2 ->
                 let (ofs, len) =
                   match suby with
                   | Some p -> p
                   | None -> (Z0, (size_of (Var.vtype vy.v_var)))
                 in
                 (match x2 with
                  | Some vpk ->
                    (match check_vpk rmap vy vpk (Some ofs) len with
                     | Ok x3 ->
                       let sry = snd x3 in
                       (match mk_addr_pexpr pd pmap rmap.Region.region_var vy
                                vpk with
                        | Ok x4 ->
                          Ok (((sry, vpk), (fst x4)), (Z.add (snd x4) ofs))
                        | Error s -> Error s)
                     | Error s -> Error s)
                  | None ->
                    Error
                      (E.stk_ierror_basic vy
                        ('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::(' '::('a'::('r'::('r'::('a'::('y'::(' '::('r'::('e'::('m'::('a'::('i'::('n'::('s'::[]))))))))))))))))))))))))
               | Error s -> Error s) with
        | Ok x2 ->
          let (y0, ofs) = x2 in
          let (y1, ey) = y0 in
          let (sry, vpk) = y1 in
          (match subx with
           | Some y2 ->
             let (ofs0, len) = y2 in
             (match get_local pmap x1.v_var with
              | Some _ ->
                (match Region.set_arr_sub rmap x1 ofs0 len (Obj.magic sry) with
                 | Ok x3 -> Ok (x3, (nop asmop))
                 | Error s -> Error s)
              | None ->
                Error
                  (E.stk_ierror_basic x1
                    ('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::(' '::('a'::('r'::('r'::('a'::('y'::(' '::('r'::('e'::('m'::('a'::('i'::('n'::('s'::[]))))))))))))))))))))))))
           | None ->
             (match get_local pmap x1.v_var with
              | Some pk ->
                (match pk with
                 | Pdirect (s, _, ws, zx, sc) ->
                   let sr = sub_region_direct s ws (Obj.magic sc) zx in
                   if eq_op sub_region_eqType (Obj.magic sr) (Obj.magic sry)
                   then let rmap0 = Region.set_move rmap x1.v_var sry in
                        Ok (rmap0, (nop asmop))
                   else let s0 =
                          E.stk_ierror x1
                            (pp_box ((PPEstring
                              ('t'::('h'::('e'::(' '::('a'::('s'::('s'::('i'::('g'::('n'::('m'::('e'::('n'::('t'::(' '::('t'::('o'::(' '::('a'::('r'::('r'::('a'::('y'::[])))))))))))))))))))))))) :: ((PPEvar
                              x1.v_var) :: ((PPEstring
                              ('c'::('a'::('n'::('n'::('o'::('t'::(' '::('b'::('e'::(' '::('t'::('u'::('r'::('n'::('e'::('d'::(' '::('i'::('n'::('t'::('o'::(' '::('a'::(' '::('n'::('o'::('p'::(':'::(' '::('s'::('o'::('u'::('r'::('c'::('e'::(' '::('a'::('n'::('d'::(' '::('d'::('e'::('s'::('t'::('i'::('n'::('a'::('t'::('i'::('o'::('n'::(' '::('r'::('e'::('g'::('i'::('o'::('n'::('s'::(' '::('a'::('r'::('e'::(' '::('n'::('o'::('t'::(' '::('e'::('q'::('u'::('a'::('l'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []))))
                        in
                        Error s0
                 | Pregptr p ->
                   let (rmap0, oir) =
                     get_addr pd asmop saparams None rmap x1.v_var (Lvar
                       (with_var x1 p)) tag sry vpk ey ofs
                   in
                   (match oir with
                    | Some ir -> Ok (rmap0, ir)
                    | None ->
                      let err_pp =
                        pp_box ((PPEstring
                          ('c'::('a'::('n'::('n'::('o'::('t'::(' '::('c'::('o'::('m'::('p'::('u'::('t'::('e'::(' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::[]))))))))))))))))))))))) :: ((PPEvar
                          x1.v_var) :: []))
                      in
                      Error (E.stk_error x1 err_pp))
                 | Pstkptr (slot0, ofsx, ws, z, x') ->
                   let is_spilling = Some (((slot0, ws), z), x') in
                   let dx_ofs = cast_const pd (Z.add ofsx z.z_ofs) in
                   let dx = Lmem ((coq_Uptr pd), (with_var x1 pmap.vrsp),
                     dx_ofs)
                   in
                   let (rmap0, oir) =
                     get_addr pd asmop saparams is_spilling rmap x1.v_var dx
                       tag sry vpk ey ofs
                   in
                   (match oir with
                    | Some ir ->
                      Ok ((Region.set_stack_ptr pd rmap0 slot0 ws z x'), ir)
                    | None ->
                      let err_pp =
                        pp_box ((PPEstring
                          ('c'::('a'::('n'::('n'::('o'::('t'::(' '::('c'::('o'::('m'::('p'::('u'::('t'::('e'::(' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::[]))))))))))))))))))))))) :: ((PPEvar
                          x1.v_var) :: []))
                      in
                      Error (E.stk_error x1 err_pp)))
              | None ->
                Error
                  (E.stk_ierror_basic x1
                    ('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::(' '::('a'::('r'::('r'::('a'::('y'::(' '::('r'::('e'::('m'::('a'::('i'::('n'::('s'::[])))))))))))))))))))))))))
        | Error s -> Error s)
     | Error s -> Error s)
  | Error s -> Error s

(** val is_protect_ptr_fail :
    'a1 asmOp -> lval list -> 'a1 sopn -> pexpr list ->
    ((lval * pexpr) * pexpr) option **)

let is_protect_ptr_fail _ rs o es =
  match o with
  | Oslh s ->
    (match s with
     | SLHprotect_ptr_fail _ ->
       (match rs with
        | [] -> None
        | r :: l ->
          (match l with
           | [] ->
             (match es with
              | [] -> None
              | e :: l0 ->
                (match l0 with
                 | [] -> None
                 | msf :: l1 ->
                   (match l1 with
                    | [] -> Some ((r, e), msf)
                    | _ :: _ -> None)))
           | _ :: _ -> None))
     | _ -> None)
  | _ -> None

(** val lower_protect_ptr_fail :
    coq_PointerData -> 'a1 asmOp -> 'a1 sh_params -> instr_info -> lval list
    -> assgn_tag -> pexpr list -> 'a1 instr_r cexec **)

let lower_protect_ptr_fail pd asmop shparams ii lvs t0 es =
  lower_slho asmop shparams ii lvs t0 (SLHprotect (coq_Uptr pd)) es

(** val alloc_protect_ptr :
    coq_PointerData -> 'a1 asmOp -> 'a1 sh_params -> pos_map ->
    Region.region_map -> instr_info -> lval -> assgn_tag -> pexpr -> pexpr ->
    (pp_error_loc, Region.region_map * 'a1 instr_r) result **)

let alloc_protect_ptr pd asmop shparams pmap rmap ii r t0 e msf =
  match get_Lvar_sub r with
  | Ok x ->
    (match get_Pvar_sub e with
     | Ok x0 ->
       let (x1, subx) = x in
       let (y, suby) = x0 in
       (match let vy = y.gv in
              (match get_var_kind pmap y with
               | Ok x2 ->
                 let ofs = Z0 in
                 (match suby with
                  | Some _ ->
                    let s =
                      E.stk_error_no_var
                        ('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('p'::('r'::('o'::('t'::('e'::('c'::('t'::('_'::('p'::('t'::('r'::(' '::('c'::('a'::('n'::('n'::('o'::('t'::(' '::('b'::('e'::(' '::('a'::(' '::('s'::('u'::('b'::(' '::('a'::('r'::('r'::('a'::('y'::[])))))))))))))))))))))))))))))))))))))))))))))
                    in
                    Error s
                  | None ->
                    let x3 = size_of (Var.vtype vy.v_var) in
                    (match x2 with
                     | Some vpk ->
                       (match vpk with
                        | VKglob _ ->
                          let s =
                            E.stk_error_no_var
                              ('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('p'::('r'::('o'::('t'::('e'::('c'::('t'::('_'::('p'::('t'::('r'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('a'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::[])))))))))))))))))))))))))))))))))))))))))))
                          in
                          Error s
                        | VKptr p ->
                          (match p with
                           | Pregptr _ ->
                             (match r with
                              | Lvar _ ->
                                (match check_vpk rmap vy vpk (Some ofs) x3 with
                                 | Ok x4 ->
                                   let sry = snd x4 in
                                   (match mk_addr_pexpr pd pmap
                                            rmap.Region.region_var vy vpk with
                                    | Ok x5 ->
                                      let (e0, _) = x5 in Ok ((sry, vpk), e0)
                                    | Error s -> Error s)
                                 | Error s -> Error s)
                              | _ ->
                                let s =
                                  E.stk_error_no_var
                                    ('d'::('e'::('s'::('t'::('i'::('n'::('a'::('t'::('i'::('o'::('n'::(' '::('o'::('f'::(' '::('p'::('r'::('o'::('t'::('e'::('c'::('t'::('_'::('p'::('t'::('r'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('a'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::[]))))))))))))))))))))))))))))))))))))))))))))))
                                in
                                Error s)
                           | _ ->
                             let s =
                               E.stk_error_no_var
                                 ('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('p'::('r'::('o'::('t'::('e'::('c'::('t'::('_'::('p'::('t'::('r'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('a'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::[])))))))))))))))))))))))))))))))))))))))))))
                             in
                             Error s))
                     | None ->
                       Error
                         (E.stk_error_no_var
                           ('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('p'::('r'::('o'::('t'::('e'::('c'::('t'::('_'::('p'::('t'::('r'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('a'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::[]))))))))))))))))))))))))))))))))))))))))))))))
               | Error s -> Error s) with
        | Ok x2 ->
          let (y0, ey) = x2 in
          let (sry, _) = y0 in
          (match subx with
           | Some _ ->
             Error
               (E.stk_error_no_var
                 ('c'::('a'::('n'::('n'::('o'::('t'::(' '::('a'::('s'::('s'::('i'::('g'::('n'::(' '::('p'::('r'::('o'::('t'::('e'::('c'::('t'::('_'::('p'::('t'::('r'::(' '::('i'::('n'::(' '::('a'::(' '::('s'::('u'::('b'::(' '::('a'::('r'::('r'::('a'::('y'::[])))))))))))))))))))))))))))))))))))))))))
           | None ->
             (match get_local pmap x1.v_var with
              | Some pk ->
                (match pk with
                 | Pregptr px ->
                   let dx = Lvar (with_var x1 px) in
                   (match add_iinfo ii (alloc_e pd pmap rmap msf) with
                    | Ok x3 ->
                      (match lower_protect_ptr_fail pd asmop shparams ii
                               (dx :: []) t0 (ey :: (x3 :: [])) with
                       | Ok x4 ->
                         let rmap0 = Region.set_move rmap x1.v_var sry in
                         Ok (rmap0, x4)
                       | Error s -> Error s)
                    | Error s -> Error s)
                 | _ ->
                   Error
                     (E.stk_error_no_var
                       ('o'::('n'::('l'::('y'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('c'::('a'::('n'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::(' '::('t'::('h'::('e'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(' '::('o'::('f'::(' '::('p'::('r'::('o'::('t'::('e'::('c'::('t'::('_'::('p'::('t'::('r'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
              | None ->
                Error
                  (E.stk_error_no_var
                    ('o'::('n'::('l'::('y'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('c'::('a'::('n'::(' '::('r'::('e'::('c'::('e'::('i'::('v'::('e'::(' '::('t'::('h'::('e'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(' '::('o'::('f'::(' '::('p'::('r'::('o'::('t'::('e'::('c'::('t'::('_'::('p'::('t'::('r'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))
        | Error s -> Error s)
     | Error s -> Error s)
  | Error s -> Error s

(** val alloc_array_move_init :
    coq_PointerData -> 'a1 asmOp -> 'a1 stack_alloc_params -> pos_map ->
    Region.region_map -> lval -> assgn_tag -> pexpr -> (pp_error_loc,
    Region.region_map * 'a1 instr_r) result **)

let alloc_array_move_init pd asmop saparams pmap rmap r tag e =
  if is_array_init e
  then (match get_Lvar_sub r with
        | Ok x ->
          let (x0, subx) = x in
          let (ofs, len) =
            match subx with
            | Some p -> p
            | None -> (Z0, (size_of (Var.vtype x0.v_var)))
          in
          (match match get_local pmap x0.v_var with
                 | Some pk ->
                   (match pk with
                    | Pdirect (x', _, ws, z, sc) ->
                      (match sc with
                       | Slocal -> Ok (sub_region_stack x' ws z)
                       | Sglob ->
                         Error
                           (E.stk_error x0
                             (pp_box ((PPEstring
                               ('c'::('a'::('n'::('n'::('o'::('t'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::(' '::('g'::('l'::('o'::('b'::(' '::('a'::('r'::('r'::('a'::('y'::[]))))))))))))))))))))))))))))) :: ((PPEvar
                               x0.v_var) :: [])))))
                    | _ -> Region.get_sub_region rmap x0)
                 | None ->
                   Error
                     (E.stk_ierror_basic x0
                       ('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::(' '::('a'::('r'::('r'::('a'::('y'::(' '::('r'::('e'::('m'::('a'::('i'::('n'::('s'::[]))))))))))))))))))))))) with
           | Ok x1 ->
             let sr = Region.sub_region_at_ofs x1 (Some ofs) len in
             let rmap0 = Region.set_move_sub rmap x0.v_var sr in
             Ok (rmap0, (nop asmop))
           | Error s -> Error s)
        | Error s -> Error s)
  else alloc_array_move pd asmop saparams pmap rmap r tag e

(** val bad_lval_number : pp_error_loc **)

let bad_lval_number =
  E.stk_ierror_no_var
    ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('o'::('f'::(' '::('l'::('v'::('a'::('l'::[]))))))))))))))))))))))

(** val alloc_lvals :
    coq_PointerData -> pos_map -> Region.region_map -> lval list -> stype
    list -> (pp_error_loc, Region.region_map * lval list) result **)

let alloc_lvals pd pmap rmap rs tys =
  fmapM2 bad_lval_number (alloc_lval pd pmap) rmap rs tys

(** val loop2 :
    'a1 asmOp -> instr_info -> (Region.region_map ->
    ((Region.region_map * Region.region_map) * (pexpr * ('a1 instr list
    list * 'a1 instr list list))) cexec) -> nat -> Region.region_map ->
    (pp_error_loc, Region.region_map * (pexpr * ('a1 instr list list * 'a1
    instr list list))) result **)

let rec loop2 asmop ii check_c2 n m =
  match n with
  | O ->
    Error
      (pp_at_ii ii
        (E.stk_ierror_no_var ('l'::('o'::('o'::('p'::('2'::[])))))))
  | S n0 ->
    (match check_c2 m with
     | Ok x ->
       if Region.incl m (snd (fst x))
       then Ok ((fst (fst x)), (snd x))
       else loop2 asmop ii check_c2 n0 (Region.merge m (snd (fst x)))
     | Error s -> Error s)

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

(** val sao_frame_size : stk_alloc_oracle_t -> coq_Z **)

let sao_frame_size sao =
  if is_RAnone sao.sao_return_address
  then Z.add sao.sao_size sao.sao_extra_size
  else round_ws sao.sao_align (Z.add sao.sao_size sao.sao_extra_size)

(** val get_Pvar : pexpr -> (pp_error_loc, gvar) result **)

let get_Pvar = function
| Pvar x -> Ok x
| _ ->
  Error
    (E.stk_ierror_no_var
      ('g'::('e'::('t'::('_'::('P'::('v'::('a'::('r'::(':'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))

(** val set_clear_bytes :
    ByteSet.t Mvar.t Mr.t -> sub_region -> coq_Z option -> coq_Z -> ByteSet.t
    Mvar.t Mr.Map.t **)

let set_clear_bytes rv sr ofs len =
  let z = sr.sr_zone in
  let z1 = Region.sub_zone_at_ofs z ofs len in
  let i = Region.interval_of_zone z1 in
  let bm = Region.get_bytes_map sr.sr_region rv in
  let bm0 = Region.clear_bytes_map i bm in
  Mr.set rv (Obj.magic sr.sr_region) bm0

(** val set_clear_pure :
    Region.region_map -> sub_region -> coq_Z option -> coq_Z ->
    Region.region_map **)

let set_clear_pure rmap sr ofs len =
  { Region.var_region = rmap.Region.var_region; Region.region_var =
    (set_clear_bytes rmap.Region.region_var sr ofs len) }

(** val set_clear :
    Region.region_map -> var_i -> sub_region -> coq_Z option -> coq_Z ->
    (pp_error_loc, Region.region_map) result **)

let set_clear rmap x sr ofs len =
  match writable x sr.sr_region with
  | Ok _ -> Ok (set_clear_pure rmap sr ofs len)
  | Error s -> Error s

(** val alloc_call_arg_aux :
    pos_map -> Region.region_map -> Region.region_map -> param_info option ->
    pexpr -> (pp_error_loc, Region.region_map * ((bool * sub_region)
    option * pexpr)) result **)

let alloc_call_arg_aux pmap rmap0 rmap sao_param e =
  match get_Pvar e with
  | Ok x ->
    if negb (is_glob x)
    then let xv = x.gv in
         (match sao_param with
          | Some pi ->
            (match get_local pmap xv.v_var with
             | Some p0 ->
               (match p0 with
                | Pregptr p ->
                  (match Region.check_valid rmap0 xv (Some Z0)
                           (size_of (Var.vtype xv.v_var)) with
                   | Ok x0 ->
                     let sr = fst x0 in
                     (match if pi.pp_writable
                            then set_clear rmap xv sr (Some Z0)
                                   (size_of (Var.vtype xv.v_var))
                            else Ok rmap with
                      | Ok x1 ->
                        (match check_align xv sr pi.pp_align with
                         | Ok _ ->
                           Ok (x1, ((Some (pi.pp_writable, sr)), (Pvar
                             (mk_lvar (with_var xv p)))))
                         | Error s -> Error s)
                      | Error s -> Error s)
                   | Error s -> Error s)
                | _ ->
                  Error
                    (E.stk_ierror_basic xv
                      ('t'::('h'::('e'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('a'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::[]))))))))))))))))))))))))))))))))))
             | None ->
               Error
                 (E.stk_ierror_basic xv
                   ('t'::('h'::('e'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('a'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::[]))))))))))))))))))))))))))))))))))
          | None ->
            (match get_local pmap xv.v_var with
             | Some _ ->
               Error
                 (E.stk_ierror_basic xv
                   ('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('g'::[])))))))))))))))))))
             | None ->
               (match check_diff pmap xv with
                | Ok _ -> Ok (rmap, (None, (Pvar x)))
                | Error s -> Error s)))
    else let s =
           E.stk_ierror_basic x.gv
             ('g'::('l'::('o'::('b'::('a'::('l'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('i'::('n'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('a'::(' '::('c'::('a'::('l'::('l'::[])))))))))))))))))))))))))))))))))))))
         in
         Error s
  | Error s -> Error s

(** val alloc_call_args_aux :
    pos_map -> Region.region_map -> param_info option list -> pexpr list ->
    (pp_error_loc, Region.region_map * ((bool * sub_region) option * pexpr)
    list) result **)

let alloc_call_args_aux pmap rmap sao_params0 es =
  fmapM2
    (E.stk_ierror_no_var
      ('b'::('a'::('d'::(' '::('p'::('a'::('r'::('a'::('m'::('s'::(' '::('i'::('n'::('f'::('o'::[]))))))))))))))))
    (alloc_call_arg_aux pmap rmap) rmap sao_params0 es

(** val disj_sub_regions : sub_region -> sub_region -> bool **)

let disj_sub_regions sr1 sr2 =
  (||) (negb (region_same sr1.sr_region sr2.sr_region))
    (disjoint_zones sr1.sr_zone sr2.sr_zone)

(** val check_all_disj :
    sub_region list -> sub_region list -> ((bool * sub_region)
    option * pexpr) list -> bool **)

let rec check_all_disj notwritables writables = function
| [] -> true
| p :: srs0 ->
  let (o, _) = p in
  (match o with
   | Some p1 ->
     let (writable0, sr) = p1 in
     if all (disj_sub_regions sr) writables
     then if writable0
          then if all (disj_sub_regions sr) notwritables
               then check_all_disj notwritables (sr :: writables) srs0
               else false
          else check_all_disj (sr :: notwritables) writables srs0
     else false
   | None -> check_all_disj notwritables writables srs0)

(** val alloc_call_args :
    pos_map -> Region.region_map -> param_info option list -> pexpr list ->
    (pp_error_loc, Region.region_map * ((bool * sub_region) option * pexpr)
    list) result **)

let alloc_call_args pmap rmap sao_params0 es =
  match alloc_call_args_aux pmap rmap sao_params0 es with
  | Ok x ->
    if check_all_disj [] [] (snd x)
    then Ok x
    else let s =
           E.stk_error_no_var
             ('s'::('o'::('m'::('e'::(' '::('w'::('r'::('i'::('t'::('a'::('b'::('l'::('e'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('a'::('r'::('e'::(' '::('n'::('o'::('t'::(' '::('d'::('i'::('s'::('j'::('o'::('i'::('n'::('t'::('s'::[])))))))))))))))))))))))))))))))))))))))
         in
         Error s
  | Error s -> Error s

(** val check_lval_reg_call :
    pos_map -> lval -> (pp_error_loc, unit) result **)

let check_lval_reg_call pmap = function
| Lnone (_, _) -> Ok ()
| Lvar x ->
  (match get_local pmap x.v_var with
   | Some _ ->
     Error
       (E.stk_ierror_basic x
         ('c'::('a'::('l'::('l'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('s'::('t'::('o'::('r'::('e'::('d'::(' '::('i'::('n'::(' '::('r'::('e'::('g'::[]))))))))))))))))))))))))))))))))))))
   | None -> (match check_diff pmap x with
              | Ok _ -> Ok ()
              | Error s -> Error s))
| Lmem (_, x, _) ->
  Error
    (E.stk_ierror_basic x
      ('c'::('a'::('l'::('l'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('s'::('t'::('o'::('r'::('e'::('d'::(' '::('i'::('n'::(' '::('r'::('e'::('g'::[]))))))))))))))))))))))))))))))))))))
| Laset (_, _, x, _) ->
  Error
    (E.stk_ierror_basic x
      ('a'::('r'::('r'::('a'::('y'::(' '::('a'::('s'::('s'::('i'::('g'::('n'::('e'::('m'::('e'::('n'::('t'::(' '::('i'::('n'::(' '::('l'::('v'::('a'::('l'::(' '::('o'::('f'::(' '::('a'::(' '::('c'::('a'::('l'::('l'::[]))))))))))))))))))))))))))))))))))))
| Lasub (_, _, _, x, _) ->
  Error
    (E.stk_ierror_basic x
      ('s'::('u'::('b'::('-'::('a'::('r'::('r'::('a'::('y'::(' '::('a'::('s'::('s'::('i'::('g'::('n'::('e'::('m'::('e'::('n'::('t'::(' '::('i'::('n'::(' '::('l'::('v'::('a'::('l'::(' '::('o'::('f'::(' '::('a'::(' '::('c'::('a'::('l'::('l'::[]))))))))))))))))))))))))))))))))))))))))

(** val get_regptr : pos_map -> var_i -> (pp_error_loc, var_i) result **)

let get_regptr pmap x =
  match get_local pmap x.v_var with
  | Some p0 ->
    (match p0 with
     | Pregptr p -> Ok (with_var x p)
     | _ ->
       Error
         (E.stk_ierror x
           (pp_box ((PPEstring
             ('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[]))))))))) :: ((PPEvar
             x.v_var) :: ((PPEstring
             ('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('a'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::[])))))))))))))))))))) :: []))))))
  | None ->
    Error
      (E.stk_ierror x
        (pp_box ((PPEstring
          ('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[]))))))))) :: ((PPEvar
          x.v_var) :: ((PPEstring
          ('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('a'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::[])))))))))))))))))))) :: [])))))

(** val alloc_lval_call :
    coq_PointerData -> pos_map -> ((bool * sub_region) option * pexpr) list
    -> Region.region_map -> lval -> nat option -> (pp_error_loc,
    Region.region_map * lval) result **)

let alloc_lval_call pd pmap srs rmap r = function
| Some i0 ->
  let (o, _) = nth (None, (Pconst Z0)) srs i0 in
  (match o with
   | Some p0 ->
     let (_, sr) = p0 in
     (match r with
      | Lnone (i1, _) -> Ok (rmap, (Lnone (i1, (Coq_sword (coq_Uptr pd)))))
      | Lvar x ->
        (match get_regptr pmap x with
         | Ok x0 ->
           (match Region.set_arr_call rmap x sr with
            | Ok x1 -> Ok (x1, (Lvar x0))
            | Error s -> Error s)
         | Error s -> Error s)
      | Lmem (_, x, _) ->
        Error
          (E.stk_ierror_basic x
            ('c'::('a'::('l'::('l'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('s'::('t'::('o'::('r'::('e'::('d'::(' '::('i'::('n'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::[]))))))))))))))))))))))))))))))))))))))))
      | Laset (_, _, x, _) ->
        Error
          (E.stk_ierror_basic x
            ('a'::('r'::('r'::('a'::('y'::(' '::('a'::('s'::('s'::('i'::('g'::('n'::('e'::('m'::('e'::('n'::('t'::(' '::('i'::('n'::(' '::('l'::('v'::('a'::('l'::(' '::('o'::('f'::(' '::('a'::(' '::('c'::('a'::('l'::('l'::[]))))))))))))))))))))))))))))))))))))
      | Lasub (_, _, _, x, _) ->
        Error
          (E.stk_ierror_basic x
            ('s'::('u'::('b'::('-'::('a'::('r'::('r'::('a'::('y'::(' '::('a'::('s'::('s'::('i'::('g'::('n'::('e'::('m'::('e'::('n'::('t'::(' '::('i'::('n'::(' '::('l'::('v'::('a'::('l'::(' '::('o'::('f'::(' '::('a'::(' '::('c'::('a'::('l'::('l'::[])))))))))))))))))))))))))))))))))))))))))
   | None ->
     Error
       (E.stk_ierror_no_var
         ('a'::('l'::('l'::('o'::('c'::('_'::('l'::('v'::('a'::('l'::('_'::('c'::('a'::('l'::('l'::[])))))))))))))))))
| None ->
  (match check_lval_reg_call pmap r with
   | Ok _ -> Ok (rmap, r)
   | Error s -> Error s)

(** val alloc_call_res :
    coq_PointerData -> pos_map -> Region.region_map -> ((bool * sub_region)
    option * pexpr) list -> nat option list -> lval list -> (pp_error_loc,
    Region.region_map * lval list) result **)

let alloc_call_res pd pmap rmap srs ret_pos rs =
  fmapM2 bad_lval_number (alloc_lval_call pd pmap srs) rmap rs ret_pos

(** val alloc_call :
    coq_PointerData -> 'a1 asmOp -> bool -> pos_map -> (funname ->
    stk_alloc_oracle_t) -> stk_alloc_oracle_t -> Region.region_map -> lval
    list -> funname -> pexpr list -> (pp_error_loc, Region.region_map * 'a1
    instr_r) result **)

let alloc_call pd _ check pmap local_alloc sao_caller rmap rs fn es =
  let sao_callee = local_alloc fn in
  (match alloc_call_args pmap rmap sao_callee.sao_params es with
   | Ok x ->
     let (rmap0, es0) = x in
     (match alloc_call_res pd pmap rmap0 es0 sao_callee.sao_return rs with
      | Ok x0 ->
        (match assert_check check
                 (negb (is_RAnone sao_callee.sao_return_address))
                 (E.stk_ierror_no_var
                   ('c'::('a'::('n'::('n'::('o'::('t'::(' '::('c'::('a'::('l'::('l'::(' '::('e'::('x'::('p'::('o'::('r'::('t'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))) with
         | Ok _ ->
           (match let local_size = sao_frame_size sao_caller in
                  assert_check check
                    (Z.leb (Z.add local_size sao_callee.sao_max_size)
                      sao_caller.sao_max_size)
                    (E.stk_ierror_no_var
                      ('e'::('r'::('r'::('o'::('r'::(' '::('i'::('n'::(' '::('m'::('a'::('x'::(' '::('s'::('i'::('z'::('e'::(' '::('c'::('o'::('m'::('p'::('u'::('t'::('a'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))))) with
            | Ok _ ->
              (match assert_check check
                       (cmp_le wsize_cmp sao_callee.sao_align
                         sao_caller.sao_align)
                       (E.stk_ierror_no_var
                         ('n'::('o'::('n'::(' '::('a'::('l'::('i'::('g'::('n'::('e'::('d'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('c'::('a'::('l'::('l'::[])))))))))))))))))))))))))) with
               | Ok _ ->
                 let es1 = map snd es0 in
                 Ok ((fst x0), (Ccall ((snd x0), fn, es1)))
               | Error s -> Error s)
            | Error s -> Error s)
         | Error s -> Error s)
      | Error s -> Error s)
   | Error s -> Error s)

(** val alloc_syscall :
    coq_PointerData -> 'a1 asmOp -> 'a1 stack_alloc_params -> pos_map ->
    instr_info -> Region.region_map -> lval list ->
    BinNums.positive Syscall_t.syscall_t -> pexpr list -> (pp_error_loc,
    Region.region_map * 'a1 instr list) result **)

let alloc_syscall pd _ saparams pmap ii rmap rs o es =
  add_iinfo ii
    (let Syscall_t.RandomBytes len = o in
     if Z.ltb (Zpos len) (wbase (coq_Uptr pd))
     then (match rs with
           | [] ->
             Error
               (E.stk_ierror_no_var
                 ('r'::('a'::('n'::('d'::('o'::('m'::('b'::('y'::('t'::('e'::('s'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::[]))))))))))))))))))))))))))))))))))))
           | y :: l ->
             (match y with
              | Lvar x ->
                (match l with
                 | [] ->
                   (match es with
                    | [] ->
                      Error
                        (E.stk_ierror_no_var
                          ('r'::('a'::('n'::('d'::('o'::('m'::('b'::('y'::('t'::('e'::('s'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::[]))))))))))))))))))))))))))))))))))))
                    | y0 :: l0 ->
                      (match y0 with
                       | Pvar xe ->
                         (match l0 with
                          | [] ->
                            let xe0 = xe.gv in
                            let xlen = with_var xe0 pmap.vxlen in
                            (match get_regptr pmap xe0 with
                             | Ok x0 ->
                               (match get_regptr pmap x with
                                | Ok x1 ->
                                  (match Region.get_sub_region rmap xe0 with
                                   | Ok x2 ->
                                     (match Region.set_sub_region rmap x x2
                                              (Some Z0) (Zpos len) with
                                      | Ok x3 ->
                                        Ok (x3, ((MkI (ii,
                                          (saparams.sap_immediate xlen (Zpos
                                            len)))) :: ((MkI (ii, (Csyscall
                                          (((Lvar x1) :: []), o,
                                          ((coq_Plvar x0) :: ((coq_Plvar xlen) :: [])))))) :: [])))
                                      | Error s -> Error s)
                                   | Error s -> Error s)
                                | Error s -> Error s)
                             | Error s -> Error s)
                          | _ :: _ ->
                            Error
                              (E.stk_ierror_no_var
                                ('r'::('a'::('n'::('d'::('o'::('m'::('b'::('y'::('t'::('e'::('s'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::[])))))))))))))))))))))))))))))))))))))
                       | _ ->
                         Error
                           (E.stk_ierror_no_var
                             ('r'::('a'::('n'::('d'::('o'::('m'::('b'::('y'::('t'::('e'::('s'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::[]))))))))))))))))))))))))))))))))))))))
                 | _ :: _ ->
                   Error
                     (E.stk_ierror_no_var
                       ('r'::('a'::('n'::('d'::('o'::('m'::('b'::('y'::('t'::('e'::('s'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::[])))))))))))))))))))))))))))))))))))))
              | _ ->
                Error
                  (E.stk_ierror_no_var
                    ('r'::('a'::('n'::('d'::('o'::('m'::('b'::('y'::('t'::('e'::('s'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::[]))))))))))))))))))))))))))))))))))))))
     else let s =
            E.stk_error_no_var
              ('r'::('a'::('n'::('d'::('o'::('m'::('b'::('y'::('t'::('e'::('s'::(':'::(' '::('t'::('h'::('e'::(' '::('r'::('e'::('q'::('u'::('e'::('s'::('t'::('e'::('d'::(' '::('s'::('i'::('z'::('e'::(' '::('i'::('s'::(' '::('t'::('o'::('o'::(' '::('l'::('a'::('r'::('g'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))
          in
          Error s)

(** val is_swap_array : 'a1 asmOp -> 'a1 sopn -> bool **)

let is_swap_array _ = function
| Opseudo_op p -> (match p with
                   | Oswap ty -> is_sarr ty
                   | _ -> false)
| _ -> false

(** val alloc_array_swap :
    'a1 asmOp -> 'a1 stack_alloc_params -> pos_map -> Region.region_map ->
    lval list -> assgn_tag -> pexpr list -> (pp_error_loc,
    Region.region_map * 'a1 instr_r) result **)

let alloc_array_swap _ saparams pmap rmap rs t0 es =
  match rs with
  | [] ->
    Error
      (E.stk_error_no_var
        ('s'::('w'::('a'::('p'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(','::(' '::('o'::('n'::('l'::('y'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('a'::('r'::('e'::(' '::('a'::('c'::('c'::('e'::('p'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  | y0 :: l ->
    (match y0 with
     | Lvar x ->
       (match l with
        | [] ->
          Error
            (E.stk_error_no_var
              ('s'::('w'::('a'::('p'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(','::(' '::('o'::('n'::('l'::('y'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('a'::('r'::('e'::(' '::('a'::('c'::('c'::('e'::('p'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        | l0 :: l1 ->
          (match l0 with
           | Lvar y ->
             (match l1 with
              | [] ->
                (match es with
                 | [] ->
                   Error
                     (E.stk_error_no_var
                       ('s'::('w'::('a'::('p'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(','::(' '::('o'::('n'::('l'::('y'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('a'::('r'::('e'::(' '::('a'::('c'::('c'::('e'::('p'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                 | y1 :: l2 ->
                   (match y1 with
                    | Pvar z' ->
                      (match l2 with
                       | [] ->
                         Error
                           (E.stk_error_no_var
                             ('s'::('w'::('a'::('p'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(','::(' '::('o'::('n'::('l'::('y'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('a'::('r'::('e'::(' '::('a'::('c'::('c'::('e'::('p'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                       | p :: l3 ->
                         (match p with
                          | Pvar w' ->
                            (match l3 with
                             | [] ->
                               let z = z'.gv in
                               (match get_regptr pmap z with
                                | Ok x0 ->
                                  (match Region.check_valid rmap z (Some Z0)
                                           (size_of (Var.vtype z.v_var)) with
                                   | Ok x1 ->
                                     let (_, srz) = x1 in
                                     let w = w'.gv in
                                     (match get_regptr pmap w with
                                      | Ok x2 ->
                                        (match Region.check_valid rmap w
                                                 (Some Z0)
                                                 (size_of (Var.vtype w.v_var)) with
                                         | Ok x3 ->
                                           let (_, srw) = x3 in
                                           let rmap0 =
                                             Region.set_move rmap x.v_var srw
                                           in
                                           let rmap1 =
                                             Region.set_move rmap0 y.v_var srz
                                           in
                                           (match get_regptr pmap x with
                                            | Ok x4 ->
                                              (match get_regptr pmap y with
                                               | Ok x5 ->
                                                 if (&&) (is_lvar z')
                                                      (is_lvar w')
                                                 then Ok (rmap1,
                                                        (saparams.sap_swap t0
                                                          x4 x5 x0 x2))
                                                 else let s =
                                                        E.stk_ierror_no_var
                                                          ('g'::('l'::('o'::('b'::('a'::('l'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('.'::('.'::('.'::[]))))))))))))))))))
                                                      in
                                                      Error s
                                               | Error s -> Error s)
                                            | Error s -> Error s)
                                         | Error s -> Error s)
                                      | Error s -> Error s)
                                   | Error s -> Error s)
                                | Error s -> Error s)
                             | _ :: _ ->
                               Error
                                 (E.stk_error_no_var
                                   ('s'::('w'::('a'::('p'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(','::(' '::('o'::('n'::('l'::('y'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('a'::('r'::('e'::(' '::('a'::('c'::('c'::('e'::('p'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                          | _ ->
                            Error
                              (E.stk_error_no_var
                                ('s'::('w'::('a'::('p'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(','::(' '::('o'::('n'::('l'::('y'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('a'::('r'::('e'::(' '::('a'::('c'::('c'::('e'::('p'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    | _ ->
                      Error
                        (E.stk_error_no_var
                          ('s'::('w'::('a'::('p'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(','::(' '::('o'::('n'::('l'::('y'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('a'::('r'::('e'::(' '::('a'::('c'::('c'::('e'::('p'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              | _ :: _ ->
                Error
                  (E.stk_error_no_var
                    ('s'::('w'::('a'::('p'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(','::(' '::('o'::('n'::('l'::('y'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('a'::('r'::('e'::(' '::('a'::('c'::('c'::('e'::('p'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           | _ ->
             Error
               (E.stk_error_no_var
                 ('s'::('w'::('a'::('p'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(','::(' '::('o'::('n'::('l'::('y'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('a'::('r'::('e'::(' '::('a'::('c'::('c'::('e'::('p'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     | _ ->
       Error
         (E.stk_error_no_var
           ('s'::('w'::('a'::('p'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('o'::('r'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(','::(' '::('o'::('n'::('l'::('y'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('a'::('r'::('e'::(' '::('a'::('c'::('c'::('e'::('p'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val alloc_i :
    coq_PointerData -> coq_MSFsize -> 'a1 asmOp -> bool -> 'a1 sh_params ->
    'a1 stack_alloc_params -> pos_map -> (funname -> stk_alloc_oracle_t) ->
    stk_alloc_oracle_t -> Region.region_map -> 'a1 instr ->
    (Region.region_map * 'a1 instr list) cexec **)

let rec alloc_i pd msfsz asmop check shparams saparams pmap local_alloc sao rmap = function
| MkI (ii, ir) ->
  (match ir with
   | Cassgn (r, t0, ty, e) ->
     if is_sarr ty
     then (match add_iinfo ii
                   (alloc_array_move_init pd asmop saparams pmap rmap r t0 e) with
           | Ok x -> Ok ((fst x), ((MkI (ii, (snd x))) :: []))
           | Error s -> Error s)
     else (match add_iinfo ii (alloc_e pd pmap rmap e) with
           | Ok x ->
             (match add_iinfo ii (alloc_lval pd pmap rmap r ty) with
              | Ok x0 ->
                Ok ((fst x0), ((MkI (ii, (Cassgn ((snd x0), t0, ty,
                  x)))) :: []))
              | Error s -> Error s)
           | Error s -> Error s)
   | Copn (rs, t0, o, e) ->
     (match is_protect_ptr_fail asmop rs o e with
      | Some p ->
        let (p0, msf) = p in
        let (r, e0) = p0 in
        (match alloc_protect_ptr pd asmop shparams pmap rmap ii r t0 e0 msf with
         | Ok x -> Ok ((fst x), ((MkI (ii, (snd x))) :: []))
         | Error s -> Error s)
      | None ->
        if is_swap_array asmop o
        then (match add_iinfo ii
                      (alloc_array_swap asmop saparams pmap rmap rs t0 e) with
              | Ok x -> Ok ((fst x), ((MkI (ii, (snd x))) :: []))
              | Error s -> Error s)
        else (match add_iinfo ii (alloc_es pd pmap rmap e) with
              | Ok x ->
                (match add_iinfo ii
                         (alloc_lvals pd pmap rmap rs
                           (sopn_tout msfsz asmop o)) with
                 | Ok x0 ->
                   Ok ((fst x0), ((MkI (ii, (Copn ((snd x0), t0, o,
                     x)))) :: []))
                 | Error s -> Error s)
              | Error s -> Error s))
   | Csyscall (rs, o, es) ->
     alloc_syscall pd asmop saparams pmap ii rmap rs o es
   | Cif (e, c1, c2) ->
     (match add_iinfo ii (alloc_e pd pmap rmap e) with
      | Ok x ->
        (match fmapM
                 (alloc_i pd msfsz asmop check shparams saparams pmap
                   local_alloc sao) rmap c1 with
         | Ok x0 ->
           (match fmapM
                    (alloc_i pd msfsz asmop check shparams saparams pmap
                      local_alloc sao) rmap c2 with
            | Ok x1 ->
              let rmap0 = Region.merge (fst x0) (fst x1) in
              Ok (rmap0, ((MkI (ii, (Cif (x, (flatten (snd x0)),
              (flatten (snd x1)))))) :: []))
            | Error s -> Error s)
         | Error s -> Error s)
      | Error s -> Error s)
   | Cfor (_, _, _) ->
     Error
       (pp_at_ii ii
         (E.stk_ierror_no_var
           ('d'::('o'::('n'::('\''::('t'::(' '::('d'::('e'::('a'::('l'::(' '::('w'::('i'::('t'::('h'::(' '::('f'::('o'::('r'::(' '::('l'::('o'::('o'::('p'::[]))))))))))))))))))))))))))
   | Cwhile (a, c1, e, c2) ->
     let check_c = fun rmap0 ->
       match fmapM
               (alloc_i pd msfsz asmop check shparams saparams pmap
                 local_alloc sao) rmap0 c1 with
       | Ok x ->
         let rmap1 = fst x in
         (match add_iinfo ii (alloc_e pd pmap rmap1 e) with
          | Ok x0 ->
            (match fmapM
                     (alloc_i pd msfsz asmop check shparams saparams pmap
                       local_alloc sao) rmap1 c2 with
             | Ok x1 -> Ok ((rmap1, (fst x1)), (x0, ((snd x), (snd x1))))
             | Error s -> Error s)
          | Error s -> Error s)
       | Error s -> Error s
     in
     (match loop2 asmop ii check_c Loop.nb rmap with
      | Ok x ->
        Ok ((fst x), ((MkI (ii, (Cwhile (a, (flatten (fst (snd (snd x)))),
          (fst (snd x)), (flatten (snd (snd (snd x)))))))) :: []))
      | Error s -> Error s)
   | Ccall (rs, fn, es) ->
     (match add_iinfo ii
              (alloc_call pd asmop check pmap local_alloc sao rmap rs fn es) with
      | Ok x -> Ok ((fst x), ((MkI (ii, (snd x))) :: []))
      | Error s -> Error s))

(** val init_stack_layout :
    (coq_Z * wsize) Mvar.t -> stk_alloc_oracle_t -> (pp_error_loc,
    (coq_Z * wsize) Mvar.t) result **)

let init_stack_layout mglob sao =
  let add0 = fun xsr slp ->
    let (stack, p) = slp in
    let (p0, ofs) = xsr in
    let (x, ws) = p0 in
    (match Mvar.get stack x with
     | Some _ ->
       Error
         (E.stk_ierror_no_var
           ('d'::('u'::('p'::('l'::('i'::('c'::('a'::('t'::('e'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('r'::('e'::('g'::('i'::('o'::('n'::[])))))))))))))))))))))))
     | None ->
       (match Mvar.get mglob x with
        | Some _ ->
          Error
            (E.stk_ierror_no_var
              ('a'::(' '::('r'::('e'::('g'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('b'::('o'::('t'::('h'::(' '::('g'::('l'::('o'::('b'::(' '::('a'::('n'::('d'::(' '::('s'::('t'::('a'::('c'::('k'::[]))))))))))))))))))))))))))))))))
        | None ->
          if cmp_le Z.compare p ofs
          then let len = size_of (Var.vtype (Obj.magic x)) in
               if cmp_le wsize_cmp ws sao.sao_align
               then if eq_op coq_Z_eqType
                         (Obj.magic Z.coq_land ofs
                           (Z.sub (wsize_size ws) (Zpos Coq_xH)))
                         (Obj.magic Z0)
                    then let stack0 = Mvar.set stack x (ofs, ws) in
                         Ok (stack0, (Z.add ofs len))
                    else Error
                           (E.stk_ierror_no_var
                             ('b'::('a'::('d'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('r'::('e'::('g'::('i'::('o'::('n'::(' '::('a'::('l'::('i'::('g'::('n'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))))))
               else Error
                      (E.stk_ierror_no_var
                        ('b'::('a'::('d'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('a'::('l'::('i'::('g'::('n'::('m'::('e'::('n'::('t'::[]))))))))))))))))))))
          else Error
                 (E.stk_ierror_no_var
                   ('s'::('t'::('a'::('c'::('k'::(' '::('r'::('e'::('g'::('i'::('o'::('n'::(' '::('o'::('v'::('e'::('r'::('l'::('a'::('p'::[])))))))))))))))))))))))
  in
  if Z.leb Z0 sao.sao_ioff
  then (match foldM (Obj.magic add0) (Mvar.empty, sao.sao_ioff) sao.sao_slots with
        | Ok x ->
          let (stack, size0) = x in
          if cmp_le Z.compare size0 sao.sao_size
          then Ok stack
          else Error
                 (E.stk_ierror_no_var
                   ('s'::('t'::('a'::('c'::('k'::(' '::('s'::('i'::('z'::('e'::[])))))))))))
        | Error s -> Error s)
  else let s =
         E.stk_ierror_no_var
           ('n'::('e'::('g'::('a'::('t'::('i'::('v'::('e'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::[])))))))))))))))))))))))))))))
       in
       Error s

(** val add_alloc :
    coq_PointerData -> (coq_Z * wsize) Mvar.t -> (coq_Z * wsize) Mvar.t ->
    (Var.var * ptr_kind_init) -> ((ptr_kind
    Mvar.t * Region.region_map) * SvExtra.Sv.t) -> (pp_error_loc, (ptr_kind
    Mvar.Map.t * Region.region_map) * SvExtra.Sv.t) result **)

let add_alloc pd globals0 stack xpk = function
| (p, sv) ->
  let (locals0, rmap) = p in
  let (x, pk) = xpk in
  if SvExtra.Sv.mem (Obj.magic x) sv
  then Error
         (E.stk_ierror_no_var
           ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('g'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::[]))))))))))))))))))))
  else (match Mvar.get locals0 (Obj.magic x) with
        | Some _ ->
          Error
            (E.stk_ierror_no_var
              ('t'::('h'::('e'::(' '::('o'::('r'::('a'::('c'::('l'::('e'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::('e'::('d'::(' '::('t'::('w'::('o'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::('s'::(' '::('f'::('o'::('r'::(' '::('t'::('h'::('e'::(' '::('s'::('a'::('m'::('e'::(' '::('v'::('a'::('r'::[])))))))))))))))))))))))))))))))))))))))))))))))))
        | None ->
          (match match pk with
                 | PIdirect (x', z, sc) ->
                   let vars =
                     match sc with
                     | Slocal -> stack
                     | Sglob -> globals0
                   in
                   (match Mvar.get vars (Obj.magic x') with
                    | Some y ->
                      let (ofs', ws') = y in
                      if (&&)
                           (cmp_le Z.compare (size_of (Var.vtype x)) z.z_len)
                           ((&&) (cmp_le Z.compare Z0 z.z_ofs)
                             (cmp_le Z.compare (Z.add z.z_ofs z.z_len)
                               (size_of (Var.vtype x'))))
                      then let rmap0 =
                             match sc with
                             | Slocal ->
                               let sr = sub_region_stack x' ws' z in
                               Region.set_arr_init rmap x sr
                             | Sglob -> rmap
                           in
                           Ok ((sv, (Pdirect (x', ofs', ws', z, sc))), rmap0)
                      else Error
                             (E.stk_ierror_no_var
                               ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('s'::('l'::('o'::('t'::[])))))))))))))
                    | None ->
                      Error
                        (E.stk_ierror_no_var
                          ('u'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('r'::('e'::('g'::('i'::('o'::('n'::[]))))))))))))))))
                 | PIregptr p0 ->
                   if negb (is_sarr (Var.vtype x))
                   then Error
                          (E.stk_ierror_no_var
                            ('a'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('a'::('n'::(' '::('a'::('r'::('r'::('a'::('y'::[]))))))))))))))))))))))))))))))))))))
                   else if SvExtra.Sv.mem (Obj.magic p0) sv
                        then Error
                               (E.stk_ierror_no_var
                                 ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('g'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::(' '::('a'::('l'::('r'::('e'::('a'::('d'::('y'::(' '::('e'::('x'::('i'::('s'::('t'::('s'::[])))))))))))))))))))))))))))))))))))
                        else (match Mvar.get locals0 (Obj.magic p0) with
                              | Some _ ->
                                Error
                                  (E.stk_ierror_no_var
                                    ('a'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::(' '::('i'::('s'::(' '::('e'::('q'::('u'::('a'::('l'::(' '::('t'::('o'::(' '::('a'::(' '::('p'::('r'::('o'::('g'::('r'::('a'::('m'::(' '::('v'::('a'::('r'::[]))))))))))))))))))))))))))))))))))))
                              | None ->
                                if negb
                                     (eq_op stype_eqType
                                       (Obj.magic Var.vtype p0)
                                       (Obj.magic (Coq_sword (coq_Uptr pd))))
                                then Error
                                       (E.stk_ierror_no_var
                                         ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::(' '::('t'::('y'::('p'::('e'::[])))))))))))))))))))))
                                else Ok (((SvExtra.Sv.add (Obj.magic p0) sv),
                                       (Pregptr p0)), rmap))
                 | PIstkptr (x', z, xp) ->
                   if negb (is_sarr (Var.vtype x))
                   then Error
                          (E.stk_ierror_no_var
                            ('a'::(' '::('s'::('t'::('k'::(' '::('p'::('t'::('r'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('a'::('n'::(' '::('a'::('r'::('r'::('a'::('y'::[]))))))))))))))))))))))))))))))))))))
                   else (match Mvar.get stack (Obj.magic x') with
                         | Some p0 ->
                           let (ofs', ws') = p0 in
                           if SvExtra.Sv.mem (Obj.magic xp) sv
                           then Error
                                  (E.stk_ierror_no_var
                                    ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('s'::('t'::('k'::(' '::('p'::('t'::('r'::(' '::('('::('n'::('o'::('t'::(' '::('u'::('n'::('i'::('q'::('u'::('e'::(')'::[])))))))))))))))))))))))))))))
                           else if eq_op Var.var_eqType (Obj.magic xp)
                                     (Obj.magic x)
                                then Error
                                       (E.stk_ierror_no_var
                                         ('a'::(' '::('p'::('s'::('e'::('u'::('d'::('o'::('-'::('v'::('a'::('r'::(' '::('i'::('s'::(' '::('e'::('q'::('u'::('a'::('l'::(' '::('t'::('o'::(' '::('a'::(' '::('p'::('r'::('o'::('g'::('r'::('a'::('m'::(' '::('v'::('a'::('r'::[])))))))))))))))))))))))))))))))))))))))
                                else (match Mvar.get locals0 (Obj.magic xp) with
                                      | Some _ ->
                                        Error
                                          (E.stk_ierror_no_var
                                            ('a'::(' '::('p'::('s'::('e'::('u'::('d'::('o'::('-'::('v'::('a'::('r'::(' '::('i'::('s'::(' '::('e'::('q'::('u'::('a'::('l'::(' '::('t'::('o'::(' '::('a'::(' '::('p'::('r'::('o'::('g'::('r'::('a'::('m'::(' '::('v'::('a'::('r'::[])))))))))))))))))))))))))))))))))))))))
                                      | None ->
                                        if (&&)
                                             (cmp_le wsize_cmp (coq_Uptr pd)
                                               ws')
                                             ((&&)
                                               (cmp_le Z.compare Z0 z.z_ofs)
                                               ((&&)
                                                 (eq_op coq_Z_eqType
                                                   (Obj.magic Z.coq_land
                                                     z.z_ofs
                                                     (Z.sub
                                                       (wsize_size
                                                         (coq_Uptr pd)) (Zpos
                                                       Coq_xH)))
                                                   (Obj.magic Z0))
                                                 ((&&)
                                                   (cmp_le Z.compare
                                                     (wsize_size
                                                       (coq_Uptr pd)) z.z_len)
                                                   (cmp_le Z.compare
                                                     (Z.add z.z_ofs z.z_len)
                                                     (size_of (Var.vtype x'))))))
                                        then Ok
                                               (((SvExtra.Sv.add
                                                   (Obj.magic xp) sv),
                                               (Pstkptr (x', ofs', ws', z,
                                               xp))), rmap)
                                        else Error
                                               (E.stk_ierror_no_var
                                                 ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('p'::('t'::('r'::(' '::('k'::('i'::('n'::('d'::[]))))))))))))))))))
                         | None ->
                           Error
                             (E.stk_ierror_no_var
                               ('u'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('r'::('e'::('g'::('i'::('o'::('n'::[])))))))))))))))))))))) with
           | Ok x0 ->
             let (y, rmap0) = x0 in
             let (sv0, pk0) = y in
             let locals1 = Mvar.set locals0 (Obj.magic x) pk0 in
             Ok ((locals1, rmap0), sv0)
           | Error s -> Error s))

(** val init_local_map :
    coq_PointerData -> SvExtra.Sv.elt -> SvExtra.Sv.elt -> SvExtra.Sv.elt ->
    (coq_Z * wsize) Mvar.t -> (coq_Z * wsize) Mvar.t -> stk_alloc_oracle_t ->
    (pp_error_loc, (ptr_kind Mvar.t * Region.region_map) * SvExtra.Sv.t)
    result **)

let init_local_map pd vrip0 vrsp0 vxlen0 globals0 stack sao =
  if negb (eq_op CmpVar.t vxlen0 vrip0)
  then if negb (eq_op CmpVar.t vxlen0 vrsp0)
       then let sv =
              SvExtra.Sv.add vxlen0
                (SvExtra.Sv.add vrip0 (SvExtra.Sv.add vrsp0 SvExtra.Sv.empty))
            in
            (match foldM (add_alloc pd globals0 stack) ((Mvar.empty,
                     Region.empty), sv) sao.sao_alloc with
             | Ok x -> Ok x
             | Error s -> Error s)
       else let s =
              E.stk_ierror_no_var
                ('t'::('w'::('o'::(' '::('f'::('r'::('e'::('s'::('h'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::('s'::(' '::('a'::('r'::('e'::(' '::('e'::('q'::('u'::('a'::('l'::[])))))))))))))))))))))))))))))
            in
            Error s
  else let s =
         E.stk_ierror_no_var
           ('t'::('w'::('o'::(' '::('f'::('r'::('e'::('s'::('h'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::('s'::(' '::('a'::('r'::('e'::(' '::('e'::('q'::('u'::('a'::('l'::[])))))))))))))))))))))))))))))
       in
       Error s

(** val check_result :
    pos_map -> Region.region_map -> Equality.sort option list -> var_i list
    -> nat option -> var_i -> (pp_error_loc, var_i) result **)

let check_result pmap rmap paramsi params oi x =
  match oi with
  | Some i ->
    (match nth None paramsi i with
     | Some sr ->
       if eq_op stype_eqType (Obj.magic Var.vtype x.v_var)
            (Obj.magic Var.vtype (nth x params i).v_var)
       then (match Region.check_valid rmap x (Some Z0)
                     (size_of (Var.vtype x.v_var)) with
             | Ok x0 ->
               let sr' = fst x0 in
               if eq_op sub_region_eqType sr (Obj.magic sr')
               then (match get_regptr pmap x with
                     | Ok x1 -> Ok x1
                     | Error s -> Error s)
               else let s =
                      E.stk_ierror_no_var
                        ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('i'::('n'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::[])))))))))))))))))))))))))
                    in
                    Error s
             | Error s -> Error s)
       else let s =
              E.stk_ierror_no_var
                ('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('i'::('n'::(' '::('r'::('e'::('s'::('u'::('l'::('t'::(' '::('n'::('o'::('t'::(' '::('c'::('o'::('r'::('r'::('e'::('s'::('p'::('o'::('n'::('d'::('i'::('n'::('g'::(' '::('t'::('o'::(' '::('a'::(' '::('p'::('a'::('r'::('a'::('m'::('e'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))))))))))))))))
            in
            Error s
     | None ->
       Error
         (E.stk_ierror_no_var
           ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('i'::('n'::('f'::('o'::[])))))))))))))))))))))))
  | None ->
    (match check_var pmap x with
     | Ok _ ->
       (match check_diff pmap x with
        | Ok _ -> Ok x
        | Error s -> Error s)
     | Error s -> Error s)

(** val check_all_writable_regions_returned :
    sub_region option list -> nat option list -> bool **)

let check_all_writable_regions_returned paramsi ret_pos =
  all2 (fun i osr ->
    match osr with
    | Some sr ->
      if sr.sr_region.r_writable
      then in_mem (Obj.magic (Some i))
             (mem (seq_predType (option_eqType nat_eqType))
               (Obj.magic ret_pos))
      else true
    | None -> true) (iota O (size paramsi)) paramsi

(** val check_results :
    pos_map -> Region.region_map -> Equality.sort option list -> var_i list
    -> nat option list -> var_i list -> (pp_error_loc, var_i list) result **)

let check_results pmap rmap paramsi params ret_pos res =
  if check_all_writable_regions_returned (Obj.magic paramsi) ret_pos
  then mapM2
         (E.stk_ierror_no_var
           ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('i'::('n'::('f'::('o'::[]))))))))))))))))))))))
         (check_result pmap rmap paramsi params) ret_pos res
  else let s =
         E.stk_ierror_no_var
           ('a'::(' '::('w'::('r'::('i'::('t'::('a'::('b'::('l'::('e'::(' '::('r'::('e'::('g'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::('e'::('d'::[])))))))))))))))))))))))))))))))))
       in
       Error s

(** val init_param :
    coq_PointerData -> (coq_Z * wsize) Mvar.t -> (coq_Z * wsize) Mvar.t ->
    ((SvExtra.Sv.t * ptr_kind Mvar.t) * Region.region_map) -> param_info
    option -> var_i -> (pp_error_loc, ((SvExtra.Sv.t * ptr_kind
    Mvar.Map.t) * Region.region_map) * (sub_region option * var_i)) result **)

let init_param pd mglob stack accu pi x =
  let (y, rmap) = accu in
  let (disj, lmap) = y in
  if negb (SvExtra.Sv.mem (Obj.magic x.v_var) disj)
  then (match Mvar.get lmap (Obj.magic x.v_var) with
        | Some _ ->
          Error
            (E.stk_ierror_no_var
              ('a'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('a'::('l'::('s'::('o'::(' '::('o'::('c'::('c'::('u'::('r'::('s'::(' '::('a'::('s'::(' '::('a'::(' '::('p'::('a'::('r'::('a'::('m'::('e'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))))))))))))))))
        | None ->
          (match pi with
           | Some pi0 ->
             if eq_op stype_eqType (Obj.magic Var.vtype pi0.pp_ptr)
                  (Obj.magic (Coq_sword (coq_Uptr pd)))
             then if negb (SvExtra.Sv.mem (Obj.magic pi0.pp_ptr) disj)
                  then if is_sarr (Var.vtype x.v_var)
                       then (match Mvar.get lmap (Obj.magic pi0.pp_ptr) with
                             | Some _ ->
                               Error
                                 (E.stk_ierror_no_var
                                   ('a'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::(' '::('i'::('s'::(' '::('e'::('q'::('u'::('a'::('l'::(' '::('t'::('o'::(' '::('a'::(' '::('l'::('o'::('c'::('a'::('l'::(' '::('v'::('a'::('r'::[]))))))))))))))))))))))))))))))))))
                             | None ->
                               (match Mvar.get mglob (Obj.magic x.v_var) with
                                | Some _ ->
                                  Error
                                    (E.stk_ierror_no_var
                                      ('a'::(' '::('r'::('e'::('g'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('b'::('o'::('t'::('h'::(' '::('g'::('l'::('o'::('b'::(' '::('a'::('n'::('d'::(' '::('p'::('a'::('r'::('a'::('m'::[]))))))))))))))))))))))))))))))))
                                | None ->
                                  (match Mvar.get stack (Obj.magic x.v_var) with
                                   | Some _ ->
                                     Error
                                       (E.stk_ierror_no_var
                                         ('a'::(' '::('r'::('e'::('g'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('b'::('o'::('t'::('h'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('a'::('n'::('d'::(' '::('p'::('a'::('r'::('a'::('m'::[])))))))))))))))))))))))))))))))))
                                   | None ->
                                     let r = { r_slot = x.v_var; r_align =
                                       pi0.pp_align; r_writable =
                                       pi0.pp_writable }
                                     in
                                     let sr = sub_region_full x.v_var r in
                                     Ok
                                     ((((SvExtra.Sv.add
                                          (Obj.magic pi0.pp_ptr) disj),
                                     (Mvar.set lmap (Obj.magic x.v_var)
                                       (Pregptr pi0.pp_ptr))),
                                     (Region.set_move rmap x.v_var sr)),
                                     ((Some sr), (with_var x pi0.pp_ptr))))))
                       else let s =
                              E.stk_ierror_no_var
                                ('b'::('a'::('d'::(' '::('r'::('e'::('g'::(' '::('p'::('t'::('r'::(' '::('t'::('y'::('p'::('e'::[]))))))))))))))))
                            in
                            Error s
                  else let s =
                         E.stk_ierror_no_var
                           ('d'::('u'::('p'::('l'::('i'::('c'::('a'::('t'::('e'::(' '::('r'::('e'::('g'::('i'::('o'::('n'::[]))))))))))))))))
                       in
                       Error s
             else let s =
                    E.stk_ierror_no_var
                      ('b'::('a'::('d'::(' '::('p'::('t'::('r'::(' '::('t'::('y'::('p'::('e'::[]))))))))))))
                  in
                  Error s
           | None -> Ok (accu, (None, x))))
  else let s =
         E.stk_ierror_no_var
           ('a'::(' '::('p'::('a'::('r'::('a'::('m'::('e'::('t'::('e'::('r'::(' '::('a'::('l'::('r'::('e'::('a'::('d'::('y'::(' '::('e'::('x'::('i'::('s'::('t'::('s'::[]))))))))))))))))))))))))))
       in
       Error s

(** val init_params :
    coq_PointerData -> (coq_Z * wsize) Mvar.t -> (coq_Z * wsize) Mvar.t ->
    SvExtra.Sv.t -> ptr_kind Mvar.t -> Region.region_map -> param_info option
    list -> var_i list -> (pp_error_loc, ((SvExtra.Sv.t * ptr_kind
    Mvar.t) * Region.region_map) * (sub_region option * var_i) list) result **)

let init_params pd mglob stack disj lmap rmap sao_params0 params =
  fmapM2
    (E.stk_ierror_no_var
      ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('i'::('n'::('f'::('o'::[]))))))))))))))))))))))
    (init_param pd mglob stack) ((disj, lmap), rmap) sao_params0 params

(** val alloc_fd_aux :
    coq_PointerData -> coq_MSFsize -> 'a1 asmOp -> bool -> 'a1 sh_params ->
    'a1 stack_alloc_params -> sprog_extra -> (coq_Z * wsize) Mvar.t ->
    (Ident.Ident.name -> stype -> Ident.Ident.ident) -> (funname ->
    stk_alloc_oracle_t) -> stk_alloc_oracle_t -> ('a1, unit) _fundef -> 'a1
    _ufundef cexec **)

let alloc_fd_aux pd msfsz asmop check shparams saparams p_extra0 mglob fresh_reg local_alloc sao fd =
  let vrip0 = { Var.vtype = (Coq_sword (coq_Uptr pd)); Var.vname =
    p_extra0.sp_rip }
  in
  let vrsp0 = { Var.vtype = (Coq_sword (coq_Uptr pd)); Var.vname =
    p_extra0.sp_rsp }
  in
  let vxlen0 = { Var.vtype = (Coq_sword (coq_Uptr pd)); Var.vname =
    (fresh_reg
      (Ident.Ident.name_of_string
        ('_'::('_'::('l'::('e'::('n'::('_'::('_'::[])))))))) (Coq_sword
      (coq_Uptr pd))) }
  in
  (match init_stack_layout mglob sao with
   | Ok x ->
     (match init_local_map pd (Obj.magic vrip0) (Obj.magic vrsp0)
              (Obj.magic vxlen0) mglob x sao with
      | Ok x0 ->
        let (y, disj) = x0 in
        let (locals0, rmap) = y in
        (match init_params pd mglob x disj locals0 rmap sao.sao_params
                 fd.f_params with
         | Ok x1 ->
           let (y0, alloc_params) = x1 in
           let (y1, rmap0) = y0 in
           let (sv, lmap) = y1 in
           let paramsi = map fst alloc_params in
           let params = map snd alloc_params in
           let pmap = { vrip = vrip0; vrsp = vrsp0; vxlen = vxlen0; globals =
             mglob; locals = lmap; vnew = sv }
           in
           if Z.leb Z0 sao.sao_extra_size
           then (match let local_size = sao_frame_size sao in
                       assert_check check (Z.leb local_size sao.sao_max_size)
                         (E.stk_ierror_no_var
                           ('s'::('a'::('o'::('_'::('m'::('a'::('x'::('_'::('s'::('i'::('z'::('e'::(' '::('t'::('o'::('o'::(' '::('s'::('m'::('a'::('l'::('l'::[]))))))))))))))))))))))) with
                 | Ok _ ->
                   (match fmapM
                            (alloc_i pd msfsz asmop check shparams saparams
                              pmap local_alloc sao) rmap0 fd.f_body with
                    | Ok x2 ->
                      let (rmap1, body) = x2 in
                      (match check_results pmap rmap1 (Obj.magic paramsi)
                               fd.f_params sao.sao_return fd.f_res with
                       | Ok x3 ->
                         Ok { f_info = fd.f_info; f_tyin =
                           (map2 (fun o ty ->
                             match o with
                             | Some _ -> Coq_sword (coq_Uptr pd)
                             | None -> ty) sao.sao_params fd.f_tyin);
                           f_params = params; f_body = (flatten body);
                           f_tyout =
                           (map2 (fun o ty ->
                             match o with
                             | Some _ -> Coq_sword (coq_Uptr pd)
                             | None -> ty) sao.sao_return fd.f_tyout);
                           f_res = x3; f_extra = fd.f_extra }
                       | Error s -> Error s)
                    | Error s -> Error s)
                 | Error s -> Error s)
           else let s =
                  E.stk_ierror_no_var
                    ('n'::('e'::('g'::('a'::('t'::('i'::('v'::('e'::(' '::('e'::('x'::('t'::('r'::('a'::(' '::('s'::('i'::('z'::('e'::[])))))))))))))))))))
                in
                Error s
         | Error s -> Error s)
      | Error s -> Error s)
   | Error s -> Error s)

(** val alloc_fd :
    coq_PointerData -> coq_MSFsize -> 'a1 asmOp -> bool -> 'a1 sh_params ->
    'a1 stack_alloc_params -> sprog_extra -> (coq_Z * wsize) Mvar.t ->
    (Ident.Ident.name -> stype -> Ident.Ident.ident) -> (funname ->
    stk_alloc_oracle_t) -> funname -> ('a1, unit) _fundef -> (pp_error_loc,
    'a1 sfundef) result **)

let alloc_fd pd msfsz asmop check shparams saparams p_extra0 mglob fresh_reg local_alloc fn fd =
  match alloc_fd_aux pd msfsz asmop check shparams saparams p_extra0 mglob
          fresh_reg local_alloc (local_alloc fn) fd with
  | Ok x ->
    let f_extra0 = { sf_align = (local_alloc fn).sao_align; sf_stk_sz =
      (local_alloc fn).sao_size; sf_stk_ioff = (local_alloc fn).sao_ioff;
      sf_stk_extra_sz = (local_alloc fn).sao_extra_size; sf_stk_max =
      (local_alloc fn).sao_max_size; sf_max_call_depth =
      (local_alloc fn).sao_max_call_depth; sf_to_save =
      (local_alloc fn).sao_to_save; sf_save_stack = (local_alloc fn).sao_rsp;
      sf_return_address = (local_alloc fn).sao_return_address }
    in
    Ok (swith_extra pd asmop pd (Obj.magic x) (Obj.magic f_extra0))
  | Error s -> Error s

(** val ptake :
    positive -> 'a1 list -> 'a1 list -> ('a1 list * 'a1 list) option **)

let rec ptake p r l =
  match p with
  | Coq_xI p0 ->
    (match l with
     | [] -> None
     | x :: l0 ->
       (match ptake p0 (x :: r) l0 with
        | Some y -> let (r0, l1) = y in ptake p0 r0 l1
        | None -> None))
  | Coq_xO p0 ->
    (match ptake p0 r l with
     | Some p1 -> let (r0, l0) = p1 in ptake p0 r0 l0
     | None -> None)
  | Coq_xH -> (match l with
               | [] -> None
               | x :: l0 -> Some ((x :: r), l0))

(** val ztake : coq_Z -> 'a1 list -> ('a1 list * 'a1 list) option **)

let ztake z l =
  match z with
  | Z0 -> Some ([], l)
  | Zpos p ->
    (match ptake p [] l with
     | Some p0 -> let (r, l0) = p0 in Some ((rev r), l0)
     | None -> None)
  | Zneg _ -> None

(** val check_glob :
    GRing.ComRing.sort list -> glob_value -> (pp_error_loc, unit) result **)

let check_glob data = function
| Gword (ws, w) ->
  if eq_op (GRing.ComRing.eqType (word ws)) (LE.decode ws data) w
  then Ok ()
  else Error
         (E.stk_ierror_no_var
           ('b'::('a'::('d'::(' '::('d'::('e'::('c'::('o'::('d'::('e'::[])))))))))))
| Garr (p, t0) ->
  (match foldM (fun wd i ->
           match CoreMem.read coq_Z_eqType WArray.coq_PointerZ
                   (WArray.array_CM p) t0 (Obj.magic i) U8 with
           | Ok w ->
             if eq_op (GRing.ComRing.eqType (word U8)) wd w
             then Ok (Z.add i (Zpos Coq_xH))
             else Error
                    (E.stk_ierror_no_var
                      ('b'::('a'::('d'::(' '::('d'::('e'::('c'::('o'::('d'::('e'::(' '::('a'::('r'::('r'::('a'::('y'::(' '::('e'::('q'::[]))))))))))))))))))))
           | Error _ ->
             Error
               (E.stk_ierror_no_var
                 ('b'::('a'::('d'::(' '::('d'::('e'::('c'::('o'::('d'::('e'::(' '::('a'::('r'::('r'::('a'::('y'::(' '::('l'::('e'::('n'::[]))))))))))))))))))))))
           Z0 data with
   | Ok _ -> Ok ()
   | Error s -> Error s)

(** val size_glob : glob_value -> coq_Z **)

let size_glob = function
| Gword (ws, _) -> wsize_size ws
| Garr (p, _) -> Zpos p

(** val init_map :
    ((Var.var * wsize) * coq_Z) list -> GRing.ComRing.sort list -> glob_decl
    list -> (coq_Z * wsize) Mvar.t cexec **)

let init_map l data gd =
  let add0 = fun vp globals0 ->
    let (p0, p) = vp in
    let (v, ws) = p0 in
    let (p1, data0) = globals0 in
    let (mvar, pos) = p1 in
    if Z.leb pos p
    then if eq_op coq_Z_eqType
              (Obj.magic Z.coq_land p (Z.sub (wsize_size ws) (Zpos Coq_xH)))
              (Obj.magic Z0)
         then let s = size_of (Var.vtype v) in
              (match ztake (Z.sub p pos) data0 with
               | Some p2 ->
                 let (_, data1) = p2 in
                 (match ztake s data1 with
                  | Some p3 ->
                    let (vdata, data2) = p3 in
                    (match assoc Var.var_eqType (Obj.magic gd) (Obj.magic v) with
                     | Some gv0 ->
                       if eq_op coq_Z_eqType (Obj.magic s)
                            (Obj.magic size_glob gv0)
                       then (match check_glob vdata gv0 with
                             | Ok _ ->
                               Ok (((Mvar.set mvar (Obj.magic v) (p, ws)),
                                 (Z.add p s)), data2)
                             | Error s0 -> Error s0)
                       else let s0 =
                              E.stk_ierror_no_var
                                ('b'::('a'::('d'::(' '::('s'::('i'::('z'::('e'::[]))))))))
                            in
                            Error s0
                     | None ->
                       Error
                         (E.stk_ierror_no_var
                           ('u'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('v'::('a'::('r'::[])))))))))))))
                  | None ->
                    Error
                      (E.stk_ierror_no_var
                        ('b'::('a'::('d'::(' '::('d'::('a'::('t'::('a'::(' '::('2'::[]))))))))))))
               | None ->
                 Error
                   (E.stk_ierror_no_var
                     ('b'::('a'::('d'::(' '::('d'::('a'::('t'::('a'::(' '::('1'::[]))))))))))))
         else Error
                (E.stk_ierror_no_var
                  ('b'::('a'::('d'::(' '::('g'::('l'::('o'::('b'::('a'::('l'::(' '::('a'::('l'::('i'::('g'::('n'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))
    else Error
           (E.stk_ierror_no_var
             ('g'::('l'::('o'::('b'::('a'::('l'::(' '::('o'::('v'::('e'::('r'::('l'::('a'::('p'::[])))))))))))))))
  in
  (match foldM add0 ((Mvar.empty, Z0), data) l with
   | Ok x ->
     let (y, _) = x in
     let (mvar, _) = y in
     if SvExtra.Sv.subset (SvExtra.sv_of_list (Obj.magic fst) gd)
          (SvExtra.sv_of_list (fun x0 -> fst (fst (Obj.magic x0))) l)
     then Ok mvar
     else let s =
            E.stk_ierror_no_var
              ('m'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('g'::('l'::('o'::('b'::('a'::('l'::('s'::[])))))))))))))))
          in
          Error s
   | Error s -> Error s)

(** val alloc_prog :
    coq_PointerData -> coq_MSFsize -> 'a1 asmOp -> bool -> 'a1 sh_params ->
    'a1 stack_alloc_params -> (Ident.Ident.name -> stype ->
    Ident.Ident.ident) -> Ident.Ident.ident -> Ident.Ident.ident ->
    GRing.ComRing.sort list -> ((Var.var * wsize) * coq_Z) list -> (funname
    -> stk_alloc_oracle_t) -> 'a1 _uprog -> 'a1 _sprog cexec **)

let alloc_prog pd msfsz asmop check shparams saparams fresh_reg rip rsp global_data global_alloc local_alloc p =
  match init_map global_alloc global_data p.p_globs with
  | Ok x ->
    let p_extra0 = { sp_rsp = rsp; sp_rip = rip; sp_globs = global_data } in
    if negb (eq_op Ident.ident_eqType (Obj.magic rip) (Obj.magic rsp))
    then (match map_cfprog_name_gen (fun x0 -> x0.f_info)
                  (alloc_fd pd msfsz asmop check shparams saparams p_extra0 x
                    fresh_reg local_alloc) p.p_funcs with
          | Ok x0 ->
            Ok { p_funcs = (Obj.magic x0); p_globs = []; p_extra = p_extra0 }
          | Error s -> Error s)
    else let s =
           E.stk_ierror_no_var
             ('r'::('i'::('p'::(' '::('a'::('n'::('d'::(' '::('r'::('s'::('p'::(' '::('c'::('l'::('a'::('s'::('h'::[])))))))))))))))))
         in
         Error s
  | Error s -> Error s
