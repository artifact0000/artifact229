open BinInt
open BinNums
open Bool
open Datatypes
open EqdepFacts
open Compiler_util
open Eqtype
open Expr
open Flag_combination
open Global
open Sem_op_typed
open Sem_type
open Seq
open Slh_ops
open Sopn
open Ssralg
open Ssrbool
open Ssrfun
open Ssrint
open Type
open Utils0
open Var0
open Warray_
open Word0
open Word_ssrZ
open Wsize
open Xseq

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val e2bool : pexpr -> bool exec **)

let e2bool = function
| Pbool b -> Ok b
| _ -> type_error

(** val e2int : pexpr -> coq_Z exec **)

let e2int = function
| Pconst z -> Ok z
| _ -> type_error

(** val e2word : wsize -> pexpr -> GRing.ComRing.sort exec **)

let e2word sz e =
  match is_wconst sz e with
  | Some w -> Ok w
  | None -> type_error

(** val of_expr : stype -> pexpr -> sem_t exec **)

let of_expr = function
| Coq_sbool -> Obj.magic e2bool
| Coq_sint -> Obj.magic e2int
| Coq_sarr _ -> (fun _ -> type_error)
| Coq_sword sz -> e2word sz

(** val to_expr : stype -> sem_t -> pexpr exec **)

let to_expr t0 b =
  match t0 with
  | Coq_sbool -> Ok (Pbool (Obj.magic b))
  | Coq_sint -> Ok (Pconst (Obj.magic b))
  | Coq_sarr _ -> type_error
  | Coq_sword sz -> Ok (wconst sz b)

(** val ssem_sop1 : sop1 -> pexpr -> pexpr **)

let ssem_sop1 o e =
  let r =
    match of_expr (fst (type_of_op1 o)) e with
    | Ok x -> to_expr (snd (type_of_op1 o)) (sem_sop1_typed o x)
    | Error s -> Error s
  in
  (match r with
   | Ok e0 -> e0
   | Error _ -> Papp1 (o, e))

(** val ssem_sop2 : sop2 -> pexpr -> pexpr -> pexpr **)

let ssem_sop2 o e1 e2 =
  let r =
    match of_expr (fst (fst (type_of_op2 o))) e1 with
    | Ok x ->
      (match of_expr (snd (fst (type_of_op2 o))) e2 with
       | Ok x0 ->
         (match sem_sop2_typed o x x0 with
          | Ok x1 -> to_expr (snd (type_of_op2 o)) x1
          | Error s -> Error s)
       | Error s -> Error s)
    | Error s -> Error s
  in
  (match r with
   | Ok e -> e
   | Error _ -> Papp2 (o, e1, e2))

(** val snot : pexpr -> pexpr **)

let rec snot e = match e with
| Pbool b -> Pbool (negb b)
| Papp1 (s, e0) -> (match s with
                    | Onot -> e0
                    | _ -> Papp1 (Onot, e))
| Papp2 (s, e1, e2) ->
  (match s with
   | Oand -> Papp2 (Oor, (snot e1), (snot e2))
   | Oor -> Papp2 (Oand, (snot e1), (snot e2))
   | _ -> Papp1 (Onot, e))
| Pif (t0, e0, e1, e2) -> Pif (t0, e0, (snot e1), (snot e2))
| _ -> Papp1 (Onot, e)

(** val sneg_int : pexpr -> pexpr **)

let sneg_int e = match e with
| Pconst z -> Pconst (Z.opp z)
| Papp1 (s, e') ->
  (match s with
   | Oneg o ->
     (match o with
      | Op_int -> e'
      | Op_w _ -> Papp1 ((Oneg Op_int), e))
   | _ -> Papp1 ((Oneg Op_int), e))
| _ -> Papp1 ((Oneg Op_int), e)

(** val s_op1 : sop1 -> pexpr -> pexpr **)

let s_op1 o e =
  match o with
  | Onot -> snot e
  | Oneg o0 -> (match o0 with
                | Op_int -> sneg_int e
                | Op_w _ -> ssem_sop1 o e)
  | _ -> ssem_sop1 o e

(** val sbeq : pexpr -> pexpr -> pexpr **)

let sbeq e1 e2 =
  match is_bool e1 with
  | Some b ->
    (match is_bool e2 with
     | Some b0 -> Pbool (eq_op bool_eqType (Obj.magic b) (Obj.magic b0))
     | None -> if b then e2 else snot e2)
  | None ->
    (match is_bool e2 with
     | Some b -> if b then e1 else snot e1
     | None -> Papp2 (Obeq, e1, e2))

(** val sand : pexpr -> pexpr -> pexpr **)

let sand e1 e2 =
  match is_bool e1 with
  | Some b -> if b then e2 else Pbool false
  | None ->
    (match is_bool e2 with
     | Some b -> if b then e1 else Pbool false
     | None -> Papp2 (Oand, e1, e2))

(** val sor : pexpr -> pexpr -> pexpr **)

let sor e1 e2 =
  match is_bool e1 with
  | Some b -> if b then Pbool true else e2
  | None ->
    (match is_bool e2 with
     | Some b -> if b then Pbool true else e1
     | None -> Papp2 (Oor, e1, e2))

(** val sadd_int : pexpr -> pexpr -> pexpr **)

let sadd_int e1 e2 =
  match is_const e1 with
  | Some n ->
    (match is_const e2 with
     | Some n0 -> Pconst (Z.add n n0)
     | None ->
       if eq_op coq_Z_eqType (Obj.magic n) (Obj.magic int_to_Z (Posz O))
       then e2
       else Papp2 ((Oadd Op_int), e1, e2))
  | None ->
    (match is_const e2 with
     | Some n ->
       if eq_op coq_Z_eqType (Obj.magic n) (Obj.magic int_to_Z (Posz O))
       then e1
       else Papp2 ((Oadd Op_int), e1, e2)
     | None -> Papp2 ((Oadd Op_int), e1, e2))

(** val sadd_w : wsize -> pexpr -> pexpr -> pexpr **)

let sadd_w sz e1 e2 =
  match is_wconst sz e1 with
  | Some n ->
    (match is_wconst sz e2 with
     | Some n0 ->
       wconst sz (GRing.add (GRing.ComRing.zmodType (word sz)) n n0)
     | None ->
       if eq_op (GRing.ComRing.eqType (word sz)) n
            (GRing.zero (GRing.ComRing.zmodType (word sz)))
       then e2
       else Papp2 ((Oadd (Op_w sz)), e1, e2))
  | None ->
    (match is_wconst sz e2 with
     | Some n ->
       if eq_op (GRing.ComRing.eqType (word sz)) n
            (GRing.zero (GRing.ComRing.zmodType (word sz)))
       then e1
       else Papp2 ((Oadd (Op_w sz)), e1, e2)
     | None -> Papp2 ((Oadd (Op_w sz)), e1, e2))

(** val sadd : op_kind -> pexpr -> pexpr -> pexpr **)

let sadd = function
| Op_int -> sadd_int
| Op_w sz -> sadd_w sz

(** val ssub_int : pexpr -> pexpr -> pexpr **)

let ssub_int e1 e2 =
  match is_const e1 with
  | Some n1 ->
    (match is_const e2 with
     | Some n -> Pconst (Z.sub n1 n)
     | None -> Papp2 ((Osub Op_int), e1, e2))
  | None ->
    (match is_const e2 with
     | Some n ->
       if eq_op coq_Z_eqType (Obj.magic n) (Obj.magic int_to_Z (Posz O))
       then e1
       else Papp2 ((Osub Op_int), e1, e2)
     | None -> Papp2 ((Osub Op_int), e1, e2))

(** val ssub_w : wsize -> pexpr -> pexpr -> pexpr **)

let ssub_w sz e1 e2 =
  match is_wconst sz e1 with
  | Some n1 ->
    (match is_wconst sz e2 with
     | Some n ->
       wconst sz
         (GRing.add (GRing.ComRing.zmodType (word sz)) n1
           (GRing.opp (GRing.ComRing.zmodType (word sz)) n))
     | None -> Papp2 ((Osub (Op_w sz)), e1, e2))
  | None ->
    (match is_wconst sz e2 with
     | Some n ->
       if eq_op (GRing.ComRing.eqType (word sz)) n
            (GRing.zero (GRing.ComRing.zmodType (word sz)))
       then e1
       else Papp2 ((Osub (Op_w sz)), e1, e2)
     | None -> Papp2 ((Osub (Op_w sz)), e1, e2))

(** val ssub : op_kind -> pexpr -> pexpr -> pexpr **)

let ssub = function
| Op_int -> ssub_int
| Op_w sz -> ssub_w sz

(** val smul_int : pexpr -> pexpr -> pexpr **)

let smul_int e1 e2 =
  match is_const e1 with
  | Some n ->
    (match is_const e2 with
     | Some n0 -> Pconst (Z.mul n n0)
     | None ->
       if eq_op coq_Z_eqType (Obj.magic n) (Obj.magic int_to_Z (Posz O))
       then Pconst Z0
       else if eq_op coq_Z_eqType (Obj.magic n)
                 (Obj.magic int_to_Z (Posz (S O)))
            then e2
            else Papp2 ((Omul Op_int), e1, e2))
  | None ->
    (match is_const e2 with
     | Some n ->
       if eq_op coq_Z_eqType (Obj.magic n) (Obj.magic int_to_Z (Posz O))
       then Pconst Z0
       else if eq_op coq_Z_eqType (Obj.magic n)
                 (Obj.magic int_to_Z (Posz (S O)))
            then e1
            else Papp2 ((Omul Op_int), e1, e2)
     | None -> Papp2 ((Omul Op_int), e1, e2))

(** val smul_w : wsize -> pexpr -> pexpr -> pexpr **)

let smul_w sz e1 e2 =
  match is_wconst sz e1 with
  | Some n ->
    (match is_wconst sz e2 with
     | Some n0 ->
       wconst sz (GRing.mul (GRing.ComRing.ringType (word sz)) n n0)
     | None ->
       if eq_op (GRing.ComRing.eqType (word sz)) n
            (GRing.zero (GRing.ComRing.zmodType (word sz)))
       then wconst sz (GRing.zero (GRing.ComRing.zmodType (word sz)))
       else if eq_op (GRing.ComRing.eqType (word sz)) n
                 (GRing.one (GRing.ComRing.ringType (word sz)))
            then e2
            else Papp2 ((Omul (Op_w sz)), (wconst sz n), e2))
  | None ->
    (match is_wconst sz e2 with
     | Some n ->
       if eq_op (GRing.ComRing.eqType (word sz)) n
            (GRing.zero (GRing.ComRing.zmodType (word sz)))
       then wconst sz (GRing.zero (GRing.ComRing.zmodType (word sz)))
       else if eq_op (GRing.ComRing.eqType (word sz)) n
                 (GRing.one (GRing.ComRing.ringType (word sz)))
            then e1
            else Papp2 ((Omul (Op_w sz)), e1, (wconst sz n))
     | None -> Papp2 ((Omul (Op_w sz)), e1, e2))

(** val smul : op_kind -> pexpr -> pexpr -> pexpr **)

let smul = function
| Op_int -> smul_int
| Op_w sz -> smul_w sz

(** val s_eq : op_kind -> pexpr -> pexpr -> pexpr **)

let s_eq ty e1 e2 =
  if eq_expr e1 e2
  then Pbool true
  else (match ty with
        | Op_int ->
          (match is_const e1 with
           | Some i1 ->
             (match is_const e2 with
              | Some i2 ->
                Pbool (eq_op coq_Z_eqType (Obj.magic i1) (Obj.magic i2))
              | None -> Papp2 ((Oeq ty), e1, e2))
           | None -> Papp2 ((Oeq ty), e1, e2))
        | Op_w sz ->
          (match is_wconst sz e1 with
           | Some i1 ->
             (match is_wconst sz e2 with
              | Some i2 ->
                Pbool (eq_op (GRing.ComRing.eqType (word sz)) i1 i2)
              | None -> Papp2 ((Oeq ty), e1, e2))
           | None -> Papp2 ((Oeq ty), e1, e2)))

(** val sneq : op_kind -> pexpr -> pexpr -> pexpr **)

let sneq ty e1 e2 =
  match is_bool (s_eq ty e1 e2) with
  | Some b -> Pbool (negb b)
  | None -> Papp2 ((Oneq ty), e1, e2)

(** val is_cmp_const : cmp_kind -> pexpr -> coq_Z option **)

let is_cmp_const ty e =
  match ty with
  | Cmp_int -> is_const e
  | Cmp_w (sg, sz) ->
    Ssrfun.Option.bind (fun w -> Some
      (match sg with
       | Signed -> wsigned sz w
       | Unsigned -> wunsigned sz w)) (is_wconst sz e)

(** val slt : cmp_kind -> pexpr -> pexpr -> pexpr **)

let slt ty e1 e2 =
  if eq_expr e1 e2
  then Pbool false
  else (match is_cmp_const ty e1 with
        | Some n1 ->
          (match is_cmp_const ty e2 with
           | Some n2 -> Pbool (Z.ltb n1 n2)
           | None -> Papp2 ((Olt ty), e1, e2))
        | None -> Papp2 ((Olt ty), e1, e2))

(** val sle : cmp_kind -> pexpr -> pexpr -> pexpr **)

let sle ty e1 e2 =
  if eq_expr e1 e2
  then Pbool true
  else (match is_cmp_const ty e1 with
        | Some n1 ->
          (match is_cmp_const ty e2 with
           | Some n2 -> Pbool (Z.leb n1 n2)
           | None -> Papp2 ((Ole ty), e1, e2))
        | None -> Papp2 ((Ole ty), e1, e2))

(** val sgt : cmp_kind -> pexpr -> pexpr -> pexpr **)

let sgt ty e1 e2 =
  if eq_expr e1 e2
  then Pbool false
  else (match is_cmp_const ty e1 with
        | Some n1 ->
          (match is_cmp_const ty e2 with
           | Some n2 -> Pbool (Z.gtb n1 n2)
           | None -> Papp2 ((Ogt ty), e1, e2))
        | None -> Papp2 ((Ogt ty), e1, e2))

(** val sge : cmp_kind -> pexpr -> pexpr -> pexpr **)

let sge ty e1 e2 =
  if eq_expr e1 e2
  then Pbool true
  else (match is_cmp_const ty e1 with
        | Some n1 ->
          (match is_cmp_const ty e2 with
           | Some n2 -> Pbool (Z.geb n1 n2)
           | None -> Papp2 ((Oge ty), e1, e2))
        | None -> Papp2 ((Oge ty), e1, e2))

(** val s_op2 : sop2 -> pexpr -> pexpr -> pexpr **)

let s_op2 o e1 e2 =
  match o with
  | Obeq -> sbeq e1 e2
  | Oand -> sand e1 e2
  | Oor -> sor e1 e2
  | Oadd ty -> sadd ty e1 e2
  | Omul ty -> smul ty e1 e2
  | Osub ty -> ssub ty e1 e2
  | Oeq ty -> s_eq ty e1 e2
  | Oneq ty -> sneq ty e1 e2
  | Olt ty -> slt ty e1 e2
  | Ole ty -> sle ty e1 e2
  | Ogt ty -> sgt ty e1 e2
  | Oge ty -> sge ty e1 e2
  | _ -> ssem_sop2 o e1 e2

(** val app_sopn :
    stype list -> 'a1 exec sem_prod -> pexpr list -> 'a1 exec **)

let app_sopn ts x x0 =
  app_sopn of_expr ts x x0

(** val s_opN : coq_FlagCombinationParams -> opN -> pexpr list -> pexpr **)

let s_opN fcp op0 es =
  match app_sopn (fst (type_of_opN op0)) (sem_opN_typed fcp op0) es with
  | Ok r ->
    (match op0 with
     | Opack (ws, _) -> Papp1 ((Oword_of_int ws), (Pconst (wunsigned ws r)))
     | Ocombine_flags _ -> Pbool (Obj.magic r))
  | Error _ -> PappN (op0, es)

(** val s_if : stype -> pexpr -> pexpr -> pexpr -> pexpr **)

let s_if t0 e e1 e2 =
  match is_bool e with
  | Some b -> if b then e1 else e2
  | None -> Pif (t0, e, e1, e2)

type const_v =
| Cbool of bool
| Cint of coq_Z
| Cword of wsize * GRing.ComRing.sort

(** val const_v_beq : const_v -> const_v -> bool **)

let const_v_beq c1 c2 =
  match c1 with
  | Cbool b1 ->
    (match c2 with
     | Cbool b2 -> eq_op bool_eqType (Obj.magic b1) (Obj.magic b2)
     | _ -> false)
  | Cint z1 ->
    (match c2 with
     | Cint z2 -> eq_op coq_Z_eqType (Obj.magic z1) (Obj.magic z2)
     | _ -> false)
  | Cword (sz1, w1) ->
    (match c2 with
     | Cword (sz2, w2) ->
       if wsize_eq_dec sz1 sz2
       then eq_op (GRing.ComRing.eqType (word sz2)) w1 w2
       else false
     | _ -> false)

(** val const_v_eq_axiom : const_v Equality.axiom **)

let const_v_eq_axiom _top_assumption_ =
  let _evar_0_ = fun b1 __top_assumption_ ->
    let _evar_0_ = fun b2 ->
      let _evar_0_ = fun _ -> ReflectT in
      let _evar_0_0 = fun _ -> ReflectF in
      (match eqP bool_eqType b1 b2 with
       | ReflectT -> _evar_0_ __
       | ReflectF -> _evar_0_0 __)
    in
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = fun _ _ -> ReflectF in
    (match __top_assumption_ with
     | Cbool b -> Obj.magic _evar_0_ b
     | Cint z -> _evar_0_0 z
     | Cword (sz, word0) -> _evar_0_1 sz word0)
  in
  let _evar_0_0 = fun z1 __top_assumption_ ->
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = fun z2 ->
      let _evar_0_1 = fun _ -> ReflectT in
      let _evar_0_2 = fun _ -> ReflectF in
      (match eqP coq_Z_eqType z1 z2 with
       | ReflectT -> _evar_0_1 __
       | ReflectF -> _evar_0_2 __)
    in
    let _evar_0_2 = fun _ _ -> ReflectF in
    (match __top_assumption_ with
     | Cbool b -> _evar_0_0 b
     | Cint z -> Obj.magic _evar_0_1 z
     | Cword (sz, word0) -> _evar_0_2 sz word0)
  in
  let _evar_0_1 = fun sz1 w1 __top_assumption_ ->
    let _evar_0_1 = fun _ -> ReflectF in
    let _evar_0_2 = fun _ -> ReflectF in
    let _evar_0_3 = fun sz2 w2 ->
      let _evar_0_3 = fun _ ->
        internal_eq_rew_r_dep sz1 sz2 (fun w3 ->
          iffP (eq_op (GRing.ComRing.eqType (word sz2)) w3 w2)
            (if eq_op (GRing.ComRing.eqType (word sz2)) w3 w2
             then ReflectT
             else ReflectF)) w1
      in
      let _evar_0_4 = fun _ -> ReflectF in
      if wsize_eq_dec sz1 sz2 then _evar_0_3 __ else _evar_0_4 __
    in
    (match __top_assumption_ with
     | Cbool b -> _evar_0_1 b
     | Cint z -> _evar_0_2 z
     | Cword (sz, word0) -> _evar_0_3 sz word0)
  in
  (match _top_assumption_ with
   | Cbool b -> Obj.magic _evar_0_ b
   | Cint z -> Obj.magic _evar_0_0 z
   | Cword (sz, word0) -> _evar_0_1 sz word0)

(** val const_v_eqMixin : const_v Equality.mixin_of **)

let const_v_eqMixin =
  { Equality.op = const_v_beq; Equality.mixin_of__1 = const_v_eq_axiom }

(** val const_v_eqType : Equality.coq_type **)

let const_v_eqType =
  Obj.magic const_v_eqMixin

(** val const : const_v -> pexpr **)

let const = function
| Cbool b -> Pbool b
| Cint z -> Pconst z
| Cword (sz, z) -> wconst sz z

type globals = (Var.var -> glob_value option) option

(** val const_prop_e :
    coq_FlagCombinationParams -> globals -> const_v Mvar.t -> pexpr -> pexpr **)

let const_prop_e fcp globs =
  let pget_global = fun aa sz x e ->
    match globs with
    | Some f ->
      (match f x.gv.v_var with
       | Some g ->
         (match g with
          | Gword (_, _) -> Pget (aa, sz, x, e)
          | Garr (len, a) ->
            (match e with
             | Pconst i ->
               (match WArray.get len aa sz a i with
                | Ok w -> wconst sz w
                | Error _ -> Pget (aa, sz, x, e))
             | _ -> Pget (aa, sz, x, e)))
       | None -> Pget (aa, sz, x, e))
    | None -> Pget (aa, sz, x, e)
  in
  let rec const_prop_e0 m e = match e with
  | Pvar g ->
    let { gv = x; gs = scope } = g in
    (match scope with
     | Slocal ->
       (match Mvar.get m (Obj.magic x.v_var) with
        | Some n -> const n
        | None -> e)
     | Sglob ->
       (match globs with
        | Some f ->
          (match f x.v_var with
           | Some g0 ->
             (match g0 with
              | Gword (ws, w) -> const (Cword (ws, w))
              | Garr (_, _) -> e)
           | None -> e)
        | None -> e))
  | Pget (aa, sz, x, e0) ->
    let e1 = const_prop_e0 m e0 in
    if is_glob x then pget_global aa sz x e1 else Pget (aa, sz, x, e1)
  | Psub (aa, sz, len, x, e0) -> Psub (aa, sz, len, x, (const_prop_e0 m e0))
  | Pload (sz, x, e0) -> Pload (sz, x, (const_prop_e0 m e0))
  | Papp1 (o, e0) -> s_op1 o (const_prop_e0 m e0)
  | Papp2 (o, e1, e2) -> s_op2 o (const_prop_e0 m e1) (const_prop_e0 m e2)
  | PappN (op0, es) -> s_opN fcp op0 (map (const_prop_e0 m) es)
  | Pif (t0, e0, e1, e2) ->
    s_if t0 (const_prop_e0 m e0) (const_prop_e0 m e1) (const_prop_e0 m e2)
  | _ -> e
  in const_prop_e0

(** val empty_cpm : const_v Mvar.t **)

let empty_cpm =
  Mvar.empty

(** val merge_cpm : const_v Mvar.t -> const_v Mvar.t -> const_v Mvar.t **)

let merge_cpm =
  Mvar.map2 (fun _ o1 o2 ->
    match o1 with
    | Some n1 ->
      (match o2 with
       | Some n2 ->
         if eq_op const_v_eqType (Obj.magic n1) (Obj.magic n2)
         then Some n1
         else None
       | None -> None)
    | None -> None)

(** val remove_cpm : const_v Mvar.t -> SvExtra.Sv.t -> const_v Mvar.t **)

let remove_cpm m s =
  SvExtra.Sv.fold (fun x m0 -> Mvar.remove m0 x) s m

(** val const_prop_rv :
    coq_FlagCombinationParams -> globals -> const_v Mvar.t -> lval -> const_v
    Mvar.t * lval **)

let const_prop_rv fcp globs m rv = match rv with
| Lnone (_, _) -> (m, rv)
| Lvar x -> ((Mvar.remove m (Obj.magic x.v_var)), rv)
| Lmem (sz, x, e) -> (m, (Lmem (sz, x, (const_prop_e fcp globs m e))))
| Laset (aa, sz, x, e) ->
  ((Mvar.remove m (Obj.magic x.v_var)), (Laset (aa, sz, x,
    (const_prop_e fcp globs m e))))
| Lasub (aa, sz, len, x, e) ->
  ((Mvar.remove m (Obj.magic x.v_var)), (Lasub (aa, sz, len, x,
    (const_prop_e fcp globs m e))))

(** val const_prop_rvs :
    coq_FlagCombinationParams -> globals -> const_v Mvar.t -> lval list ->
    const_v Mvar.t * lval list **)

let rec const_prop_rvs fcp globs m = function
| [] -> (m, [])
| rv :: rvs0 ->
  let (m0, rv0) = const_prop_rv fcp globs m rv in
  let (m1, rvs1) = const_prop_rvs fcp globs m0 rvs0 in (m1, (rv0 :: rvs1))

(** val wsize_of_stype : stype -> wsize **)

let wsize_of_stype = function
| Coq_sword sz -> sz
| _ -> U64

(** val add_cpm :
    const_v Mvar.t -> lval -> assgn_tag -> stype -> pexpr -> const_v Mvar.t **)

let add_cpm m rv tag ty e =
  match rv with
  | Lvar x ->
    (match tag with
     | AT_inline ->
       (match e with
        | Pconst z -> Mvar.set m (Obj.magic x.v_var) (Cint z)
        | Pbool b -> Mvar.set m (Obj.magic x.v_var) (Cbool b)
        | Papp1 (s, p) ->
          (match s with
           | Oword_of_int _ ->
             (match p with
              | Pconst z ->
                let szty = wsize_of_stype ty in
                let szx = wsize_of_stype (Var.vtype x.v_var) in
                let sz = cmp_min wsize_cmp szty szx in
                let w = Cword (sz, (wrepr sz z)) in
                Mvar.set m (Obj.magic x.v_var) w
              | _ -> m)
           | _ -> m)
        | _ -> m)
     | _ -> m)
  | _ -> m

(** val const_prop :
    'a1 asmOp -> (const_v Mvar.t -> 'a1 instr -> const_v Mvar.t * 'a1 instr
    list) -> const_v Mvar.t -> 'a1 instr list -> const_v Mvar.t * 'a1 instr
    list **)

let rec const_prop asmop const_prop_i0 m = function
| [] -> (m, [])
| i :: c0 ->
  let (m0, ic) = const_prop_i0 m i in
  let (m1, c1) = const_prop asmop const_prop_i0 m0 c0 in (m1, (cat ic c1))

(** val is_update_imm :
    'a1 asmOp -> lval list -> 'a1 sopn -> pexpr list ->
    ((lval * bool) * pexpr) option **)

let is_update_imm _ xs o es =
  match o with
  | Oslh s ->
    (match s with
     | SLHupdate ->
       (match es with
        | [] -> None
        | y :: l ->
          (match y with
           | Pbool b ->
             (match l with
              | [] -> None
              | e :: l0 ->
                (match l0 with
                 | [] ->
                   (match xs with
                    | [] -> None
                    | x :: l1 ->
                      (match l1 with
                       | [] -> Some ((x, b), e)
                       | _ :: _ -> None))
                 | _ :: _ -> None))
           | _ -> None))
     | _ -> None)
  | _ -> None

(** val const_prop_i :
    coq_FlagCombinationParams -> coq_MSFsize -> 'a1 asmOp -> glob_decl list
    -> const_v Mvar.t -> 'a1 instr -> const_v Mvar.t * 'a1 instr list **)

let const_prop_i fcp msfsz asmop gd m i =
  let without_globals = None in
  let with_globals = fun gd0 tag ->
    match tag with
    | AT_none -> None
    | AT_keep -> None
    | AT_rename -> None
    | AT_inline -> Some (assoc Var.var_eqType gd0)
    | AT_phinode -> None
  in
  let rec const_prop_ir m0 ii ir = match ir with
  | Cassgn (x, tag, ty, e) ->
    let globs = Obj.magic with_globals gd tag in
    let e0 = const_prop_e fcp globs m0 e in
    let (m1, x0) = const_prop_rv fcp globs m0 x in
    let m2 = add_cpm m1 x0 tag ty e0 in
    (m2, ((MkI (ii, (Cassgn (x0, tag, ty, e0)))) :: []))
  | Copn (xs, t0, o, es) ->
    let es0 = map (const_prop_e fcp without_globals m0) es in
    let (m1, xs0) = const_prop_rvs fcp without_globals m0 xs in
    let ir0 =
      match is_update_imm asmop xs0 o es0 with
      | Some p ->
        let (p0, e) = p in
        let (x, b) = p0 in
        if b
        then Copn ((x :: []), AT_none, (Oslh SLHmove), (e :: []))
        else Cassgn (x, AT_none, (Coq_sword (msf_size msfsz)),
               (wconst (msf_size msfsz)
                 (GRing.opp
                   (GRing.Ring.zmodType
                     (GRing.ComRing.ringType (word (msf_size msfsz))))
                   (GRing.one
                     (GRing.ComRing.ringType (word (msf_size msfsz)))))))
      | None -> Copn (xs0, t0, o, es0)
    in
    (m1, ((MkI (ii, ir0)) :: []))
  | Csyscall (xs, o, es) ->
    let es0 = map (const_prop_e fcp without_globals m0) es in
    let (m1, xs0) = const_prop_rvs fcp without_globals m0 xs in
    (m1, ((MkI (ii, (Csyscall (xs0, o, es0)))) :: []))
  | Cif (b, c1, c2) ->
    let b0 = const_prop_e fcp without_globals m0 b in
    (match is_bool b0 with
     | Some b1 ->
       let c = if b1 then c1 else c2 in const_prop asmop const_prop_i0 m0 c
     | None ->
       let (m1, c3) = const_prop asmop const_prop_i0 m0 c1 in
       let (m2, c4) = const_prop asmop const_prop_i0 m0 c2 in
       ((merge_cpm m1 m2), ((MkI (ii, (Cif (b0, c3, c4)))) :: [])))
  | Cfor (x, r, c) ->
    let (p, e2) = r in
    let (dir, e1) = p in
    let e3 = const_prop_e fcp without_globals m0 e1 in
    let e4 = const_prop_e fcp without_globals m0 e2 in
    let m1 = remove_cpm m0 (write_i asmop ir) in
    let (_, c0) = const_prop asmop const_prop_i0 m1 c in
    (m1, ((MkI (ii, (Cfor (x, ((dir, e3), e4), c0)))) :: []))
  | Cwhile (a, c, e, c') ->
    let m1 = remove_cpm m0 (write_i asmop ir) in
    let (m', c0) = const_prop asmop const_prop_i0 m1 c in
    let e0 = const_prop_e fcp without_globals m' e in
    let (_, c'0) = const_prop asmop const_prop_i0 m' c' in
    let cw =
      match is_bool e0 with
      | Some b ->
        if b then (MkI (ii, (Cwhile (a, c0, e0, c'0)))) :: [] else c0
      | None -> (MkI (ii, (Cwhile (a, c0, e0, c'0)))) :: []
    in
    (m', cw)
  | Ccall (xs, f, es) ->
    let es0 = map (const_prop_e fcp without_globals m0) es in
    let (m1, xs0) = const_prop_rvs fcp without_globals m0 xs in
    (m1, ((MkI (ii, (Ccall (xs0, f, es0)))) :: []))
  and const_prop_i0 m0 = function
  | MkI (ii, ir) -> const_prop_ir m0 ii ir
  in const_prop_i0 m i

(** val const_prop_fun :
    coq_FlagCombinationParams -> coq_MSFsize -> 'a1 asmOp -> progT ->
    glob_decl list -> 'a1 fundef -> ('a1, extra_fun_t) _fundef **)

let const_prop_fun fcp msfsz asmop _ gd f =
  let { f_info = ii; f_tyin = si; f_params = p; f_body = c; f_tyout = so;
    f_res = r; f_extra = ev } = f
  in
  let (_, c0) = const_prop asmop (const_prop_i fcp msfsz asmop gd) empty_cpm c
  in
  { f_info = ii; f_tyin = si; f_params = p; f_body = c0; f_tyout = so;
  f_res = r; f_extra = ev }

(** val const_prop_prog :
    coq_FlagCombinationParams -> coq_MSFsize -> 'a1 asmOp -> progT -> 'a1
    prog -> 'a1 prog **)

let const_prop_prog fcp msfsz asmop pT p =
  map_prog asmop pT (const_prop_fun fcp msfsz asmop pT p.p_globs) p
