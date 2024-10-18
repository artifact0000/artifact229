open BinInt
open BinNums
open Eqtype
open Expr
open Fexpr
open Ssrfun
open Word0
open Word_ssrZ
open Wsize

type lea = { lea_disp : coq_Z; lea_base : var_i option; lea_scale : coq_Z;
             lea_offset : var_i option }

(** val lea_const : coq_Z -> lea **)

let lea_const z =
  { lea_disp = z; lea_base = None; lea_scale = (Zpos Coq_xH); lea_offset =
    None }

(** val lea_var : var_i -> lea **)

let lea_var x =
  { lea_disp = Z0; lea_base = (Some x); lea_scale = (Zpos Coq_xH);
    lea_offset = None }

(** val mkLea :
    coq_Z -> var_i option -> Equality.sort -> var_i option -> lea **)

let mkLea d b sc o =
  if eq_op coq_Z_eqType sc (Obj.magic Z0)
  then { lea_disp = d; lea_base = b; lea_scale = (Zpos Coq_xH); lea_offset =
         None }
  else { lea_disp = d; lea_base = b; lea_scale = (Obj.magic sc); lea_offset =
         o }

(** val lea_mul : lea -> lea -> lea option **)

let lea_mul l1 l2 =
  let { lea_disp = d1; lea_base = b1; lea_scale = sc1; lea_offset = o1 } = l1
  in
  let { lea_disp = d2; lea_base = b2; lea_scale = sc2; lea_offset = o2 } = l2
  in
  let d = Z.mul d1 d2 in
  (match b1 with
   | Some _ ->
     (match o1 with
      | Some _ -> None
      | None ->
        (match b2 with
         | Some _ -> None
         | None ->
           (match o2 with
            | Some _ -> None
            | None -> Some (mkLea d None (Obj.magic d2) b1))))
   | None ->
     (match o1 with
      | Some _ ->
        (match b2 with
         | Some _ -> None
         | None ->
           (match o2 with
            | Some _ -> None
            | None -> Some (mkLea d None (Obj.magic Z.mul d2 sc1) o1)))
      | None ->
        (match b2 with
         | Some _ ->
           (match o2 with
            | Some _ -> None
            | None -> Some (mkLea d None (Obj.magic d1) b2))
         | None ->
           (match o2 with
            | Some _ -> Some (mkLea d None (Obj.magic Z.mul d1 sc2) o2)
            | None -> Some (lea_const d)))))

(** val lea_add : lea -> lea -> lea option **)

let lea_add l1 l2 =
  let { lea_disp = d1; lea_base = b1; lea_scale = sc1; lea_offset = o1 } = l1
  in
  let { lea_disp = d2; lea_base = b2; lea_scale = sc2; lea_offset = o2 } = l2
  in
  let disp = Z.add d1 d2 in
  (match b1 with
   | Some _ ->
     (match o1 with
      | Some _ ->
        (match b2 with
         | Some _ -> None
         | None ->
           (match o2 with
            | Some _ -> None
            | None -> Some (mkLea disp b1 (Obj.magic sc1) o1)))
      | None ->
        (match b2 with
         | Some _ ->
           (match o2 with
            | Some _ -> None
            | None -> Some (mkLea disp b1 (Obj.magic (Zpos Coq_xH)) b2))
         | None ->
           (match o2 with
            | Some _ -> Some (mkLea disp b1 (Obj.magic sc2) o2)
            | None -> Some (mkLea disp b1 (Obj.magic sc1) o1))))
   | None ->
     (match o1 with
      | Some _ ->
        (match b2 with
         | Some _ ->
           (match o2 with
            | Some _ -> None
            | None -> Some (mkLea disp b2 (Obj.magic sc1) o1))
         | None ->
           (match o2 with
            | Some _ ->
              if eq_op coq_Z_eqType (Obj.magic sc1) (Obj.magic (Zpos Coq_xH))
              then Some (mkLea disp o1 (Obj.magic sc2) o2)
              else if eq_op coq_Z_eqType (Obj.magic sc2)
                        (Obj.magic (Zpos Coq_xH))
                   then Some (mkLea disp o2 (Obj.magic sc1) o1)
                   else None
            | None -> Some (mkLea disp b1 (Obj.magic sc1) o1)))
      | None -> Some (mkLea disp b2 (Obj.magic sc2) o2)))

(** val lea_sub : lea -> lea -> lea option **)

let lea_sub l1 l2 =
  let { lea_disp = d1; lea_base = b1; lea_scale = sc1; lea_offset = o1 } = l1
  in
  let { lea_disp = d2; lea_base = b2; lea_scale = _; lea_offset = o2 } = l2 in
  let disp = Z.sub d1 d2 in
  (match b2 with
   | Some _ -> None
   | None ->
     (match o2 with
      | Some _ -> None
      | None -> Some (mkLea disp b1 (Obj.magic sc1) o1)))

(** val mk_lea_rec : wsize -> fexpr -> lea option **)

let rec mk_lea_rec sz = function
| Fvar x -> Some (lea_var x)
| Fapp1 (s, f) ->
  (match s with
   | Oword_of_int sz' ->
     (match f with
      | Fconst z -> Some (lea_const (wunsigned sz' (wrepr sz' z)))
      | _ -> None)
   | _ -> None)
| Fapp2 (s, e1, e2) ->
  (match s with
   | Oadd o ->
     (match o with
      | Op_int -> None
      | Op_w _ ->
        (match mk_lea_rec sz e1 with
         | Some l1 ->
           (match mk_lea_rec sz e2 with
            | Some l2 -> lea_add l1 l2
            | None -> None)
         | None -> None))
   | Omul o ->
     (match o with
      | Op_int -> None
      | Op_w _ ->
        (match mk_lea_rec sz e1 with
         | Some l1 ->
           (match mk_lea_rec sz e2 with
            | Some l2 -> lea_mul l1 l2
            | None -> None)
         | None -> None))
   | Osub o ->
     (match o with
      | Op_int -> None
      | Op_w _ ->
        (match mk_lea_rec sz e1 with
         | Some l1 ->
           (match mk_lea_rec sz e2 with
            | Some l2 -> lea_sub l1 l2
            | None -> None)
         | None -> None))
   | _ -> None)
| _ -> None

(** val mk_lea : wsize -> pexpr -> lea option **)

let mk_lea sz e =
  Option.bind (mk_lea_rec sz) (fexpr_of_pexpr e)
