open BinNums
open BinPos
open Datatypes
open Label
open Linear
open Sopn
open Utils0

(** val map_lfundef :
    'a1 asmOp -> ('a1 lcmd -> 'a1 lcmd) -> 'a1 lfundef -> 'a1 lfundef **)

let map_lfundef _ f lfd =
  { lfd_info = lfd.lfd_info; lfd_align = lfd.lfd_align; lfd_tyin =
    lfd.lfd_tyin; lfd_arg = lfd.lfd_arg; lfd_body = (f lfd.lfd_body);
    lfd_tyout = lfd.lfd_tyout; lfd_res = lfd.lfd_res; lfd_export =
    lfd.lfd_export; lfd_callee_saved = lfd.lfd_callee_saved; lfd_stk_max =
    lfd.lfd_stk_max; lfd_frame_size = lfd.lfd_frame_size }

(** val max_map :
    ('a2 -> 'a2 -> comparison) -> ('a1 -> 'a2 option) -> 'a1 list -> 'a2
    option -> 'a2 option **)

let rec max_map cmp f xs acc =
  match xs with
  | [] -> acc
  | x :: xs' ->
    let acc' =
      match f x with
      | Some y -> Some (match acc with
                        | Some z -> cmp_max cmp y z
                        | None -> y)
      | None -> acc
    in
    max_map cmp f xs' acc'

(** val max_lcmd_lbl : 'a1 asmOp -> 'a1 lcmd -> label option **)

let max_lcmd_lbl _ c =
  let f = fun i ->
    match i.li_i with
    | Lopn (_, _, _) -> None
    | Lsyscall _ -> None
    | Lcall (_, _) -> None
    | Lret -> None
    | Lalign -> None
    | Llabel (_, lbl) -> Some lbl
    | _ -> None
  in
  max_map Pos.compare f c None

(** val max_lfd_lbl : 'a1 asmOp -> 'a1 lfundef -> label option **)

let max_lfd_lbl asmop lfd =
  max_lcmd_lbl asmop lfd.lfd_body

(** val next_lbl : label -> label **)

let next_lbl lbl =
  Pos.add lbl Coq_xH

(** val next_lfd_lbl : 'a1 asmOp -> 'a1 lfundef -> label **)

let next_lfd_lbl asmop lfd =
  match max_lfd_lbl asmop lfd with
  | Some lbl -> next_lbl lbl
  | None -> Coq_xH
