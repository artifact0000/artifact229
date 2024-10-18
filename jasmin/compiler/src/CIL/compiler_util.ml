open BinNums
open Datatypes
open Expr
open Fexpr
open Seq
open Sopn
open Utils0
open Var0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type warning_msg =
| Use_lea

type box =
| Vbox
| Hbox
| HoVbox
| Nobox

type pp_error =
| PPEstring of char list
| PPEz of coq_Z
| PPEvar of Var.var
| PPEvarinfo of var_info
| PPElval of lval
| PPEfunname of funname
| PPEfuninfo of fun_info
| PPEiinfo of instr_info
| PPEexpr of pexpr
| PPErexpr of rexpr
| PPEfexpr of fexpr
| PPEbox of box * pp_error list
| PPEbreak

type pp_error_loc = { pel_msg : pp_error; pel_fn : funname option;
                      pel_fi : fun_info option; pel_ii : instr_info option;
                      pel_vi : var_info option; pel_pass : char list option;
                      pel_internal : bool }

(** val pp_hov : pp_error list -> pp_error **)

let pp_hov x =
  PPEbox (HoVbox, x)

(** val pp_box : pp_error list -> pp_error **)

let pp_box x =
  PPEbox (Hbox, x)

(** val pp_vbox : pp_error list -> pp_error **)

let pp_vbox x =
  PPEbox (Vbox, x)

(** val pp_nobox : pp_error list -> pp_error **)

let pp_nobox x =
  PPEbox (Nobox, x)

(** val pp_list : pp_error -> ('a1 -> pp_error) -> 'a1 list -> pp_error **)

let rec pp_list sep pp = function
| [] -> pp_nobox []
| x :: xs0 ->
  (match xs0 with
   | [] -> pp x
   | _ :: _ -> pp_nobox ((pp x) :: (sep :: ((pp_list sep pp xs0) :: []))))

(** val pp_break : pp_error -> pp_error **)

let pp_break pp =
  pp_nobox (pp :: (PPEbreak :: []))

(** val pp_break_s : char list -> pp_error **)

let pp_break_s s =
  pp_break (PPEstring s)

(** val pp_Sv : SvExtra.Sv.t -> pp_error **)

let pp_Sv s =
  pp_nobox ((PPEstring
    ('{'::[])) :: ((pp_list (pp_break_s (','::[]))
                     (Obj.magic (fun x -> PPEvar x)) (SvExtra.Sv.elements s)) :: ((PPEstring
    ('}'::[])) :: [])))

type 'a cexec = (pp_error_loc, 'a) result

(** val pp_at_ii : instr_info -> pp_error_loc -> pp_error_loc **)

let pp_at_ii ii e =
  { pel_msg = e.pel_msg; pel_fn = e.pel_fn; pel_fi = e.pel_fi; pel_ii = (Some
    ii); pel_vi = e.pel_vi; pel_pass = e.pel_pass; pel_internal =
    e.pel_internal }

(** val add_iinfo : instr_info -> 'a1 cexec -> (pp_error_loc, 'a1) result **)

let add_iinfo ii = function
| Ok a -> Ok a
| Error e -> Error (pp_at_ii ii e)

(** val pp_at_fi : fun_info -> pp_error_loc -> pp_error_loc **)

let pp_at_fi fi e =
  { pel_msg = e.pel_msg; pel_fn = e.pel_fn; pel_fi = (Some fi); pel_ii =
    e.pel_ii; pel_vi = e.pel_vi; pel_pass = e.pel_pass; pel_internal =
    e.pel_internal }

(** val add_finfo : fun_info -> 'a1 cexec -> 'a1 cexec **)

let add_finfo fi = function
| Ok a -> Ok a
| Error pp -> Error (pp_at_fi fi pp)

(** val pp_at_fn : funname -> pp_error_loc -> pp_error_loc **)

let pp_at_fn fn e =
  { pel_msg = e.pel_msg; pel_fn = (Some fn); pel_fi = e.pel_fi; pel_ii =
    e.pel_ii; pel_vi = e.pel_vi; pel_pass = e.pel_pass; pel_internal =
    e.pel_internal }

(** val add_funname : funname -> 'a1 cexec -> 'a1 cexec **)

let add_funname fn = function
| Ok a -> Ok a
| Error pp -> Error (pp_at_fn fn pp)

(** val map_prog_name :
    'a1 asmOp -> progT -> (funname -> 'a1 fundef -> 'a1 fundef) -> 'a1 prog
    -> 'a1 prog **)

let map_prog_name _ _ f p =
  { p_funcs = (map (fun f0 -> ((fst f0), (f (fst f0) (snd f0)))) p.p_funcs);
    p_globs = p.p_globs; p_extra = p.p_extra }

(** val map_prog :
    'a1 asmOp -> progT -> ('a1 fundef -> 'a1 fundef) -> 'a1 prog -> 'a1 prog **)

let map_prog asmop pT f p =
  map_prog_name asmop pT (fun _ -> f) p

(** val map_cfprog_name_gen :
    ('a1 -> fun_info) -> (funname -> 'a1 -> 'a2 cexec) -> (funname * 'a1)
    list -> (pp_error_loc, (funname * 'a2) list) result **)

let map_cfprog_name_gen info f =
  mapM (fun f0 ->
    match add_finfo (info (snd f0))
            (add_funname (fst f0) (f (fst f0) (snd f0))) with
    | Ok x -> Ok ((fst f0), x)
    | Error s -> Error s)

(** val map_cfprog_gen :
    ('a1 -> fun_info) -> ('a1 -> 'a2 cexec) -> (funname * 'a1) list ->
    (pp_error_loc, (funname * 'a2) list) result **)

let map_cfprog_gen info f =
  map_cfprog_name_gen info (fun _ -> f)

(** val pp_internal_error : char list -> pp_error -> pp_error_loc **)

let pp_internal_error pass pp =
  { pel_msg = pp; pel_fn = None; pel_fi = None; pel_ii = None; pel_vi = None;
    pel_pass = (Some pass); pel_internal = true }

(** val pp_internal_error_s : char list -> char list -> pp_error_loc **)

let pp_internal_error_s pass s =
  pp_internal_error pass (PPEstring s)

(** val pp_internal_error_s_at :
    char list -> instr_info -> char list -> pp_error_loc **)

let pp_internal_error_s_at pass ii s =
  pp_at_ii ii (pp_internal_error_s pass s)

module type LoopCounter =
 sig
  val nb : nat
 end

module Loop =
 struct
  (** val nb : nat **)

  let nb =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val nbP : __ **)

  let nbP =
    __
 end

(** val gen_loop_iterator : char list -> instr_info option -> pp_error_loc **)

let gen_loop_iterator pass_name ii =
  { pel_msg = (PPEstring
    ('l'::('o'::('o'::('p'::(' '::('i'::('t'::('e'::('r'::('a'::('t'::('o'::('r'::(' '::('t'::('o'::('o'::(' '::('s'::('m'::('a'::('l'::('l'::[]))))))))))))))))))))))));
    pel_fn = None; pel_fi = None; pel_ii = ii; pel_vi = None; pel_pass =
    (Some pass_name); pel_internal = true }

(** val loop_iterator : char list -> pp_error_loc **)

let loop_iterator pass_name =
  gen_loop_iterator pass_name None

(** val ii_loop_iterator : char list -> instr_info -> pp_error_loc **)

let ii_loop_iterator pass_name ii =
  gen_loop_iterator pass_name (Some ii)
