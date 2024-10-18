open BinInt
open BinNums
open Datatypes
open String0
open Compiler_util
open Expr
open Label
open Linear
open Linear_util
open Memory_model
open One_varmap
open Seq
open Sopn
open Stack_zero_strategy
open Type
open Utils0
open Var0
open Warray_
open Word_ssrZ
open Wsize

module E =
 struct
  (** val pass : char list **)

  let pass =
    's'::('t'::('a'::('c'::('k'::(' '::('z'::('e'::('r'::('o'::('i'::('z'::('a'::('t'::('i'::('o'::('n'::[]))))))))))))))))

  (** val error : pp_error -> pp_error_loc **)

  let error msg =
    { pel_msg = msg; pel_fn = None; pel_fi = None; pel_ii = None; pel_vi =
      None; pel_pass = (Some pass); pel_internal = true }
 end

type 'asm_op stack_zeroization_params =
  stack_zero_strategy -> Ident.Ident.ident -> label -> wsize -> wsize ->
  coq_Z -> ('asm_op lcmd * SvExtra.Sv.t) cexec
  (* singleton inductive, whose constructor was Build_stack_zeroization_params *)

(** val szp_cmd :
    'a1 asmOp -> 'a1 stack_zeroization_params -> stack_zero_strategy ->
    Ident.Ident.ident -> label -> wsize -> wsize -> coq_Z -> ('a1
    lcmd * SvExtra.Sv.t) cexec **)

let szp_cmd _ s =
  s

(** val stack_zeroization_lfd_body :
    coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1
    stack_zeroization_params -> Ident.Ident.ident -> 'a1 lfundef ->
    stack_zero_strategy -> wsize -> 'a1 lfundef cexec **)

let stack_zeroization_lfd_body pd asmop ovmi szparams rspn lfd szs ws =
  let lbl = next_lfd_lbl asmop lfd in
  let ws_align = lfd.lfd_align in
  let frame_size = lfd.lfd_frame_size in
  let stk_max = lfd.lfd_stk_max in
  if is_align coq_Z_eqType WArray.coq_PointerZ (Obj.magic frame_size) ws_align
  then if is_align coq_Z_eqType WArray.coq_PointerZ (Obj.magic stk_max) ws
       then if cmp_le wsize_cmp ws ws_align
            then (match szp_cmd asmop szparams szs rspn lbl ws_align ws
                          stk_max with
                  | Ok x ->
                    let (cmd, vars) = x in
                    if negb
                         (SvExtra.Sv.mem
                           (Obj.magic
                             (mk_var_i { Var.vtype = (Coq_sword
                               (coq_Uptr pd)); Var.vname = rspn }).v_var)
                           vars)
                    then if SvExtra.disjoint vars
                              (SvExtra.Sv.union ovmi.callee_saved
                                (SvExtra.sv_of_list
                                  (Obj.magic (fun v -> v.v_var)) lfd.lfd_res))
                         then Ok (map_lfundef asmop (fun c -> cat c cmd) lfd)
                         else let s =
                                E.error
                                  (pp_box ((PPEstring
                                    ('T'::('h'::('e'::(' '::('z'::('e'::('r'::('o'::('i'::('z'::('a'::('t'::('i'::('o'::('n'::(' '::('c'::('o'::('d'::('e'::(' '::('m'::('o'::('d'::('i'::('f'::('i'::('e'::('d'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::('s'::(' '::('t'::('h'::('a'::('t'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((PPEstring
                                    ('u'::('n'::('c'::('h'::('a'::('n'::('g'::('e'::('d'::(' '::('p'::('e'::('r'::(' '::('t'::('h'::('e'::(' '::('c'::('a'::('l'::('l'::('i'::('n'::('g'::(' '::('c'::('o'::('n'::('v'::('e'::('n'::('t'::('i'::('o'::('n'::('s'::[])))))))))))))))))))))))))))))))))))))) :: [])))
                              in
                              Error s
                    else let s =
                           E.error
                             (pp_box ((PPEstring
                               ('R'::('S'::('P'::(' '::('m'::('o'::('d'::('i'::('f'::('i'::('e'::('d'::[]))))))))))))) :: []))
                         in
                         Error s
                  | Error s -> Error s)
            else let s =
                   E.error
                     (pp_box ((PPEstring
                       ('T'::('h'::('e'::(' '::('c'::('l'::('e'::('a'::('r'::(' '::('s'::('t'::('e'::('p'::(' '::('('::[]))))))))))))))))) :: ((PPEstring
                       (string_of_wsize ws)) :: ((PPEstring
                       (')'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('d'::('i'::('v'::('i'::('d'::('e'::(' '::('t'::('h'::('e'::(' '::('a'::('l'::('i'::('g'::('n'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('t'::('h'::('e'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('('::[]))))))))))))))))))))))))))))))))))))))))))))) :: ((PPEstring
                       (append ('u'::[]) (string_of_wsize ws_align))) :: ((PPEstring
                       (')'::[])) :: []))))))
                 in
                 Error s
       else let s =
              E.error
                (pp_box ((PPEstring
                  ('T'::('h'::('e'::(' '::('u'::('s'::('e'::('d'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('s'::('i'::('z'::('e'::(' '::('('::[])))))))))))))))))))))) :: ((PPEz
                  stk_max) :: ((PPEstring
                  (')'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('a'::(' '::('m'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('o'::('f'::(' '::('t'::('h'::('e'::(' '::('c'::('l'::('e'::('a'::('r'::(' '::('s'::('t'::('e'::('p'::(' '::('('::[]))))))))))))))))))))))))))))))))))))))))) :: ((PPEstring
                  (append ('u'::[]) (string_of_wsize ws))) :: ((PPEstring
                  (')'::[])) :: []))))))
            in
            Error s
  else let s =
         E.error
           (pp_box ((PPEstring
             ('T'::('h'::('e'::(' '::('e'::('x'::('p'::('o'::('r'::('t'::(' '::('f'::('r'::('a'::('m'::('e'::(' '::('s'::('i'::('z'::('e'::(' '::('('::[])))))))))))))))))))))))) :: ((PPEz
             frame_size) :: ((PPEstring
             (')'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('a'::(' '::('m'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('o'::('f'::(' '::('t'::('h'::('e'::(' '::('a'::('l'::('i'::('g'::('n'::('m'::('e'::('n'::('t'::(' '::('o'::('f'::(' '::('t'::('h'::('e'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('('::[]))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((PPEstring
             (append ('u'::[]) (string_of_wsize ws_align))) :: ((PPEstring
             (')'::[])) :: []))))))
       in
       Error s

(** val stack_zeroization_lfd :
    coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1
    stack_zeroization_params -> (funname -> (stack_zero_strategy * wsize)
    option) -> Ident.Ident.ident -> funname -> 'a1 lfundef -> 'a1 lfundef
    cexec **)

let stack_zeroization_lfd pd asmop ovmi szparams szs_of_fn rsp fn lfd =
  match szs_of_fn fn with
  | Some p ->
    let (szs, ws) = p in
    if (&&) lfd.lfd_export (Z.ltb Z0 lfd.lfd_stk_max)
    then stack_zeroization_lfd_body pd asmop ovmi szparams rsp lfd szs ws
    else Ok lfd
  | None -> Ok lfd

(** val stack_zeroization_lprog :
    coq_PointerData -> 'a1 asmOp -> one_varmap_info -> 'a1
    stack_zeroization_params -> (funname -> (stack_zero_strategy * wsize)
    option) -> 'a1 lprog -> 'a1 lprog cexec **)

let stack_zeroization_lprog pd asmop ovmi szparams szs_of_fn lp =
  match map_cfprog_name_gen (fun l -> l.lfd_info)
          (stack_zeroization_lfd pd asmop ovmi szparams szs_of_fn lp.lp_rsp)
          lp.lp_funcs with
  | Ok x ->
    Ok { lp_rip = lp.lp_rip; lp_rsp = lp.lp_rsp; lp_globs = lp.lp_globs;
      lp_funcs = x }
  | Error s -> Error s
