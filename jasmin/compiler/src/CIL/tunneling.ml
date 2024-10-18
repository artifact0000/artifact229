open Datatypes
open Compiler_util
open Eqtype
open Expr
open Label
open Linear
open Seq
open Seq_extra
open Sopn
open Ssrbool
open Unionfind
open Utils0
open Var0

module E =
 struct
  (** val pass : char list **)

  let pass =
    't'::('u'::('n'::('n'::('e'::('l'::('i'::('n'::('g'::[]))))))))

  (** val tunneling_error : char list -> pp_error_loc **)

  let tunneling_error =
    pp_internal_error_s pass
 end

(** val labels_of_body : 'a1 asmOp -> 'a1 linstr list -> label list **)

let labels_of_body _ fb =
  pmap (fun li -> match li.li_i with
                  | Llabel (_, lbl) -> Some lbl
                  | _ -> None) fb

(** val goto_targets : 'a1 asmOp -> 'a1 linstr list -> remote_label list **)

let goto_targets _ fb =
  pmap (fun li -> match li.li_i with
                  | Lgoto lbl -> Some lbl
                  | _ -> None) fb

(** val coq_Linstr_align : 'a1 asmOp -> 'a1 linstr **)

let coq_Linstr_align _ =
  { li_ii = dummy_instr_info; li_i = Lalign }

(** val tunnel_chart :
    'a1 asmOp -> Equality.sort -> LUF.unionfind -> 'a1 linstr -> 'a1 linstr
    -> LUF.unionfind **)

let tunnel_chart _ fn uf c c' =
  let { li_ii = _; li_i = li_i0 } = c in
  (match li_i0 with
   | Llabel (l0, l) ->
     (match l0 with
      | InternalLabel ->
        let { li_ii = _; li_i = li_i1 } = c' in
        (match li_i1 with
         | Llabel (l1, l') ->
           (match l1 with
            | InternalLabel -> LUF.union uf (Obj.magic l) (Obj.magic l')
            | ExternalLabel -> uf)
         | Lgoto r ->
           let (fn', l') = r in
           if eq_op funname_eqType fn (Obj.magic fn')
           then LUF.union uf (Obj.magic l) (Obj.magic l')
           else uf
         | _ -> uf)
      | ExternalLabel -> uf)
   | _ -> uf)

(** val tunnel_plan :
    'a1 asmOp -> Equality.sort -> LUF.unionfind -> 'a1 lcmd -> LUF.unionfind **)

let tunnel_plan asmop fn uf lc =
  pairfoldl (tunnel_chart asmop fn) uf (coq_Linstr_align asmop) lc

(** val tunnel_bore :
    'a1 asmOp -> Equality.sort -> LUF.unionfind -> 'a1 linstr -> 'a1 linstr **)

let tunnel_bore _ fn uf c =
  let { li_ii = ii; li_i = li } = c in
  (match li with
   | Lgoto r ->
     let (fn', l') = r in
     { li_ii = ii; li_i =
     (if eq_op funname_eqType fn (Obj.magic fn')
      then Lgoto (fn', (Obj.magic LUF.find uf l'))
      else Lgoto (fn', l')) }
   | Lcond (pe, l') ->
     { li_ii = ii; li_i = (Lcond (pe, (Obj.magic LUF.find uf l'))) }
   | _ -> { li_ii = ii; li_i = li })

(** val tunnel_head :
    'a1 asmOp -> Equality.sort -> LUF.unionfind -> 'a1 linstr list -> 'a1
    linstr list **)

let tunnel_head asmop fn uf lc =
  map (tunnel_bore asmop fn uf) lc

(** val tunnel_engine :
    'a1 asmOp -> Equality.sort -> 'a1 lcmd -> 'a1 lcmd -> 'a1 lcmd **)

let tunnel_engine asmop fn lc lc' =
  tunnel_head asmop fn (tunnel_plan asmop fn LUF.empty lc) lc'

(** val tunnel_lcmd : 'a1 asmOp -> Equality.sort -> 'a1 lcmd -> 'a1 lcmd **)

let tunnel_lcmd asmop fn lc =
  tunnel_engine asmop fn lc lc

(** val tunnel_lfundef :
    'a1 asmOp -> Equality.sort -> 'a1 lfundef -> 'a1 lfundef **)

let tunnel_lfundef asmop fn fd =
  with_lbody asmop fd (tunnel_lcmd asmop fn fd.lfd_body)

(** val tunnel_funcs :
    'a1 asmOp -> (Equality.sort * 'a1 lfundef) list -> (Equality.sort * 'a1
    lfundef) list **)

let tunnel_funcs asmop =
  map (fun f -> ((fst f), (tunnel_lfundef asmop (fst f) (snd f))))

(** val tunnel_lprog : 'a1 asmOp -> 'a1 lprog -> 'a1 lprog **)

let tunnel_lprog asmop p =
  with_lfds asmop p (Obj.magic tunnel_funcs asmop p.lp_funcs)

(** val well_formed_body : 'a1 asmOp -> funname -> 'a1 linstr list -> bool **)

let well_formed_body asmop fn fb =
  let lbls = labels_of_body asmop fb in
  (&&) (uniq pos_eqType (Obj.magic lbls))
    (all (fun pat ->
      let (fn', l) = pat in
      (||) (negb (eq_op funname_eqType (Obj.magic fn) (Obj.magic fn')))
        (in_mem (Obj.magic l)
          (mem (seq_predType pos_eqType) (Obj.magic lbls))))
      (goto_targets asmop fb))

(** val well_formed_funcs :
    'a1 asmOp -> (Equality.sort * 'a1 lfundef) list -> bool **)

let well_formed_funcs asmop lf =
  (&&) (uniq funname_eqType (map fst lf))
    (all (fun func ->
      well_formed_body asmop (fst (Obj.magic func)) (snd func).lfd_body) lf)

(** val well_formed_lprog : 'a1 asmOp -> 'a1 lprog -> bool **)

let well_formed_lprog asmop p =
  well_formed_funcs asmop (Obj.magic p.lp_funcs)

(** val tunnel_program :
    'a1 asmOp -> 'a1 lprog -> (pp_error_loc, 'a1 lprog) result **)

let tunnel_program asmop p =
  if well_formed_lprog asmop p
  then Ok (tunnel_lprog asmop p)
  else Error
         (E.tunneling_error
           ('n'::('o'::('t'::(' '::('w'::('e'::('l'::('l'::('-'::('f'::('o'::('r'::('m'::('e'::('d'::[]))))))))))))))))
