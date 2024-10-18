open BinNums
open Datatypes
open String0
open Arch_decl
open Arch_extra
open Compiler_util
open Eqtype
open Expr
open Fexpr
open Lea
open Linear
open One_varmap
open Oseq
open Seq
open Sopn
open Ssralg
open Ssrbool
open Ssrnat
open Syscall
open Type
open Utils0
open Var0
open Word0
open Wsize

module E =
 struct
  (** val pass_name : char list **)

  let pass_name =
    'a'::('s'::('m'::('g'::('e'::('n'::[])))))

  (** val gen_error :
      bool -> instr_info option -> var_info option -> pp_error -> pp_error_loc **)

  let gen_error internal ii vi msg =
    { pel_msg = msg; pel_fn = None; pel_fi = None; pel_ii = ii; pel_vi = vi;
      pel_pass = (Some pass_name); pel_internal = internal }

  (** val internal_error : instr_info -> char list -> pp_error_loc **)

  let internal_error ii msg =
    gen_error true (Some ii) None (PPEstring msg)

  (** val unexpected_sopn :
      coq_MSFsize -> 'a1 asmOp -> instr_info -> char list -> 'a1 sopn ->
      pp_error_loc **)

  let unexpected_sopn h h0 ii msg op =
    let err =
      pp_box ((PPEstring msg) :: ((PPEstring
        ('u'::('n'::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('o'::('r'::[])))))))))))))))))))) :: ((PPEstring
        (string_of_sopn h h0 op)) :: [])))
    in
    gen_error true (Some ii) None err

  (** val error : instr_info -> pp_error -> pp_error_loc **)

  let error ii msg =
    gen_error false (Some ii) None msg

  (** val verror :
      bool -> char list -> instr_info -> var_i -> pp_error_loc **)

  let verror internal msg ii v =
    gen_error internal (Some ii) (Some v.v_info)
      (pp_box ((PPEstring msg) :: ((PPEstring (':'::[])) :: ((PPEvar
        v.v_var) :: []))))

  (** val invalid_name : char list -> instr_info -> var_i -> pp_error_loc **)

  let invalid_name category0 ii v =
    verror true
      (append ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::[]))))))))
        (append category0 (' '::('n'::('a'::('m'::('e'::[]))))))) ii v

  (** val invalid_ty : char list -> instr_info -> var_i -> pp_error_loc **)

  let invalid_ty category0 ii v =
    verror true
      (append ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::[]))))))))
        (append category0 (' '::('t'::('y'::('p'::('e'::[]))))))) ii v

  (** val invalid_flag : instr_info -> var_i -> pp_error_loc **)

  let invalid_flag ii v =
    verror false
      ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('n'::('a'::('m'::('e'::(' '::('f'::('o'::('r'::(' '::('r'::('f'::('l'::('a'::('g'::(' '::('('::('c'::('h'::('e'::('c'::('k'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('a'::('t'::('i'::('o'::('n'::('?'::(')'::[]))))))))))))))))))))))))))))))))))))))))))))))
      ii v

  (** val berror : instr_info -> fexpr -> char list -> pp_error_loc **)

  let berror ii e msg =
    gen_error false (Some ii) None
      (pp_vbox
        ((pp_box ((PPEstring
           ('n'::('o'::('t'::(' '::('a'::('b'::('l'::('e'::(' '::('t'::('o'::(' '::('c'::('o'::('m'::('p'::('i'::('l'::('e'::(' '::('t'::('h'::('e'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))))))))) :: ((PPEfexpr
           e) :: []))) :: ((PPEstring msg) :: [])))

  (** val werror : instr_info -> rexpr -> char list -> pp_error_loc **)

  let werror ii e msg =
    gen_error false (Some ii) None
      (pp_vbox
        ((pp_box ((PPEstring
           ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('x'::('p'::('r'::(' '::('f'::('o'::('r'::(' '::('o'::('p'::('r'::('d'::[]))))))))))))))))))))))) :: ((PPErexpr
           e) :: []))) :: ((PPEstring msg) :: [])))
 end

(** val fail : instr_info -> char list -> pp_error_loc **)

let fail ii msg =
  E.error ii
    (pp_box ((PPEstring
      ('s'::('t'::('o'::('r'::('e'::('-'::('l'::('a'::('b'::('e'::('l'::(':'::[]))))))))))))) :: ((PPEstring
      msg) :: [])))

(** val of_var_e :
    stype -> 'a1 coq_ToString -> 'a1 coq_ToIdent -> instr_info -> var_i ->
    (pp_error_loc, 'a1) result **)

let of_var_e t0 tS tI ii v =
  match of_var t0 tS tI v.v_var with
  | Some r -> Ok r
  | None ->
    if eq_op stype_eqType (Obj.magic Var.vtype v.v_var)
         (Obj.magic rtype t0 tS)
    then Error (E.invalid_name tS.category ii v)
    else Error (E.invalid_ty tS.category ii v)

(** val to_reg :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    arch_toIdent -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t option **)

let to_reg arch atoI =
  of_var (Coq_sword arch.reg_size) arch.toS_r atoI.toI_r

(** val to_regx :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    arch_toIdent -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5) regx_t option **)

let to_regx arch atoI =
  of_var (Coq_sword arch.reg_size) arch.toS_rx atoI.toI_rx

(** val to_xreg :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    arch_toIdent -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5) xreg_t option **)

let to_xreg arch atoI =
  of_var (Coq_sword arch.xreg_size) arch.toS_x atoI.toI_x

(** val to_rflag :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    arch_toIdent -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5) rflag_t option **)

let to_rflag arch atoI =
  of_var Coq_sbool arch.toS_f atoI.toI_f

(** val asm_typed_reg_of_var :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    arch_toIdent -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_typed_reg cexec **)

let asm_typed_reg_of_var arch atoI x =
  match to_reg arch atoI x with
  | Some r -> Ok (ARReg r)
  | None ->
    (match to_regx arch atoI x with
     | Some r -> Ok (ARegX r)
     | None ->
       (match to_xreg arch atoI x with
        | Some r -> Ok (AXReg r)
        | None ->
          (match to_rflag arch atoI x with
           | Some f -> Ok (ABReg f)
           | None ->
             Error
               (E.gen_error true None None (PPEstring
                 ('c'::('a'::('n'::(' '::('n'::('o'::('t'::(' '::('m'::('a'::('p'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('t'::('o'::(' '::('a'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[])))))))))))))))))))))))))))))))))))))))

(** val var_of_asm_typed_reg :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    arch_toIdent -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_typed_reg -> Var.var **)

let var_of_asm_typed_reg arch atoI = function
| ARReg r -> to_var (Coq_sword arch.reg_size) arch.toS_r atoI.toI_r r
| ARegX r -> to_var (Coq_sword arch.reg_size) arch.toS_rx atoI.toI_rx r
| AXReg r -> to_var (Coq_sword arch.xreg_size) arch.toS_x atoI.toI_x r
| ABReg r -> to_var Coq_sbool arch.toS_f atoI.toI_f r

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) asm_gen_params =
  instr_info -> fexpr -> ('reg, 'regx, 'xreg, 'rflag, 'cond) cond_t cexec
  (* singleton inductive, whose constructor was Build_asm_gen_params *)

(** val agp_assemble_cond :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) asm_gen_params -> instr_info -> fexpr -> ('a1, 'a2, 'a3,
    'a4, 'a5) cond_t cexec **)

let agp_assemble_cond _ a =
  a

(** val scale_of_z : instr_info -> coq_Z -> nat cexec **)

let scale_of_z ii = function
| Zpos p ->
  (match p with
   | Coq_xI _ ->
     Error
       (E.error ii (PPEstring
         ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('s'::('c'::('a'::('l'::('e'::[])))))))))))))))
   | Coq_xO p0 ->
     (match p0 with
      | Coq_xI _ ->
        Error
          (E.error ii (PPEstring
            ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('s'::('c'::('a'::('l'::('e'::[])))))))))))))))
      | Coq_xO p1 ->
        (match p1 with
         | Coq_xI _ ->
           Error
             (E.error ii (PPEstring
               ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('s'::('c'::('a'::('l'::('e'::[])))))))))))))))
         | Coq_xO p2 ->
           (match p2 with
            | Coq_xH -> Ok (S (S (S O)))
            | _ ->
              Error
                (E.error ii (PPEstring
                  ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('s'::('c'::('a'::('l'::('e'::[]))))))))))))))))
         | Coq_xH -> Ok (S (S O)))
      | Coq_xH -> Ok (S O))
   | Coq_xH -> Ok O)
| _ ->
  Error
    (E.error ii (PPEstring
      ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('s'::('c'::('a'::('l'::('e'::[])))))))))))))))

(** val reg_of_ovar :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> instr_info -> var_i
    option -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t option cexec **)

let reg_of_ovar asm_e ii = function
| Some x0 ->
  (match of_var_e (Coq_sword asm_e._asm._arch_decl.reg_size)
           asm_e._asm._arch_decl.toS_r asm_e._atoI.toI_r ii x0 with
   | Ok x1 -> Ok (Some x1)
   | Error s -> Error s)
| None -> Ok None

(** val assemble_lea :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> instr_info -> lea ->
    (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5) address) result **)

let assemble_lea asm_e ii lea0 =
  match reg_of_ovar asm_e ii lea0.lea_base with
  | Ok x ->
    (match reg_of_ovar asm_e ii lea0.lea_offset with
     | Ok x0 ->
       (match scale_of_z ii lea0.lea_scale with
        | Ok x1 ->
          Ok (Areg { ad_disp =
            (wrepr (coq_Uptr (arch_pd asm_e._asm._arch_decl)) lea0.lea_disp);
            ad_base = x; ad_scale = x1; ad_offset = x0 })
        | Error s -> Error s)
     | Error s -> Error s)
  | Error s -> Error s

(** val addr_of_fexpr :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> Var.var -> instr_info ->
    wsize -> fexpr -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5) address) result **)

let addr_of_fexpr asm_e =
  let is_none = fun m -> match m with
                         | Some _ -> false
                         | None -> true in
  (fun rip ii sz e ->
  if cmp_le wsize_cmp sz (coq_Uptr (arch_pd asm_e._asm._arch_decl))
  then (match mk_lea_rec sz e with
        | Some lea0 ->
          (match lea0.lea_base with
           | Some r ->
             if eq_op Var.var_eqType (Obj.magic r.v_var) (Obj.magic rip)
             then if is_none lea0.lea_offset
                  then Ok (Arip
                         (wrepr (coq_Uptr (arch_pd asm_e._asm._arch_decl))
                           lea0.lea_disp))
                  else let s =
                         E.error ii
                           (pp_box ((PPEstring
                             ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('g'::('l'::('o'::('b'::('a'::('l'::(' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::(' '::(':'::[]))))))))))))))))))))))))) :: ((PPEfexpr
                             e) :: [])))
                       in
                       Error s
             else assemble_lea asm_e ii lea0
           | None -> assemble_lea asm_e ii lea0)
        | None ->
          Error
            (E.error ii
              (pp_box ((PPEstring
                ('n'::('o'::('t'::(' '::('a'::('b'::('l'::('e'::(' '::('t'::('o'::(' '::('a'::('s'::('s'::('e'::('m'::('b'::('l'::('e'::(' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::(' '::(':'::[]))))))))))))))))))))))))))))))) :: ((PPEfexpr
                e) :: [])))))
  else let s =
         E.error ii (PPEstring
           ('B'::('a'::('d'::(' '::('t'::('y'::('p'::('e'::(' '::('f'::('o'::('r'::(' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::[])))))))))))))))))))))
       in
       Error s)

(** val addr_of_xpexpr :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> Var.var -> instr_info ->
    wsize -> var_i -> fexpr -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5)
    address) result **)

let addr_of_xpexpr asm_e rip ii sz v e =
  addr_of_fexpr asm_e rip ii sz (Fapp2 ((Oadd (Op_w sz)), (Fvar v), e))

(** val xreg_of_var :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> instr_info -> var_i ->
    ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg cexec **)

let xreg_of_var asm_e ii x =
  match to_xreg asm_e._asm._arch_decl asm_e._atoI x.v_var with
  | Some r -> Ok (XReg r)
  | None ->
    (match to_reg asm_e._asm._arch_decl asm_e._atoI x.v_var with
     | Some r -> Ok (Arch_decl.Reg r)
     | None ->
       (match to_regx asm_e._asm._arch_decl asm_e._atoI x.v_var with
        | Some r -> Ok (Regx r)
        | None ->
          Error
            (E.verror false
              ('N'::('o'::('t'::(' '::('a'::(' '::('('::('x'::(')'::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[])))))))))))))))))
              ii x)))

(** val assemble_word_load :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> Var.var -> instr_info ->
    wsize -> rexpr -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg) result **)

let assemble_word_load asm_e rip ii sz e = match e with
| Load (sz', v, e') ->
  if eq_op wsize_eqType (Obj.magic sz) (Obj.magic sz')
  then (match addr_of_xpexpr asm_e rip ii
                (coq_Uptr (arch_pd asm_e._asm._arch_decl)) v e' with
        | Ok x -> Ok (Addr x)
        | Error s -> Error s)
  else let s =
         E.werror ii e
           ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('L'::('o'::('a'::('d'::(' '::('s'::('i'::('z'::('e'::[])))))))))))))))))
       in
       Error s
| Rexpr f ->
  (match f with
   | Fvar x -> xreg_of_var asm_e ii x
   | Fapp1 (s, f0) ->
     (match s with
      | Oword_of_int sz' ->
        (match f0 with
         | Fconst z ->
           let w = wrepr sz' z in
           let w1 = sign_extend sz sz' w in
           let w2 = wrepr sz z in
           if eq_op (GRing.ComRing.eqType (word sz)) w1 w2
           then Ok (Imm (sz', w))
           else let s0 =
                  E.werror ii e
                    ('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::[])))))))))))))))))))))
                in
                Error s0
         | _ ->
           Error
             (E.werror ii e
               ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('x'::('p'::('r'::(' '::('f'::('o'::('r'::(' '::('w'::('o'::('r'::('d'::[]))))))))))))))))))))))))
      | _ ->
        Error
          (E.werror ii e
            ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('x'::('p'::('r'::(' '::('f'::('o'::('r'::(' '::('w'::('o'::('r'::('d'::[]))))))))))))))))))))))))
   | _ ->
     Error
       (E.werror ii e
         ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('x'::('p'::('r'::(' '::('f'::('o'::('r'::(' '::('w'::('o'::('r'::('d'::[]))))))))))))))))))))))))

(** val assemble_word :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> addr_kind -> Var.var ->
    instr_info -> wsize -> rexpr -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5)
    asm_arg) result **)

let assemble_word asm_e k rip ii sz e =
  match k with
  | AK_compute ->
    (match e with
     | Load (_, _, _) ->
       let s =
         E.werror ii e
           ('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('r'::('e'::('x'::('p'::('r'::(' '::('f'::('o'::('r'::(' '::('L'::('E'::('A'::[])))))))))))))))))))))
       in
       Error s
     | Rexpr f ->
       (match addr_of_fexpr asm_e rip ii sz f with
        | Ok x -> Ok (Addr x)
        | Error s -> Error s))
  | AK_mem -> assemble_word_load asm_e rip ii sz e

(** val arg_of_rexpr :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) asm_gen_params -> addr_kind -> Var.var -> instr_info ->
    stype -> rexpr -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg) result **)

let arg_of_rexpr asm_e agparams k rip ii ty e =
  match ty with
  | Coq_sbool ->
    (match e with
     | Load (_, _, _) ->
       let s =
         E.werror ii e
           ('n'::('o'::('t'::(' '::('a'::('b'::('l'::('e'::(' '::('t'::('o'::(' '::('a'::('s'::('s'::('e'::('m'::('b'::('l'::('e'::(' '::('a'::(' '::('l'::('o'::('a'::('d'::(' '::('e'::('x'::('p'::('r'::('e'::('s'::('s'::('i'::('o'::('n'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('b'::('o'::('o'::('l'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
       in
       Error s
     | Rexpr f ->
       (match agp_assemble_cond asm_e agparams ii f with
        | Ok x -> Ok (Condt x)
        | Error s -> Error s))
  | Coq_sint ->
    Error
      (E.werror ii e
        ('n'::('o'::('t'::(' '::('a'::('b'::('l'::('e'::(' '::('t'::('o'::(' '::('a'::('s'::('s'::('e'::('m'::('b'::('l'::('e'::(' '::('a'::('n'::(' '::('e'::('x'::('p'::('r'::('e'::('s'::('s'::('i'::('o'::('n'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('i'::('n'::('t'::[])))))))))))))))))))))))))))))))))))))))))))))))
  | Coq_sarr _ ->
    Error
      (E.werror ii e
        ('n'::('o'::('t'::(' '::('a'::('b'::('l'::('e'::(' '::('t'::('o'::(' '::('a'::('s'::('s'::('e'::('m'::('b'::('l'::('e'::(' '::('a'::('n'::(' '::('e'::('x'::('p'::('r'::('e'::('s'::('s'::('i'::('o'::('n'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('a'::('r'::('r'::('a'::('y'::(' '::('_'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
  | Coq_sword sz -> assemble_word asm_e k rip ii sz e

(** val rexpr_of_lexpr : lexpr -> rexpr **)

let rexpr_of_lexpr = function
| Store (s, x, e) -> Load (s, x, e)
| LLvar x -> Rexpr (Fvar x)

type 't nmap = nat -> 't option

(** val nget : 'a1 nmap -> nat -> 'a1 option **)

let nget m =
  m

(** val nset : 'a1 nmap -> nat -> 'a1 -> Equality.sort -> 'a1 option **)

let nset m n t0 x =
  if eq_op nat_eqType x (Obj.magic n) then Some t0 else nget m (Obj.magic x)

(** val nempty : nat -> 'a1 option **)

let nempty _ =
  None

(** val is_implicit :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5) implicit_arg -> rexpr -> bool **)

let is_implicit asm_e i = function
| Load (_, _, _) -> false
| Rexpr f ->
  (match f with
   | Fvar x ->
     eq_op Var.var_eqType (Obj.magic x.v_var)
       (Obj.magic var_of_implicit_arg asm_e._asm._arch_decl asm_e._atoI i)
   | _ -> false)

(** val compile_arg :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ((('a1, 'a2,
    'a3, 'a4, 'a5) Arch_decl.arg_desc * stype) * rexpr) -> ('a1, 'a2, 'a3,
    'a4, 'a5) asm_arg nmap -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg nmap cexec **)

let compile_arg asm_e agparams rip ii ade m =
  let ad = fst ade in
  let e = snd ade in
  (match fst ad with
   | Arch_decl.ADImplicit i ->
     if is_implicit asm_e i e
     then Ok m
     else let s =
            E.internal_error ii
              ('('::('c'::('o'::('m'::('p'::('i'::('l'::('e'::('_'::('a'::('r'::('g'::(')'::(' '::('b'::('a'::('d'::(' '::('i'::('m'::('p'::('l'::('i'::('c'::('i'::('t'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[])))))))))))))))))))))))))))))))))))
          in
          Error s
   | Arch_decl.ADExplicit (k, n, o) ->
     (match arg_of_rexpr asm_e agparams k rip ii (snd ad) e with
      | Ok x ->
        if check_oreg asm_e._asm._arch_decl (Obj.magic o) x
        then (match nget m n with
              | Some a' ->
                if eq_op (asm_arg_eqType asm_e._asm._arch_decl) (Obj.magic x)
                     (Obj.magic a')
                then Ok m
                else Error
                       (E.internal_error ii
                         ('('::('c'::('o'::('m'::('p'::('i'::('l'::('e'::('_'::('a'::('r'::('g'::(')'::(' '::('n'::('o'::('t'::(' '::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('a'::('s'::('m'::('_'::('a'::('r'::('g'::[])))))))))))))))))))))))))))))))))))))
              | None -> Ok (Obj.magic nset m n x))
        else let s =
               E.internal_error ii
                 ('('::('c'::('o'::('m'::('p'::('i'::('l'::('e'::('_'::('a'::('r'::('g'::(')'::(' '::('b'::('a'::('d'::(' '::('f'::('o'::('r'::('c'::('e'::('d'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[])))))))))))))))))))))))))))))))))
             in
             Error s
      | Error s -> Error s))

(** val compile_args :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> (('a1, 'a2,
    'a3, 'a4, 'a5) Arch_decl.arg_desc * stype) list -> rexpr list -> ('a1,
    'a2, 'a3, 'a4, 'a5) asm_arg nmap -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4,
    'a5) asm_arg nmap) result **)

let compile_args asm_e agparams rip ii adts es m =
  foldM (compile_arg asm_e agparams rip ii) m (zip adts es)

(** val compat_imm :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> stype -> Equality.sort
    -> Equality.sort -> bool **)

let compat_imm asm_e ty a' a =
  (||) (eq_op (asm_arg_eqType asm_e._asm._arch_decl) a a')
    (match ty with
     | Coq_sword sz ->
       (match Obj.magic a with
        | Imm (sz1, w1) ->
          (match Obj.magic a' with
           | Imm (sz2, w2) ->
             eq_op (GRing.ComRing.eqType (word sz)) (sign_extend sz sz1 w1)
               (sign_extend sz sz2 w2)
           | _ -> false)
        | _ -> false)
     | _ -> false)

(** val check_sopn_arg :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ('a1, 'a2, 'a3,
    'a4, 'a5) asm_arg list -> rexpr -> (('a1, 'a2, 'a3, 'a4, 'a5)
    Arch_decl.arg_desc * stype) -> bool **)

let check_sopn_arg asm_e agparams rip ii loargs x adt =
  match fst adt with
  | Arch_decl.ADImplicit i -> is_implicit asm_e i x
  | Arch_decl.ADExplicit (k, n, o) ->
    (match onth loargs n with
     | Some a ->
       (match arg_of_rexpr asm_e agparams k rip ii (snd adt) x with
        | Ok a' ->
          (&&) (compat_imm asm_e (snd adt) (Obj.magic a) (Obj.magic a'))
            (check_oreg asm_e._asm._arch_decl (Obj.magic o) a)
        | Error _ -> false)
     | None -> false)

(** val check_sopn_dest :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ('a1, 'a2, 'a3,
    'a4, 'a5) asm_arg list -> rexpr -> (('a1, 'a2, 'a3, 'a4, 'a5)
    Arch_decl.arg_desc * stype) -> bool **)

let check_sopn_dest asm_e agparams rip ii loargs x adt =
  match fst adt with
  | Arch_decl.ADImplicit i -> is_implicit asm_e i x
  | Arch_decl.ADExplicit (_, n, o) ->
    (match onth loargs n with
     | Some a ->
       (match arg_of_rexpr asm_e agparams AK_mem rip ii (snd adt) x with
        | Ok a' ->
          (&&)
            (eq_op (asm_arg_eqType asm_e._asm._arch_decl) (Obj.magic a)
              (Obj.magic a'))
            (check_oreg asm_e._asm._arch_decl (Obj.magic o) a)
        | Error _ -> false)
     | None -> false)

(** val assemble_asm_op_aux :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ('a1, 'a2, 'a3,
    'a4, 'a5, 'a6) asm_op_msb_t -> lexpr list -> rexpr list -> (pp_error_loc,
    ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg list) result **)

let assemble_asm_op_aux asm_e agparams rip ii op outx inx =
  let id = instr_desc asm_e._asm._arch_decl asm_e._asm._asm_op_decl op in
  (match compile_args asm_e agparams rip ii (zip id.id_in id.id_tin) inx
           nempty with
   | Ok x ->
     let eoutx = map rexpr_of_lexpr outx in
     (match compile_args asm_e agparams rip ii (zip id.id_out id.id_tout)
              eoutx x with
      | Ok x0 ->
        (match omap (nget x0) (iota O id.id_nargs) with
         | Some asm_args0 -> Ok asm_args0
         | None ->
           Error
             (E.internal_error ii
               ('c'::('o'::('m'::('p'::('i'::('l'::('e'::('_'::('a'::('r'::('g'::(' '::(':'::(' '::('a'::('s'::('s'::('e'::('r'::('t'::(' '::('f'::('a'::('l'::('s'::('e'::(' '::('n'::('g'::('e'::('t'::[])))))))))))))))))))))))))))))))))
      | Error s -> Error s)
   | Error s -> Error s)

(** val check_sopn_args :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ('a1, 'a2, 'a3,
    'a4, 'a5) asm_arg list -> rexpr list -> (('a1, 'a2, 'a3, 'a4, 'a5)
    Arch_decl.arg_desc * stype) list -> bool **)

let check_sopn_args asm_e agparams rip ii loargs xs adt =
  all2 (check_sopn_arg asm_e agparams rip ii loargs) xs adt

(** val check_sopn_dests :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ('a1, 'a2, 'a3,
    'a4, 'a5) asm_arg list -> lexpr list -> (('a1, 'a2, 'a3, 'a4, 'a5)
    Arch_decl.arg_desc * stype) list -> bool **)

let check_sopn_dests asm_e agparams rip ii loargs outx adt =
  let eoutx = map rexpr_of_lexpr outx in
  all2 (check_sopn_dest asm_e agparams rip ii loargs) eoutx adt

(** val check_arg_kind_no_imm :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5) asm_arg -> arg_kind -> bool **)

let check_arg_kind_no_imm _ a cond =
  match a with
  | Condt _ -> (match cond with
                | CAcond -> true
                | _ -> false)
  | Imm (_, _) -> (match cond with
                   | CAimm _ -> true
                   | _ -> false)
  | Arch_decl.Reg _ -> (match cond with
                        | CAreg -> true
                        | _ -> false)
  | Regx _ -> (match cond with
               | CAregx -> true
               | _ -> false)
  | Addr _ -> (match cond with
               | CAmem _ -> true
               | _ -> false)
  | XReg _ -> (match cond with
               | CAxmm -> true
               | _ -> false)

(** val filter_arg_kinds_no_imm :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5) asm_arg -> arg_kinds -> (unit, arg_kinds) result **)

let filter_arg_kinds_no_imm asm_e a cond =
  let cond' = filter (check_arg_kind_no_imm asm_e a) cond in
  (match cond' with
   | [] -> Error ()
   | _ :: _ -> Ok cond')

(** val filter_args_kinds_no_imm :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5) asm_args -> args_kinds -> args_kinds option **)

let filter_args_kinds_no_imm asm_e args cond =
  match mapM2 () (fun a c -> filter_arg_kinds_no_imm asm_e a c) args cond with
  | Ok cond0 -> Some cond0
  | Error _ -> None

(** val filter_i_args_kinds_no_imm :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> i_args_kinds -> ('a1,
    'a2, 'a3, 'a4, 'a5) asm_args -> i_args_kinds **)

let filter_i_args_kinds_no_imm asm_e cond a =
  pmap (filter_args_kinds_no_imm asm_e a) cond

(** val enforce_imm_arg_kind :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5) asm_arg -> arg_kind -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg option **)

let enforce_imm_arg_kind _ a cond =
  match a with
  | Condt _ -> (match cond with
                | CAcond -> Some a
                | _ -> None)
  | Imm (sz, w) ->
    (match cond with
     | CAimm sz' ->
       let w1 = zero_extend sz' sz w in
       let w2 = sign_extend sz sz' w1 in
       if eq_op (GRing.ComRing.eqType (word sz)) w w2
       then Some (Imm (sz', w1))
       else None
     | _ -> None)
  | Arch_decl.Reg _ -> (match cond with
                        | CAreg -> Some a
                        | _ -> None)
  | Regx _ -> (match cond with
               | CAregx -> Some a
               | _ -> None)
  | Addr _ -> (match cond with
               | CAmem _ -> Some a
               | _ -> None)
  | XReg _ -> (match cond with
               | CAxmm -> Some a
               | _ -> None)

(** val enforce_imm_arg_kinds :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5) asm_arg -> arg_kinds -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg option **)

let enforce_imm_arg_kinds asm_e a cond =
  find_map (enforce_imm_arg_kind asm_e a) cond

(** val enforce_imm_args_kinds :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5) asm_args -> args_kinds -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_args option **)

let enforce_imm_args_kinds asm_e args cond =
  match mapM2 () (fun a c -> o2r () (enforce_imm_arg_kinds asm_e a c)) args
          cond with
  | Ok args0 -> Some args0
  | Error _ -> None

(** val enforce_imm_i_args_kinds :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> i_args_kinds -> ('a1,
    'a2, 'a3, 'a4, 'a5) asm_args -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_args option **)

let enforce_imm_i_args_kinds asm_e cond a =
  find_map (enforce_imm_args_kinds asm_e a) cond

(** val pp_arg_kind : arg_kind -> pp_error **)

let pp_arg_kind = function
| CAcond -> PPEstring ('c'::('o'::('n'::('d'::[]))))
| CAreg -> PPEstring ('r'::('e'::('g'::[])))
| CAregx -> PPEstring ('r'::('e'::('g'::('x'::[]))))
| CAxmm -> PPEstring ('x'::('r'::('e'::('g'::[]))))
| CAmem b ->
  pp_nobox ((PPEstring
    ('m'::('e'::('m'::(' '::('('::('g'::('l'::('o'::('b'::(' '::[]))))))))))) :: ((PPEstring
    (if b then [] else 'n'::('o'::('t'::(' '::[]))))) :: ((PPEstring
    ('a'::('l'::('l'::('o'::('w'::('e'::('d'::(')'::[]))))))))) :: [])))
| CAimm ws ->
  pp_nobox ((PPEstring ('i'::('m'::('m'::(' '::[]))))) :: ((PPEstring
    (string_of_wsize ws)) :: []))

(** val pp_arg_kinds : arg_kind list -> pp_error **)

let pp_arg_kinds cond =
  pp_box
    ((pp_nobox ((PPEstring
       ('['::[])) :: ((pp_list (pp_break_s (';'::[])) pp_arg_kind cond) :: ((PPEstring
       (']'::[])) :: [])))) :: [])

(** val pp_args_kinds : arg_kind list list -> pp_error **)

let pp_args_kinds cond =
  pp_box
    ((pp_nobox ((PPEstring
       ('['::[])) :: ((pp_list (pp_break_s (';'::[])) pp_arg_kinds cond) :: ((PPEstring
       (']'::[])) :: [])))) :: [])

(** val pp_i_args_kinds : arg_kind list list list -> pp_error **)

let pp_i_args_kinds cond =
  pp_vbox ((pp_list PPEbreak pp_args_kinds cond) :: [])

(** val assemble_asm_op :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ('a1, 'a2, 'a3,
    'a4, 'a5, 'a6) asm_op_msb_t -> lexpr list -> rexpr list -> (pp_error_loc,
    'a6 * ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg list) result **)

let assemble_asm_op asm_e agparams rip ii op outx inx =
  let id = instr_desc asm_e._asm._arch_decl asm_e._asm._asm_op_decl op in
  (match assemble_asm_op_aux asm_e agparams rip ii op outx inx with
   | Ok x ->
     let s = id.id_str_jas () in
     let args_kinds0 = filter_i_args_kinds_no_imm asm_e id.id_args_kinds x in
     if negb
          (eq_op (seq_eqType (seq_eqType (seq_eqType arg_kind_eqType)))
            (Obj.magic args_kinds0) (Obj.magic []))
     then (match enforce_imm_i_args_kinds asm_e args_kinds0 x with
           | Some asm_args0 ->
             if (&&)
                  (check_sopn_args asm_e agparams rip ii asm_args0 inx
                    (zip id.id_in id.id_tin))
                  (check_sopn_dests asm_e agparams rip ii asm_args0 outx
                    (zip id.id_out id.id_tout))
             then Ok ((snd op), asm_args0)
             else let s0 =
                    E.internal_error ii
                      ('a'::('s'::('s'::('e'::('m'::('b'::('l'::('e'::('_'::('a'::('s'::('m'::('_'::('o'::('p'::('n'::(':'::(' '::('c'::('a'::('n'::('n'::('o'::('t'::(' '::('c'::('h'::('e'::('c'::('k'::[]))))))))))))))))))))))))))))))
                  in
                  Error s0
           | None ->
             let s0 =
               E.error ii
                 (pp_nobox
                   ((pp_box ((PPEstring
                      ('i'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('i'::('o'::('n'::[])))))))))))) :: ((PPEstring
                      s) :: ((PPEstring
                      ('i'::('s'::(' '::('g'::('i'::('v'::('e'::('n'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('o'::('n'::('e'::(' '::('t'::('o'::('o'::(' '::('l'::('a'::('r'::('g'::('e'::(' '::('i'::('m'::('m'::('e'::('d'::('i'::('a'::('t'::('e'::(' '::('a'::('s'::(' '::('a'::('n'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: [])))) :: (PPEbreak :: (
                   (pp_vbox ((PPEstring
                     ('A'::('l'::('l'::('o'::('w'::('e'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('t'::('h'::('e'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('('::('e'::('x'::('c'::('e'::('p'::('t'::(' '::('o'::('n'::(' '::('i'::('m'::('m'::('e'::('d'::('i'::('a'::('t'::('e'::(' '::('s'::('i'::('z'::('e'::('s'::(')'::(' '::('a'::('r'::('e'::(':'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: (
                     (pp_nobox ((PPEstring
                       (' '::(' '::[]))) :: ((pp_vbox
                                               ((pp_i_args_kinds args_kinds0) :: [])) :: []))) :: ((PPEstring
                     ('A'::('l'::('l'::(' '::('a'::('l'::('l'::('o'::('w'::('e'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('('::('r'::('e'::('g'::('a'::('r'::('d'::('l'::('e'::('s'::('s'::(' '::('o'::('f'::(' '::('t'::('h'::('e'::(' '::('i'::('n'::('p'::('u'::('t'::(')'::(' '::('a'::('r'::('e'::(':'::[])))))))))))))))))))))))))))))))))))))))))))))))) :: (
                     (pp_nobox ((PPEstring
                       (' '::(' '::[]))) :: ((pp_vbox
                                               ((pp_i_args_kinds
                                                  id.id_args_kinds) :: [])) :: []))) :: []))))) :: []))))
             in
             Error s0)
     else let s0 =
            E.error ii
              (pp_nobox
                ((pp_box ((PPEstring
                   ('i'::('n'::('s'::('t'::('r'::('u'::('c'::('t'::('i'::('o'::('n'::[])))))))))))) :: ((PPEstring
                   s) :: ((PPEstring
                   ('i'::('s'::(' '::('g'::('i'::('v'::('e'::('n'::(' '::('i'::('n'::('c'::('o'::('m'::('p'::('a'::('t'::('i'::('b'::('l'::('e'::(' '::('a'::('r'::('g'::('s'::('.'::[])))))))))))))))))))))))))))) :: [])))) :: (PPEbreak :: (
                (pp_vbox ((PPEstring
                  ('A'::('l'::('l'::('o'::('w'::('e'::('d'::(' '::('a'::('r'::('g'::('s'::(' '::('a'::('r'::('e'::(':'::[])))))))))))))))))) :: (
                  (pp_nobox ((PPEstring
                    (' '::(' '::[]))) :: ((pp_i_args_kinds id.id_args_kinds) :: []))) :: []))) :: []))))
          in
          Error s0
   | Error s -> Error s)

(** val assemble_asm_args :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ((('a1, 'a2,
    'a3, 'a4, 'a5, 'a6) asm_op_msb_t * lexpr list) * rexpr list) ->
    (pp_error_loc, 'a6 * ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg list) result **)

let assemble_asm_args asm_e agparams rip ii = function
| (y, rs) ->
  let (op, ls) = y in assemble_asm_op asm_e agparams rip ii op ls rs

(** val assemble_sopn :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ('a1, 'a2, 'a3,
    'a4, 'a5, 'a6, 'a7) extended_op sopn -> lexpr list -> rexpr list ->
    (pp_error_loc, ('a6 * ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg list) list) result **)

let assemble_sopn asm_e agparams rip ii op outx inx =
  match op with
  | Oasm a ->
    (match a with
     | BaseOp op0 ->
       (match assemble_asm_op asm_e agparams rip ii op0 outx inx with
        | Ok x -> Ok (x :: [])
        | Error s -> Error s)
     | ExtOp op0 ->
       (match asm_e.to_asm ii op0 outx inx with
        | Ok x -> mapM (assemble_asm_args asm_e agparams rip ii) x
        | Error s -> Error s))
  | _ ->
    Error
      (E.unexpected_sopn (arch_msfsz asm_e._asm._arch_decl) (asm_opI asm_e)
        ii
        ('a'::('s'::('s'::('e'::('m'::('b'::('l'::('e'::('_'::('s'::('o'::('p'::('n'::(':'::[]))))))))))))))
        op)

(** val is_not_app1 : rexpr -> bool **)

let is_not_app1 = function
| Load (_, _, _) -> true
| Rexpr f -> (match f with
              | Fapp1 (_, _) -> false
              | _ -> true)

(** val assemble_i :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) asm_gen_params -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5,
    'a6, 'a7) extended_op linstr -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_i list
    cexec **)

let assemble_i asm_e agparams rip i =
  let { li_ii = ii; li_i = ir } = i in
  let mk = fun i0 -> { asmi_ii = ii; asmi_i = i0 } in
  (match ir with
   | Lopn (ds, op, es) ->
     (match assemble_sopn asm_e agparams rip ii op ds es with
      | Ok x -> Ok (map (fun x0 -> mk (AsmOp ((fst x0), (snd x0)))) x)
      | Error s -> Error s)
   | Lsyscall o -> Ok ((mk (SysCall o)) :: [])
   | Lcall (o, l) ->
     (match o with
      | Some r ->
        (match to_reg asm_e._asm._arch_decl asm_e._atoI r.v_var with
         | Some r0 -> Ok ((mk (JAL (r0, l))) :: [])
         | None ->
           let s =
             E.verror true
               ('N'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[]))))))))))))))
               ii r
           in
           Error s)
      | None -> Ok ((mk (CALL l)) :: []))
   | Lret -> Ok ((mk POPPC) :: [])
   | Lalign -> Ok ((mk ALIGN) :: [])
   | Llabel (k, lbl) -> Ok ((mk (LABEL (k, lbl))) :: [])
   | Lgoto lbl -> Ok ((mk (JMP lbl)) :: [])
   | Ligoto e ->
     if is_not_app1 e
     then (match assemble_word asm_e AK_mem rip ii
                   (coq_Uptr (arch_pd asm_e._asm._arch_decl)) e with
           | Ok x -> Ok ((mk (JMPI x)) :: [])
           | Error s -> Error s)
     else let s =
            E.werror ii e
              ('L'::('i'::('g'::('o'::('t'::('o'::('/'::('J'::('M'::('P'::('I'::[])))))))))))
          in
          Error s
   | LstoreLabel (x, lbl) ->
     (match of_var (Coq_sword asm_e._asm._arch_decl.reg_size)
              asm_e._asm._arch_decl.toS_r asm_e._atoI.toI_r x with
      | Some r -> Ok ((mk (STORELABEL (r, lbl))) :: [])
      | None ->
        let s = fail ii ('b'::('a'::('d'::(' '::('v'::('a'::('r'::[]))))))) in
        Error s)
   | Lcond (e, l) ->
     (match agp_assemble_cond asm_e agparams ii e with
      | Ok x -> Ok ((mk (Jcc (l, x))) :: [])
      | Error s -> Error s))

(** val assemble_c :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5, 'a6, 'a7) asm_gen_params -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5,
    'a6, 'a7) extended_op lcmd -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_i list
    cexec **)

let assemble_c asm_e agparams rip lc =
  match mapM (assemble_i asm_e agparams rip) lc with
  | Ok x -> Ok (flatten x)
  | Error s -> Error s

(** val is_typed_reg :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> Var.var -> bool **)

let is_typed_reg asm_e x =
  (&&)
    (negb (eq_op stype_eqType (Obj.magic Var.vtype x) (Obj.magic Coq_sbool)))
    (is_ok (asm_typed_reg_of_var asm_e._asm._arch_decl asm_e._atoI x))

(** val typed_reg_of_vari :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> var_i -> ('a1, 'a2, 'a3,
    'a4, 'a5) asm_typed_reg cexec **)

let typed_reg_of_vari asm_e xi =
  let { v_var = x; v_info = _ } = xi in
  asm_typed_reg_of_var asm_e._asm._arch_decl asm_e._atoI x

(** val assemble_fd :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5) calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
    asm_gen_params -> Var.var -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6,
    'a7) extended_op lfundef -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_fundef) result **)

let assemble_fd asm_e call_conv agparams rip rsp fd =
  match assemble_c asm_e agparams rip fd.lfd_body with
  | Ok x ->
    if negb
         (in_mem (Obj.magic rsp)
           (mem (seq_predType Var.var_eqType)
             (Obj.magic map (fun v -> v.v_var) fd.lfd_arg)))
    then if all (is_typed_reg asm_e) fd.lfd_callee_saved
         then (match mapM (typed_reg_of_vari asm_e) fd.lfd_arg with
               | Ok x0 ->
                 (match mapM (typed_reg_of_vari asm_e) fd.lfd_res with
                  | Ok x1 ->
                    let fd0 = { asm_fd_align = fd.lfd_align; asm_fd_arg = x0;
                      asm_fd_body = x; asm_fd_res = x1; asm_fd_export =
                      fd.lfd_export; asm_fd_total_stack =
                      (lfd_total_stack (asm_opI asm_e) fd) }
                    in
                    if check_call_conv asm_e._asm._arch_decl
                         asm_e._asm._asm_op_decl call_conv fd0
                    then Ok fd0
                    else let s =
                           E.gen_error true None None (PPEstring
                             ('e'::('x'::('p'::('o'::('r'::('t'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('s'::('p'::('e'::('c'::('t'::(' '::('t'::('h'::('e'::(' '::('c'::('a'::('l'::('l'::('i'::('n'::('g'::(' '::('c'::('o'::('n'::('v'::('e'::('n'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                         in
                         Error s
                  | Error s -> Error s)
               | Error s -> Error s)
         else let s =
                E.gen_error true None None (PPEstring
                  ('S'::('a'::('v'::('e'::('d'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::[])))))))))))))))))))))))))))))))))
              in
              Error s
    else let s =
           E.gen_error true None None (PPEstring
             ('S'::('t'::('a'::('c'::('k'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::(' '::('i'::('s'::(' '::('a'::('n'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::[])))))))))))))))))))))))))))))
         in
         Error s
  | Error s -> Error s

(** val assemble_prog :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4,
    'a5) calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
    asm_gen_params -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) extended_op lprog
    -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_prog cexec **)

let assemble_prog asm_e call_conv agparams p =
  let rip = mk_ptr asm_e._asm._arch_decl p.lp_rip in
  let rsp = mk_ptr asm_e._asm._arch_decl p.lp_rsp in
  if (&&)
       (eq_op
         (option_eqType (ceqT_eqType asm_e._asm._arch_decl.toS_r._finC._eqC))
         (Obj.magic to_reg asm_e._asm._arch_decl asm_e._atoI rip)
         (Obj.magic None))
       (eq_op
         (option_eqType (ceqT_eqType asm_e._asm._arch_decl.toS_rx._finC._eqC))
         (Obj.magic to_regx asm_e._asm._arch_decl asm_e._atoI rip)
         (Obj.magic None))
  then if eq_op
            (option_eqType
              (ceqT_eqType asm_e._asm._arch_decl.toS_r._finC._eqC))
            (Obj.magic asm_e._atoI.toI_r.of_ident p.lp_rsp)
            (Obj.magic (Some asm_e._asm._arch_decl.ad_rsp))
       then (match map_cfprog_gen (fun l -> l.lfd_info)
                     (assemble_fd asm_e call_conv agparams rip rsp) p.lp_funcs with
             | Ok x -> Ok { asm_globs = p.lp_globs; asm_funcs = x }
             | Error s -> Error s)
       else let s =
              E.gen_error true None None (PPEstring
                ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('R'::('S'::('P'::[]))))))))))))
            in
            Error s
  else let s =
         E.gen_error true None None (PPEstring
           ('I'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('R'::('I'::('P'::[]))))))))))))
       in
       Error s

(** val vflags :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    arch_toIdent -> SvExtra.Sv.t **)

let vflags ad atoI =
  SvExtra.sv_of_list (Obj.magic to_var Coq_sbool ad.toS_f atoI.toI_f)
    (rflags ad)

(** val all_vars :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    arch_toIdent -> SvExtra.Sv.t **)

let all_vars ad atoI =
  SvExtra.Sv.union
    (SvExtra.sv_of_list
      (Obj.magic to_var (Coq_sword ad.reg_size) ad.toS_r atoI.toI_r)
      (registers ad))
    (SvExtra.Sv.union
      (SvExtra.sv_of_list
        (Obj.magic to_var (Coq_sword ad.reg_size) ad.toS_rx atoI.toI_rx)
        (registerxs ad))
      (SvExtra.Sv.union
        (SvExtra.sv_of_list
          (Obj.magic to_var (Coq_sword ad.xreg_size) ad.toS_x atoI.toI_x)
          (xregisters ad)) (vflags ad atoI)))

(** val ovm_i :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    arch_toIdent -> ('a1, 'a2, 'a3, 'a4, 'a5) calling_convention ->
    one_varmap_info **)

let ovm_i ad atoI call_conv =
  { syscall_sig = (fun o ->
    let sig0 = syscall_sig_s (arch_pd ad) o in
    { scs_vin =
    (map (to_var (Coq_sword ad.reg_size) ad.toS_r atoI.toI_r)
      (take (size sig0.scs_tin) call_conv.call_reg_args)); scs_vout =
    (map (to_var (Coq_sword ad.reg_size) ad.toS_r atoI.toI_r)
      (take (size sig0.scs_tout) call_conv.call_reg_ret)) });
    One_varmap.all_vars = (all_vars ad atoI); callee_saved =
    (SvExtra.sv_of_list (Obj.magic var_of_asm_typed_reg ad atoI)
      call_conv.Arch_decl.callee_saved); One_varmap.vflags =
    (vflags ad atoI) }
