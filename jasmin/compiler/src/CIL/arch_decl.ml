open BinNums
open Bool
open Datatypes
open Eqtype
open Expr
open Flag_combination
open Label
open Sem_type
open Seq
open Sopn
open Ssralg
open Ssrbool
open Ssrnat
open Strings
open Type
open Utils0
open Var0
open Word0
open Word_ssrZ
open Wsize

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 't coq_ToString = { category : char list; _finC : 't finTypeC;
                         to_string : ('t -> char list) }

(** val category : stype -> 'a1 coq_ToString -> char list **)

let category _ toString =
  toString.category

(** val _finC : stype -> 'a1 coq_ToString -> 'a1 finTypeC **)

let _finC _ toString =
  toString._finC

(** val to_string : stype -> 'a1 coq_ToString -> 'a1 -> char list **)

let to_string _ toString =
  toString.to_string

(** val rtype : stype -> 'a1 coq_ToString -> stype **)

let rtype t _ =
  t

type ('reg, 'regx, 'xreg, 'rflag, 'cond) arch_decl = { reg_size : wsize;
                                                       xreg_size : wsize;
                                                       cond_eqC : 'cond
                                                                  eqTypeC;
                                                       toS_r : 'reg
                                                               coq_ToString;
                                                       toS_rx : 'regx
                                                                coq_ToString;
                                                       toS_x : 'xreg
                                                               coq_ToString;
                                                       toS_f : 'rflag
                                                               coq_ToString;
                                                       ad_rsp : 'reg;
                                                       ad_fcp : coq_FlagCombinationParams }

(** val reg_size : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> wsize **)

let reg_size arch_decl0 =
  arch_decl0.reg_size

(** val xreg_size : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> wsize **)

let xreg_size arch_decl0 =
  arch_decl0.xreg_size

(** val cond_eqC : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> 'a5 eqTypeC **)

let cond_eqC arch_decl0 =
  arch_decl0.cond_eqC

(** val toS_r : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> 'a1 coq_ToString **)

let toS_r arch_decl0 =
  arch_decl0.toS_r

(** val toS_rx : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> 'a2 coq_ToString **)

let toS_rx arch_decl0 =
  arch_decl0.toS_rx

(** val toS_x : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> 'a3 coq_ToString **)

let toS_x arch_decl0 =
  arch_decl0.toS_x

(** val toS_f : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> 'a4 coq_ToString **)

let toS_f arch_decl0 =
  arch_decl0.toS_f

(** val ad_rsp : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> 'a1 **)

let ad_rsp arch_decl0 =
  arch_decl0.ad_rsp

(** val ad_fcp :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> coq_FlagCombinationParams **)

let ad_fcp arch_decl0 =
  arch_decl0.ad_fcp

(** val arch_pd : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> coq_PointerData **)

let arch_pd h =
  h.reg_size

(** val arch_msfsz : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> coq_MSFsize **)

let arch_msfsz h =
  h.reg_size

(** val mk_ptr :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> Ident.Ident.ident -> Var.var **)

let mk_ptr h name =
  { Var.vtype = (Coq_sword (coq_Uptr (arch_pd h))); Var.vname = name }

type ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_t = 'reg

type ('reg, 'regx, 'xreg, 'rflag, 'cond) regx_t = 'regx

type ('reg, 'regx, 'xreg, 'rflag, 'cond) xreg_t = 'xreg

type ('reg, 'regx, 'xreg, 'rflag, 'cond) rflag_t = 'rflag

type ('reg, 'regx, 'xreg, 'rflag, 'cond) cond_t = 'cond

(** val sreg : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> stype **)

let sreg arch =
  Coq_sword arch.reg_size

type ('reg, 'regx, 'xreg, 'rflag, 'cond) wreg = sem_t

(** val sxreg : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> stype **)

let sxreg arch =
  Coq_sword arch.xreg_size

type ('reg, 'regx, 'xreg, 'rflag, 'cond) wxreg = sem_t

type ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_address = { ad_disp : GRing.ComRing.sort;
                                                         ad_base : ('reg,
                                                                   'regx,
                                                                   'xreg,
                                                                   'rflag,
                                                                   'cond)
                                                                   reg_t
                                                                   option;
                                                         ad_scale : nat;
                                                         ad_offset : 
                                                         ('reg, 'regx, 'xreg,
                                                         'rflag, 'cond) reg_t
                                                         option }

(** val ad_disp :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    reg_address -> GRing.ComRing.sort **)

let ad_disp _ r =
  r.ad_disp

(** val ad_base :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    reg_address -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t option **)

let ad_base _ r =
  r.ad_base

(** val ad_scale :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    reg_address -> nat **)

let ad_scale _ r =
  r.ad_scale

(** val ad_offset :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    reg_address -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t option **)

let ad_offset _ r =
  r.ad_offset

type ('reg, 'regx, 'xreg, 'rflag, 'cond) address =
| Areg of ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_address
| Arip of GRing.ComRing.sort

(** val oeq_reg :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t
    option -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t option -> bool **)

let oeq_reg arch x y =
  eq_op (option_eqType (ceqT_eqType arch.toS_r._finC._eqC)) (Obj.magic x)
    (Obj.magic y)

(** val reg_address_beq :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    reg_address -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_address -> bool **)

let reg_address_beq arch addr1 addr2 =
  let { ad_disp = d1; ad_base = b1; ad_scale = s1; ad_offset = o1 } = addr1 in
  let { ad_disp = d2; ad_base = b2; ad_scale = s2; ad_offset = o2 } = addr2 in
  (&&) (eq_op (GRing.ComRing.eqType (word (coq_Uptr (arch_pd arch)))) d1 d2)
    ((&&) (oeq_reg arch b1 b2)
      ((&&) (eq_op nat_eqType (Obj.magic s1) (Obj.magic s2))
        (oeq_reg arch o1 o2)))

(** val reg_address_eq_axiom :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    reg_address Equality.axiom **)

let reg_address_eq_axiom arch _top_assumption_ =
  let _evar_0_ = fun d1 b1 s1 o1 __top_assumption_ ->
    let _evar_0_ = fun d2 b2 s2 o2 ->
      iffP
        (reg_address_beq arch { ad_disp = d1; ad_base = b1; ad_scale = s1;
          ad_offset = o1 } { ad_disp = d2; ad_base = b2; ad_scale = s2;
          ad_offset = o2 })
        (if reg_address_beq arch { ad_disp = d1; ad_base = b1; ad_scale = s1;
              ad_offset = o1 } { ad_disp = d2; ad_base = b2; ad_scale = s2;
              ad_offset = o2 }
         then ReflectT
         else ReflectF)
    in
    let { ad_disp = ad_disp0; ad_base = ad_base0; ad_scale = ad_scale0;
      ad_offset = ad_offset0 } = __top_assumption_
    in
    _evar_0_ ad_disp0 ad_base0 ad_scale0 ad_offset0
  in
  let { ad_disp = ad_disp0; ad_base = ad_base0; ad_scale = ad_scale0;
    ad_offset = ad_offset0 } = _top_assumption_
  in
  _evar_0_ ad_disp0 ad_base0 ad_scale0 ad_offset0

(** val reg_address_eqMixin :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    reg_address Equality.mixin_of **)

let reg_address_eqMixin arch =
  { Equality.op = (reg_address_beq arch); Equality.mixin_of__1 =
    (reg_address_eq_axiom arch) }

(** val reg_address_eqType :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> Equality.coq_type **)

let reg_address_eqType arch =
  Obj.magic reg_address_eqMixin arch

(** val address_beq :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) address
    -> ('a1, 'a2, 'a3, 'a4, 'a5) address -> bool **)

let address_beq arch addr1 addr2 =
  match addr1 with
  | Areg ra1 ->
    (match addr2 with
     | Areg ra2 ->
       eq_op (reg_address_eqType arch) (Obj.magic ra1) (Obj.magic ra2)
     | Arip _ -> false)
  | Arip p1 ->
    (match addr2 with
     | Areg _ -> false
     | Arip p2 ->
       eq_op (GRing.ComRing.eqType (word (coq_Uptr (arch_pd arch)))) p1 p2)

(** val address_eq_axiom :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) address
    Equality.axiom **)

let address_eq_axiom arch _top_assumption_ =
  let _evar_0_ = fun _r_ __top_assumption_ ->
    let _evar_0_ = fun _r1_ ->
      reflect_inj (reg_address_eqType arch) (Obj.magic (fun x -> Areg x)) _r_
        _r1_ (eqP (reg_address_eqType arch) _r_ _r1_)
    in
    let _evar_0_0 = fun _ -> ReflectF in
    (match __top_assumption_ with
     | Areg r -> Obj.magic _evar_0_ r
     | Arip s -> _evar_0_0 s)
  in
  let _evar_0_0 = fun _s_ __top_assumption_ ->
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = fun _s1_ ->
      reflect_inj (GRing.ComRing.eqType (word arch.reg_size)) (fun x -> Arip
        x) _s_ _s1_ (eqP (GRing.ComRing.eqType (word arch.reg_size)) _s_ _s1_)
    in
    (match __top_assumption_ with
     | Areg r -> _evar_0_0 r
     | Arip s -> _evar_0_1 s)
  in
  (match _top_assumption_ with
   | Areg r -> Obj.magic _evar_0_ r
   | Arip s -> _evar_0_0 s)

(** val address_eqMixin :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) address
    Equality.mixin_of **)

let address_eqMixin arch =
  { Equality.op = (address_beq arch); Equality.mixin_of__1 =
    (address_eq_axiom arch) }

(** val address_eqType :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> Equality.coq_type **)

let address_eqType arch =
  Obj.magic address_eqMixin arch

type ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_arg =
| Condt of ('reg, 'regx, 'xreg, 'rflag, 'cond) cond_t
| Imm of wsize * GRing.ComRing.sort
| Reg of ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_t
| Regx of ('reg, 'regx, 'xreg, 'rflag, 'cond) regx_t
| Addr of ('reg, 'regx, 'xreg, 'rflag, 'cond) address
| XReg of ('reg, 'regx, 'xreg, 'rflag, 'cond) xreg_t

type ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_args =
  ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_arg list

(** val is_Condt :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg
    -> ('a1, 'a2, 'a3, 'a4, 'a5) cond_t option **)

let is_Condt _ = function
| Condt c -> Some c
| _ -> None

(** val asm_arg_beq :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg
    -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg -> bool **)

let asm_arg_beq arch a1 a2 =
  match a1 with
  | Condt t1 ->
    (match a2 with
     | Condt t2 ->
       eq_op (ceqT_eqType arch.cond_eqC) (Obj.magic t1) (Obj.magic t2)
     | _ -> false)
  | Imm (sz1, w1) ->
    (match a2 with
     | Imm (sz2, w2) ->
       (&&) (eq_op wsize_eqType (Obj.magic sz1) (Obj.magic sz2))
         (eq_op coq_Z_eqType (Obj.magic wunsigned sz1 w1)
           (Obj.magic wunsigned sz2 w2))
     | _ -> false)
  | Reg r1 ->
    (match a2 with
     | Reg r2 ->
       eq_op (ceqT_eqType arch.toS_r._finC._eqC) (Obj.magic r1) (Obj.magic r2)
     | _ -> false)
  | Regx r1 ->
    (match a2 with
     | Regx r2 ->
       eq_op (ceqT_eqType arch.toS_rx._finC._eqC) (Obj.magic r1)
         (Obj.magic r2)
     | _ -> false)
  | Addr a3 ->
    (match a2 with
     | Addr a4 -> eq_op (address_eqType arch) (Obj.magic a3) (Obj.magic a4)
     | _ -> false)
  | XReg r1 ->
    (match a2 with
     | XReg r2 ->
       eq_op (ceqT_eqType arch.toS_x._finC._eqC) (Obj.magic r1) (Obj.magic r2)
     | _ -> false)

(** val asm_arg_eq_axiom :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg
    Equality.axiom **)

let asm_arg_eq_axiom arch _top_assumption_ =
  let _evar_0_ = fun t1 __top_assumption_ ->
    let _evar_0_ = fun t2 ->
      reflect_inj (ceqT_eqType arch.cond_eqC) (fun x -> Condt x) t1 t2
        (eqP (ceqT_eqType arch.cond_eqC) t1 t2)
    in
    let _evar_0_0 = fun _ _ -> ReflectF in
    let _evar_0_1 = fun _ -> ReflectF in
    let _evar_0_2 = fun _ -> ReflectF in
    let _evar_0_3 = fun _ -> ReflectF in
    let _evar_0_4 = fun _ -> ReflectF in
    (match __top_assumption_ with
     | Condt c -> _evar_0_ c
     | Imm (ws, s) -> _evar_0_0 ws s
     | Reg r -> _evar_0_1 r
     | Regx r -> _evar_0_2 r
     | Addr a -> _evar_0_3 a
     | XReg x -> _evar_0_4 x)
  in
  let _evar_0_0 = fun sz1 w1 __top_assumption_ ->
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = fun sz2 w2 ->
      iffP
        ((&&) (eq_op wsize_eqType (Obj.magic sz1) (Obj.magic sz2))
          (eq_op coq_Z_eqType (Obj.magic wunsigned sz1 w1)
            (Obj.magic wunsigned sz2 w2)))
        (if (&&) (eq_op wsize_eqType (Obj.magic sz1) (Obj.magic sz2))
              (eq_op coq_Z_eqType (Obj.magic wunsigned sz1 w1)
                (Obj.magic wunsigned sz2 w2))
         then ReflectT
         else ReflectF)
    in
    let _evar_0_2 = fun _ -> ReflectF in
    let _evar_0_3 = fun _ -> ReflectF in
    let _evar_0_4 = fun _ -> ReflectF in
    let _evar_0_5 = fun _ -> ReflectF in
    (match __top_assumption_ with
     | Condt c -> _evar_0_0 c
     | Imm (ws, s) -> _evar_0_1 ws s
     | Reg r -> _evar_0_2 r
     | Regx r -> _evar_0_3 r
     | Addr a -> _evar_0_4 a
     | XReg x -> _evar_0_5 x)
  in
  let _evar_0_1 = fun r1 __top_assumption_ ->
    let _evar_0_1 = fun _ -> ReflectF in
    let _evar_0_2 = fun _ _ -> ReflectF in
    let _evar_0_3 = fun r2 ->
      reflect_inj (ceqT_eqType arch.toS_r._finC._eqC) (fun x -> Reg x) r1 r2
        (eqP (ceqT_eqType arch.toS_r._finC._eqC) r1 r2)
    in
    let _evar_0_4 = fun _ -> ReflectF in
    let _evar_0_5 = fun _ -> ReflectF in
    let _evar_0_6 = fun _ -> ReflectF in
    (match __top_assumption_ with
     | Condt c -> _evar_0_1 c
     | Imm (ws, s) -> _evar_0_2 ws s
     | Reg r -> _evar_0_3 r
     | Regx r -> _evar_0_4 r
     | Addr a -> _evar_0_5 a
     | XReg x -> _evar_0_6 x)
  in
  let _evar_0_2 = fun r1 __top_assumption_ ->
    let _evar_0_2 = fun _ -> ReflectF in
    let _evar_0_3 = fun _ _ -> ReflectF in
    let _evar_0_4 = fun _ -> ReflectF in
    let _evar_0_5 = fun r2 ->
      reflect_inj (ceqT_eqType arch.toS_rx._finC._eqC) (fun x -> Regx x) r1
        r2 (eqP (ceqT_eqType arch.toS_rx._finC._eqC) r1 r2)
    in
    let _evar_0_6 = fun _ -> ReflectF in
    let _evar_0_7 = fun _ -> ReflectF in
    (match __top_assumption_ with
     | Condt c -> _evar_0_2 c
     | Imm (ws, s) -> _evar_0_3 ws s
     | Reg r -> _evar_0_4 r
     | Regx r -> _evar_0_5 r
     | Addr a -> _evar_0_6 a
     | XReg x -> _evar_0_7 x)
  in
  let _evar_0_3 = fun a1 __top_assumption_ ->
    let _evar_0_3 = fun _ -> ReflectF in
    let _evar_0_4 = fun _ _ -> ReflectF in
    let _evar_0_5 = fun _ -> ReflectF in
    let _evar_0_6 = fun _ -> ReflectF in
    let _evar_0_7 = fun a2 ->
      reflect_inj (address_eqType arch) (Obj.magic (fun x -> Addr x)) a1 a2
        (eqP (address_eqType arch) a1 a2)
    in
    let _evar_0_8 = fun _ -> ReflectF in
    (match __top_assumption_ with
     | Condt c -> _evar_0_3 c
     | Imm (ws, s) -> _evar_0_4 ws s
     | Reg r -> _evar_0_5 r
     | Regx r -> _evar_0_6 r
     | Addr a -> Obj.magic _evar_0_7 a
     | XReg x -> _evar_0_8 x)
  in
  let _evar_0_4 = fun xr1 __top_assumption_ ->
    let _evar_0_4 = fun _ -> ReflectF in
    let _evar_0_5 = fun _ _ -> ReflectF in
    let _evar_0_6 = fun _ -> ReflectF in
    let _evar_0_7 = fun _ -> ReflectF in
    let _evar_0_8 = fun _ -> ReflectF in
    let _evar_0_9 = fun xr2 ->
      reflect_inj (ceqT_eqType arch.toS_x._finC._eqC) (fun x -> XReg x) xr1
        xr2 (eqP (ceqT_eqType arch.toS_x._finC._eqC) xr1 xr2)
    in
    (match __top_assumption_ with
     | Condt c -> _evar_0_4 c
     | Imm (ws, s) -> _evar_0_5 ws s
     | Reg r -> _evar_0_6 r
     | Regx r -> _evar_0_7 r
     | Addr a -> _evar_0_8 a
     | XReg x -> _evar_0_9 x)
  in
  (match _top_assumption_ with
   | Condt c -> Obj.magic _evar_0_ c
   | Imm (ws, s) -> _evar_0_0 ws s
   | Reg r -> Obj.magic _evar_0_1 r
   | Regx r -> Obj.magic _evar_0_2 r
   | Addr a -> Obj.magic _evar_0_3 a
   | XReg x -> Obj.magic _evar_0_4 x)

(** val asm_arg_eqMixin :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg
    Equality.mixin_of **)

let asm_arg_eqMixin arch =
  { Equality.op = (asm_arg_beq arch); Equality.mixin_of__1 =
    (asm_arg_eq_axiom arch) }

(** val asm_arg_eqType :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> Equality.coq_type **)

let asm_arg_eqType arch =
  Obj.magic asm_arg_eqMixin arch

type msb_flag =
| MSB_CLEAR
| MSB_MERGE

(** val msb_flag_beq : msb_flag -> msb_flag -> bool **)

let msb_flag_beq x y =
  match x with
  | MSB_CLEAR -> (match y with
                  | MSB_CLEAR -> true
                  | MSB_MERGE -> false)
  | MSB_MERGE -> (match y with
                  | MSB_CLEAR -> false
                  | MSB_MERGE -> true)

(** val msb_flag_eq_dec : msb_flag -> msb_flag -> bool **)

let msb_flag_eq_dec x y =
  let b = msb_flag_beq x y in if b then true else false

(** val msb_flag_eq_axiom : msb_flag Equality.axiom **)

let msb_flag_eq_axiom =
  eq_axiom_of_scheme msb_flag_beq

(** val msb_flag_eqMixin : msb_flag Equality.mixin_of **)

let msb_flag_eqMixin =
  { Equality.op = msb_flag_beq; Equality.mixin_of__1 = msb_flag_eq_axiom }

(** val msb_flag_eqType : Equality.coq_type **)

let msb_flag_eqType =
  Obj.magic msb_flag_eqMixin

type ('reg, 'regx, 'xreg, 'rflag, 'cond) implicit_arg =
| IArflag of ('reg, 'regx, 'xreg, 'rflag, 'cond) rflag_t
| IAreg of ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_t

(** val implicit_arg_beq :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    implicit_arg -> ('a1, 'a2, 'a3, 'a4, 'a5) implicit_arg -> bool **)

let implicit_arg_beq arch i1 i2 =
  match i1 with
  | IArflag f1 ->
    (match i2 with
     | IArflag f2 ->
       eq_op (ceqT_eqType arch.toS_f._finC._eqC) (Obj.magic f1) (Obj.magic f2)
     | IAreg _ -> false)
  | IAreg r1 ->
    (match i2 with
     | IArflag _ -> false
     | IAreg r2 ->
       eq_op (ceqT_eqType arch.toS_r._finC._eqC) (Obj.magic r1) (Obj.magic r2))

(** val implicit_arg_eq_axiom :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    implicit_arg Equality.axiom **)

let implicit_arg_eq_axiom arch _top_assumption_ =
  let _evar_0_ = fun _r_ __top_assumption_ ->
    let _evar_0_ = fun _r1_ ->
      reflect_inj (ceqT_eqType arch.toS_f._finC._eqC) (fun x -> IArflag x)
        _r_ _r1_ (eqP (ceqT_eqType arch.toS_f._finC._eqC) _r_ _r1_)
    in
    let _evar_0_0 = fun _ -> ReflectF in
    (match __top_assumption_ with
     | IArflag r -> _evar_0_ r
     | IAreg r -> _evar_0_0 r)
  in
  let _evar_0_0 = fun _r_ __top_assumption_ ->
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = fun _r1_ ->
      reflect_inj (ceqT_eqType arch.toS_r._finC._eqC) (fun x -> IAreg x) _r_
        _r1_ (eqP (ceqT_eqType arch.toS_r._finC._eqC) _r_ _r1_)
    in
    (match __top_assumption_ with
     | IArflag r -> _evar_0_0 r
     | IAreg r -> _evar_0_1 r)
  in
  (match _top_assumption_ with
   | IArflag r -> Obj.magic _evar_0_ r
   | IAreg r -> Obj.magic _evar_0_0 r)

(** val implicit_arg_eqMixin :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    implicit_arg Equality.mixin_of **)

let implicit_arg_eqMixin arch =
  { Equality.op = (implicit_arg_beq arch); Equality.mixin_of__1 =
    (implicit_arg_eq_axiom arch) }

(** val implicit_arg_eqType :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> Equality.coq_type **)

let implicit_arg_eqType arch =
  Obj.magic implicit_arg_eqMixin arch

type addr_kind =
| AK_compute
| AK_mem

type ('reg, 'regx, 'xreg, 'rflag, 'cond) arg_desc =
| ADImplicit of ('reg, 'regx, 'xreg, 'rflag, 'cond) implicit_arg
| ADExplicit of addr_kind * nat
   * ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_t option

(** val coq_F :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) rflag_t
    -> ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc **)

let coq_F _ f =
  ADImplicit (IArflag f)

(** val coq_R :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t ->
    ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc **)

let coq_R _ r =
  ADImplicit (IAreg r)

(** val coq_E :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> nat -> ('a1, 'a2, 'a3, 'a4, 'a5)
    arg_desc **)

let coq_E _ n =
  ADExplicit (AK_mem, n, None)

(** val coq_Ec :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> nat -> ('a1, 'a2, 'a3, 'a4, 'a5)
    arg_desc **)

let coq_Ec _ n =
  ADExplicit (AK_compute, n, None)

(** val coq_Ef :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> nat -> ('a1, 'a2, 'a3, 'a4, 'a5)
    reg_t -> ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc **)

let coq_Ef _ n r =
  ADExplicit (AK_mem, n, (Some r))

(** val check_oreg :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> Equality.sort option -> ('a1, 'a2,
    'a3, 'a4, 'a5) asm_arg -> bool **)

let check_oreg arch or0 ai =
  match or0 with
  | Some r ->
    (match ai with
     | Imm (_, _) -> true
     | Reg r' -> eq_op (ceqT_eqType arch.toS_r._finC._eqC) r (Obj.magic r')
     | _ -> false)
  | None -> true

type arg_kind =
| CAcond
| CAreg
| CAregx
| CAxmm
| CAmem of bool
| CAimm of wsize

(** val arg_kind_beq : arg_kind -> arg_kind -> bool **)

let arg_kind_beq x y =
  match x with
  | CAcond -> (match y with
               | CAcond -> true
               | _ -> false)
  | CAreg -> (match y with
              | CAreg -> true
              | _ -> false)
  | CAregx -> (match y with
               | CAregx -> true
               | _ -> false)
  | CAxmm -> (match y with
              | CAxmm -> true
              | _ -> false)
  | CAmem x0 ->
    (match y with
     | CAmem x1 -> internal_bool_beq x0 x1
     | _ -> false)
  | CAimm x0 -> (match y with
                 | CAimm x1 -> wsize_beq x0 x1
                 | _ -> false)

(** val arg_kind_eq_dec : arg_kind -> arg_kind -> bool **)

let arg_kind_eq_dec x y =
  let b = arg_kind_beq x y in if b then true else false

(** val arg_kind_eq_axiom : arg_kind Equality.axiom **)

let arg_kind_eq_axiom =
  eq_axiom_of_scheme arg_kind_beq

(** val arg_kind_eqMixin : arg_kind Equality.mixin_of **)

let arg_kind_eqMixin =
  { Equality.op = arg_kind_beq; Equality.mixin_of__1 = arg_kind_eq_axiom }

(** val arg_kind_eqType : Equality.coq_type **)

let arg_kind_eqType =
  Obj.magic arg_kind_eqMixin

type arg_kinds = arg_kind list

type args_kinds = arg_kinds list

type i_args_kinds = args_kinds list

(** val check_arg_kind :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg
    -> arg_kind -> bool **)

let check_arg_kind _ a cond =
  match a with
  | Condt _ -> (match cond with
                | CAcond -> true
                | _ -> false)
  | Imm (sz, _) ->
    (match cond with
     | CAimm sz' -> eq_op wsize_eqType (Obj.magic sz) (Obj.magic sz')
     | _ -> false)
  | Reg _ -> (match cond with
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

(** val check_arg_kinds :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg
    -> arg_kinds -> bool **)

let check_arg_kinds arch a cond =
  has (check_arg_kind arch a) cond

(** val check_args_kinds :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_args
    -> args_kinds -> bool **)

let check_args_kinds arch a cond =
  all2 (check_arg_kinds arch) a cond

(** val check_i_args_kinds :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> i_args_kinds -> ('a1, 'a2, 'a3,
    'a4, 'a5) asm_args -> bool **)

let check_i_args_kinds arch cond a =
  has (check_args_kinds arch a) cond

(** val check_arg_dest :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc
    -> stype -> bool **)

let check_arg_dest _ ad ty =
  match ad with
  | ADImplicit _ -> true
  | ADExplicit (_, _, _) ->
    negb (eq_op stype_eqType (Obj.magic ty) (Obj.magic Coq_sbool))

type ('reg, 'regx, 'xreg, 'rflag, 'cond) pp_asm_op_ext =
| PP_error
| PP_name
| PP_iname of wsize
| PP_iname2 of char list * wsize * wsize
| PP_viname of velem * bool
| PP_viname2 of velem * velem
| PP_ct of ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_arg

type ('reg, 'regx, 'xreg, 'rflag, 'cond) pp_asm_op = { pp_aop_name : 
                                                       char list;
                                                       pp_aop_ext : ('reg,
                                                                    'regx,
                                                                    'xreg,
                                                                    'rflag,
                                                                    'cond)
                                                                    pp_asm_op_ext;
                                                       pp_aop_args : 
                                                       (wsize * ('reg, 'regx,
                                                       'xreg, 'rflag, 'cond)
                                                       asm_arg) list }

(** val pp_aop_name :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    pp_asm_op -> char list **)

let pp_aop_name _ p =
  p.pp_aop_name

(** val pp_aop_ext :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    pp_asm_op -> ('a1, 'a2, 'a3, 'a4, 'a5) pp_asm_op_ext **)

let pp_aop_ext _ p =
  p.pp_aop_ext

(** val pp_aop_args :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    pp_asm_op -> (wsize * ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg) list **)

let pp_aop_args _ p =
  p.pp_aop_args

type ('reg, 'regx, 'xreg, 'rflag, 'cond) instr_desc_t = { id_msb_flag : 
                                                          msb_flag;
                                                          id_tin : stype list;
                                                          id_in : ('reg,
                                                                  'regx,
                                                                  'xreg,
                                                                  'rflag,
                                                                  'cond)
                                                                  arg_desc
                                                                  list;
                                                          id_tout : stype list;
                                                          id_out : ('reg,
                                                                   'regx,
                                                                   'xreg,
                                                                   'rflag,
                                                                   'cond)
                                                                   arg_desc
                                                                   list;
                                                          id_semi : sem_tuple
                                                                    exec
                                                                    sem_prod;
                                                          id_args_kinds : 
                                                          i_args_kinds;
                                                          id_nargs : 
                                                          nat;
                                                          id_str_jas : 
                                                          (unit -> char list);
                                                          id_safe : safe_cond
                                                                    list;
                                                          id_pp_asm : 
                                                          (('reg, 'regx,
                                                          'xreg, 'rflag,
                                                          'cond) asm_args ->
                                                          ('reg, 'regx,
                                                          'xreg, 'rflag,
                                                          'cond) pp_asm_op) }

(** val id_msb_flag :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    instr_desc_t -> msb_flag **)

let id_msb_flag _ i =
  i.id_msb_flag

(** val id_tin :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    instr_desc_t -> stype list **)

let id_tin _ i =
  i.id_tin

(** val id_in :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    instr_desc_t -> ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc list **)

let id_in _ i =
  i.id_in

(** val id_tout :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    instr_desc_t -> stype list **)

let id_tout _ i =
  i.id_tout

(** val id_out :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    instr_desc_t -> ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc list **)

let id_out _ i =
  i.id_out

(** val id_semi :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    instr_desc_t -> sem_tuple exec sem_prod **)

let id_semi _ i =
  i.id_semi

(** val id_args_kinds :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    instr_desc_t -> i_args_kinds **)

let id_args_kinds _ i =
  i.id_args_kinds

(** val id_nargs :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    instr_desc_t -> nat **)

let id_nargs _ i =
  i.id_nargs

(** val id_str_jas :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    instr_desc_t -> unit -> char list **)

let id_str_jas _ i =
  i.id_str_jas

(** val id_safe :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    instr_desc_t -> safe_cond list **)

let id_safe _ i =
  i.id_safe

(** val id_pp_asm :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    instr_desc_t -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_args -> ('a1, 'a2, 'a3,
    'a4, 'a5) pp_asm_op **)

let id_pp_asm _ i =
  i.id_pp_asm

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_op_decl = { _eqT : 
                                                                  'asm_op
                                                                  eqTypeC;
                                                                  instr_desc_op : 
                                                                  ('asm_op ->
                                                                  ('reg,
                                                                  'regx,
                                                                  'xreg,
                                                                  'rflag,
                                                                  'cond)
                                                                  instr_desc_t);
                                                                  prim_string : 
                                                                  (char list * 'asm_op
                                                                  prim_constructor)
                                                                  list }

(** val _eqT :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> 'a6 eqTypeC **)

let _eqT _ asm_op_decl0 =
  asm_op_decl0._eqT

(** val instr_desc_op :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> 'a6 -> ('a1, 'a2, 'a3, 'a4, 'a5) instr_desc_t **)

let instr_desc_op _ asm_op_decl0 =
  asm_op_decl0.instr_desc_op

(** val prim_string :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> (char list * 'a6 prim_constructor) list **)

let prim_string _ asm_op_decl0 =
  asm_op_decl0.prim_string

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_op_t' = 'asm_op

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_op_msb_t =
  wsize option * 'asm_op

(** val extend_size : wsize -> stype -> stype **)

let extend_size ws t = match t with
| Coq_sword ws' ->
  if cmp_le wsize_cmp ws' ws then Coq_sword ws else Coq_sword ws'
| _ -> t

(** val wextend_size : wsize -> stype -> sem_ot -> sem_ot **)

let wextend_size ws t x =
  match t with
  | Coq_sword ws' ->
    if cmp_le wsize_cmp ws' ws then zero_extend ws ws' x else x
  | _ -> x

(** val extend_tuple : wsize -> stype list -> sem_tuple -> sem_tuple **)

let rec extend_tuple ws id_tout0 t =
  match id_tout0 with
  | [] -> Obj.magic ()
  | t0 :: ts ->
    let rec_ = extend_tuple ws ts in
    (match ts with
     | [] -> wextend_size ws t0 t
     | _ :: _ ->
       Obj.magic ((wextend_size ws t0 (fst (Obj.magic t))),
         (rec_ (snd (Obj.magic t)))))

(** val apply_lprod : ('a1 -> 'a2) -> __ list -> 'a1 lprod -> 'a2 lprod **)

let rec apply_lprod f ts a =
  match ts with
  | [] -> Obj.magic f a
  | _ :: ts' -> Obj.magic (fun x -> apply_lprod f ts' (Obj.magic a x))

(** val is_not_CAmem : arg_kind -> bool **)

let is_not_CAmem = function
| CAmem _ -> false
| _ -> true

(** val exclude_mem_args_kinds :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc
    -> args_kinds -> args_kinds **)

let exclude_mem_args_kinds _ d cond =
  match d with
  | ADImplicit _ -> cond
  | ADExplicit (_, i, _) ->
    mapi (fun k c ->
      if eq_op nat_eqType (Obj.magic k) (Obj.magic i)
      then filter is_not_CAmem c
      else c) cond

(** val exclude_mem_i_args_kinds :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) arg_desc
    -> i_args_kinds -> i_args_kinds **)

let exclude_mem_i_args_kinds arch d cond =
  map (exclude_mem_args_kinds arch d) cond

(** val exclude_mem_aux :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> i_args_kinds -> ('a1, 'a2, 'a3,
    'a4, 'a5) arg_desc list -> i_args_kinds **)

let exclude_mem_aux arch cond d =
  foldl (fun cond0 d0 -> exclude_mem_i_args_kinds arch d0 cond0) cond d

(** val exclude_mem :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> i_args_kinds -> ('a1, 'a2, 'a3,
    'a4, 'a5) arg_desc list -> i_args_kinds **)

let exclude_mem arch cond d =
  filter (fun c ->
    negb
      (in_mem (Obj.magic [])
        (mem (seq_predType (seq_eqType arg_kind_eqType)) (Obj.magic c))))
    (exclude_mem_aux arch cond d)

(** val instr_desc :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_op_msb_t -> ('a1, 'a2,
    'a3, 'a4, 'a5) instr_desc_t **)

let instr_desc arch asm_op_d = function
| (ws, o0) ->
  let d = asm_op_d.instr_desc_op o0 in
  (match ws with
   | Some ws0 ->
     if eq_op msb_flag_eqType (Obj.magic d.id_msb_flag) (Obj.magic MSB_CLEAR)
     then { id_msb_flag = d.id_msb_flag; id_tin = d.id_tin; id_in = d.id_in;
            id_tout = (map (extend_size ws0) d.id_tout); id_out = d.id_out;
            id_semi =
            (apply_lprod (Result.map (extend_tuple ws0 d.id_tout))
              (map (Obj.magic __) d.id_tin) d.id_semi); id_args_kinds =
            (exclude_mem arch d.id_args_kinds d.id_out); id_nargs =
            d.id_nargs; id_str_jas = d.id_str_jas; id_safe = d.id_safe;
            id_pp_asm = d.id_pp_asm }
     else d
   | None -> d)

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_i_r =
| ALIGN
| LABEL of label_kind * label
| STORELABEL of ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_t * label
| JMP of remote_label
| JMPI of ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_arg
| Jcc of label * ('reg, 'regx, 'xreg, 'rflag, 'cond) cond_t
| JAL of ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_t * remote_label
| CALL of remote_label
| POPPC
| AsmOp of ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_op_t'
   * ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_args
| SysCall of BinNums.positive Syscall_t.syscall_t

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_i = { asmi_ii : 
                                                            instr_info;
                                                            asmi_i : 
                                                            ('reg, 'regx,
                                                            'xreg, 'rflag,
                                                            'cond, 'asm_op)
                                                            asm_i_r }

(** val asmi_ii :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_i -> instr_info **)

let asmi_ii _ _ a =
  a.asmi_ii

(** val asmi_i :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_i -> ('a1, 'a2, 'a3,
    'a4, 'a5, 'a6) asm_i_r **)

let asmi_i _ _ a =
  a.asmi_i

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_code =
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_i list

type ('reg, 'regx, 'xreg, 'rflag, 'cond) asm_typed_reg =
| ARReg of ('reg, 'regx, 'xreg, 'rflag, 'cond) reg_t
| ARegX of ('reg, 'regx, 'xreg, 'rflag, 'cond) regx_t
| AXReg of ('reg, 'regx, 'xreg, 'rflag, 'cond) xreg_t
| ABReg of ('reg, 'regx, 'xreg, 'rflag, 'cond) rflag_t

(** val asm_typed_reg_beq :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    asm_typed_reg -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_typed_reg -> bool **)

let asm_typed_reg_beq arch r1 r2 =
  match r1 with
  | ARReg r3 ->
    (match r2 with
     | ARReg r4 ->
       eq_op (ceqT_eqType arch.toS_r._finC._eqC) (Obj.magic r3) (Obj.magic r4)
     | _ -> false)
  | ARegX r3 ->
    (match r2 with
     | ARegX r4 ->
       eq_op (ceqT_eqType arch.toS_rx._finC._eqC) (Obj.magic r3)
         (Obj.magic r4)
     | _ -> false)
  | AXReg r3 ->
    (match r2 with
     | AXReg r4 ->
       eq_op (ceqT_eqType arch.toS_x._finC._eqC) (Obj.magic r3) (Obj.magic r4)
     | _ -> false)
  | ABReg r3 ->
    (match r2 with
     | ABReg r4 ->
       eq_op (ceqT_eqType arch.toS_f._finC._eqC) (Obj.magic r3) (Obj.magic r4)
     | _ -> false)

(** val asm_typed_reg_eq_axiom :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    asm_typed_reg Equality.axiom **)

let asm_typed_reg_eq_axiom arch _top_assumption_ =
  let _evar_0_ = fun r1 __top_assumption_ ->
    let _evar_0_ = fun r2 ->
      reflect_inj (ceqT_eqType arch.toS_r._finC._eqC) (fun x -> ARReg x) r1
        r2 (eqP (ceqT_eqType arch.toS_r._finC._eqC) r1 r2)
    in
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = fun _ -> ReflectF in
    let _evar_0_2 = fun _ -> ReflectF in
    (match __top_assumption_ with
     | ARReg r -> _evar_0_ r
     | ARegX r -> _evar_0_0 r
     | AXReg x -> _evar_0_1 x
     | ABReg r -> _evar_0_2 r)
  in
  let _evar_0_0 = fun r1 __top_assumption_ ->
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = fun r2 ->
      reflect_inj (ceqT_eqType arch.toS_rx._finC._eqC) (fun x -> ARegX x) r1
        r2 (eqP (ceqT_eqType arch.toS_rx._finC._eqC) r1 r2)
    in
    let _evar_0_2 = fun _ -> ReflectF in
    let _evar_0_3 = fun _ -> ReflectF in
    (match __top_assumption_ with
     | ARReg r -> _evar_0_0 r
     | ARegX r -> _evar_0_1 r
     | AXReg x -> _evar_0_2 x
     | ABReg r -> _evar_0_3 r)
  in
  let _evar_0_1 = fun r1 __top_assumption_ ->
    let _evar_0_1 = fun _ -> ReflectF in
    let _evar_0_2 = fun _ -> ReflectF in
    let _evar_0_3 = fun r2 ->
      reflect_inj (ceqT_eqType arch.toS_x._finC._eqC) (fun x -> AXReg x) r1
        r2 (eqP (ceqT_eqType arch.toS_x._finC._eqC) r1 r2)
    in
    let _evar_0_4 = fun _ -> ReflectF in
    (match __top_assumption_ with
     | ARReg r -> _evar_0_1 r
     | ARegX r -> _evar_0_2 r
     | AXReg x -> _evar_0_3 x
     | ABReg r -> _evar_0_4 r)
  in
  let _evar_0_2 = fun r1 __top_assumption_ ->
    let _evar_0_2 = fun _ -> ReflectF in
    let _evar_0_3 = fun _ -> ReflectF in
    let _evar_0_4 = fun _ -> ReflectF in
    let _evar_0_5 = fun r2 ->
      reflect_inj (ceqT_eqType arch.toS_f._finC._eqC) (fun x -> ABReg x) r1
        r2 (eqP (ceqT_eqType arch.toS_f._finC._eqC) r1 r2)
    in
    (match __top_assumption_ with
     | ARReg r -> _evar_0_2 r
     | ARegX r -> _evar_0_3 r
     | AXReg x -> _evar_0_4 x
     | ABReg r -> _evar_0_5 r)
  in
  (match _top_assumption_ with
   | ARReg r -> Obj.magic _evar_0_ r
   | ARegX r -> Obj.magic _evar_0_0 r
   | AXReg x -> Obj.magic _evar_0_1 x
   | ABReg r -> Obj.magic _evar_0_2 r)

(** val asm_typed_reg_eqMixin :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    asm_typed_reg Equality.mixin_of **)

let asm_typed_reg_eqMixin arch =
  { Equality.op = (asm_typed_reg_beq arch); Equality.mixin_of__1 =
    (asm_typed_reg_eq_axiom arch) }

(** val asm_typed_reg_eqType :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> Equality.coq_type **)

let asm_typed_reg_eqType arch =
  Obj.magic asm_typed_reg_eqMixin arch

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_fundef = { asm_fd_align : 
                                                                 wsize;
                                                                 asm_fd_arg : 
                                                                 ('reg,
                                                                 'regx,
                                                                 'xreg,
                                                                 'rflag,
                                                                 'cond)
                                                                 asm_typed_reg
                                                                 list;
                                                                 asm_fd_body : 
                                                                 ('reg,
                                                                 'regx,
                                                                 'xreg,
                                                                 'rflag,
                                                                 'cond,
                                                                 'asm_op)
                                                                 asm_code;
                                                                 asm_fd_res : 
                                                                 ('reg,
                                                                 'regx,
                                                                 'xreg,
                                                                 'rflag,
                                                                 'cond)
                                                                 asm_typed_reg
                                                                 list;
                                                                 asm_fd_export : 
                                                                 bool;
                                                                 asm_fd_total_stack : 
                                                                 coq_Z }

(** val asm_fd_align :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef -> wsize **)

let asm_fd_align _ _ a =
  a.asm_fd_align

(** val asm_fd_arg :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef -> ('a1, 'a2,
    'a3, 'a4, 'a5) asm_typed_reg list **)

let asm_fd_arg _ _ a =
  a.asm_fd_arg

(** val asm_fd_body :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef -> ('a1, 'a2,
    'a3, 'a4, 'a5, 'a6) asm_code **)

let asm_fd_body _ _ a =
  a.asm_fd_body

(** val asm_fd_res :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef -> ('a1, 'a2,
    'a3, 'a4, 'a5) asm_typed_reg list **)

let asm_fd_res _ _ a =
  a.asm_fd_res

(** val asm_fd_export :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef -> bool **)

let asm_fd_export _ _ a =
  a.asm_fd_export

(** val asm_fd_total_stack :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef -> coq_Z **)

let asm_fd_total_stack _ _ a =
  a.asm_fd_total_stack

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm_prog = { asm_globs : 
                                                               GRing.ComRing.sort
                                                               list;
                                                               asm_funcs : 
                                                               (funname * ('reg,
                                                               'regx, 'xreg,
                                                               'rflag, 'cond,
                                                               'asm_op)
                                                               asm_fundef)
                                                               list }

(** val asm_globs :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_prog ->
    GRing.ComRing.sort list **)

let asm_globs _ _ a =
  a.asm_globs

(** val asm_funcs :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_prog ->
    (funname * ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef) list **)

let asm_funcs _ _ a =
  a.asm_funcs

(** val is_ABReg :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    asm_typed_reg -> bool **)

let is_ABReg _ = function
| ABReg _ -> true
| _ -> false

type ('reg, 'regx, 'xreg, 'rflag, 'cond) calling_convention = { callee_saved : 
                                                                ('reg, 'regx,
                                                                'xreg,
                                                                'rflag,
                                                                'cond)
                                                                asm_typed_reg
                                                                list;
                                                                call_reg_args : 
                                                                ('reg, 'regx,
                                                                'xreg,
                                                                'rflag,
                                                                'cond) reg_t
                                                                list;
                                                                call_xreg_args : 
                                                                ('reg, 'regx,
                                                                'xreg,
                                                                'rflag,
                                                                'cond) xreg_t
                                                                list;
                                                                call_reg_ret : 
                                                                ('reg, 'regx,
                                                                'xreg,
                                                                'rflag,
                                                                'cond) reg_t
                                                                list;
                                                                call_xreg_ret : 
                                                                ('reg, 'regx,
                                                                'xreg,
                                                                'rflag,
                                                                'cond) xreg_t
                                                                list }

(** val callee_saved :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_typed_reg list **)

let callee_saved _ calling_convention0 =
  calling_convention0.callee_saved

(** val call_reg_args :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t list **)

let call_reg_args _ calling_convention0 =
  calling_convention0.call_reg_args

(** val call_xreg_args :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5) xreg_t list **)

let call_xreg_args _ calling_convention0 =
  calling_convention0.call_xreg_args

(** val call_reg_ret :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t list **)

let call_reg_ret _ calling_convention0 =
  calling_convention0.call_reg_ret

(** val call_xreg_ret :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5) xreg_t list **)

let call_xreg_ret _ calling_convention0 =
  calling_convention0.call_xreg_ret

(** val get_ARReg :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    asm_typed_reg -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t option **)

let get_ARReg _ = function
| ARReg r -> Some r
| _ -> None

(** val get_ARegX :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    asm_typed_reg -> ('a1, 'a2, 'a3, 'a4, 'a5) regx_t option **)

let get_ARegX _ = function
| ARegX r -> Some r
| _ -> None

(** val get_AXReg :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
    asm_typed_reg -> ('a1, 'a2, 'a3, 'a4, 'a5) xreg_t option **)

let get_AXReg _ = function
| AXReg r -> Some r
| _ -> None

(** val check_list :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> 'a6 eqTypeC -> (('a1, 'a2, 'a3,
    'a4, 'a5) asm_typed_reg -> 'a6 option) -> ('a1, 'a2, 'a3, 'a4, 'a5)
    asm_typed_reg list -> 'a6 list -> bool **)

let check_list _ eqc get l expected =
  let r = pmap get l in
  eq_op (seq_eqType (ceqT_eqType eqc)) (Obj.magic r)
    (Obj.magic take (size r) expected)

(** val check_call_conv :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) calling_convention -> ('a1, 'a2,
    'a3, 'a4, 'a5, 'a6) asm_fundef -> bool **)

let check_call_conv arch _ call_conv fd =
  if fd.asm_fd_export
  then (&&)
         (check_list arch arch.toS_r._finC._eqC (get_ARReg arch)
           fd.asm_fd_arg call_conv.call_reg_args)
         ((&&)
           (check_list arch arch.toS_x._finC._eqC (get_AXReg arch)
             fd.asm_fd_arg call_conv.call_xreg_args)
           ((&&)
             (check_list arch arch.toS_r._finC._eqC (get_ARReg arch)
               fd.asm_fd_res call_conv.call_reg_ret)
             (check_list arch arch.toS_x._finC._eqC (get_AXReg arch)
               fd.asm_fd_res call_conv.call_xreg_ret)))
  else true

(** val registers :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t
    list **)

let registers arch =
  arch.toS_r._finC.cenum

(** val registerxs :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) regx_t
    list **)

let registerxs arch =
  arch.toS_rx._finC.cenum

(** val xregisters :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) xreg_t
    list **)

let xregisters arch =
  arch.toS_x._finC.cenum

(** val rflags :
    ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5) rflag_t
    list **)

let rflags arch =
  arch.toS_f._finC.cenum

type rflagv =
| Def of bool
| Undef

(** val rflagv_beq : rflagv -> rflagv -> bool **)

let rflagv_beq x y =
  match x with
  | Def x0 ->
    (match y with
     | Def x1 -> internal_bool_beq x0 x1
     | Undef -> false)
  | Undef -> (match y with
              | Def _ -> false
              | Undef -> true)

(** val rflagv_eq_dec : rflagv -> rflagv -> bool **)

let rflagv_eq_dec x y =
  let b = rflagv_beq x y in if b then true else false

(** val rflagv_eq_axiom : rflagv Equality.axiom **)

let rflagv_eq_axiom =
  eq_axiom_of_scheme rflagv_beq

(** val rflagv_eqMixin : rflagv Equality.mixin_of **)

let rflagv_eqMixin =
  { Equality.op = rflagv_beq; Equality.mixin_of__1 = rflagv_eq_axiom }

(** val rflagv_eqType : Equality.coq_type **)

let rflagv_eqType =
  Obj.magic rflagv_eqMixin

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op) asm = { _arch_decl : 
                                                          ('reg, 'regx,
                                                          'xreg, 'rflag,
                                                          'cond) arch_decl;
                                                          _asm_op_decl : 
                                                          ('reg, 'regx,
                                                          'xreg, 'rflag,
                                                          'cond, 'asm_op)
                                                          asm_op_decl;
                                                          eval_cond : 
                                                          ((('reg, 'regx,
                                                          'xreg, 'rflag,
                                                          'cond) reg_t ->
                                                          GRing.ComRing.sort)
                                                          -> (('reg, 'regx,
                                                          'xreg, 'rflag,
                                                          'cond) rflag_t ->
                                                          bool exec) ->
                                                          ('reg, 'regx,
                                                          'xreg, 'rflag,
                                                          'cond) cond_t ->
                                                          bool exec) }

(** val _arch_decl :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm -> ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl **)

let _arch_decl asm0 =
  asm0._arch_decl

(** val _asm_op_decl :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6)
    asm_op_decl **)

let _asm_op_decl asm0 =
  asm0._asm_op_decl

(** val eval_cond :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm -> (('a1, 'a2, 'a3, 'a4, 'a5) reg_t ->
    GRing.ComRing.sort) -> (('a1, 'a2, 'a3, 'a4, 'a5) rflag_t -> bool exec)
    -> ('a1, 'a2, 'a3, 'a4, 'a5) cond_t -> bool exec **)

let eval_cond asm0 =
  asm0.eval_cond
