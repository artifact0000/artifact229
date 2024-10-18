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

val e2bool : pexpr -> bool exec

val e2int : pexpr -> coq_Z exec

val e2word : wsize -> pexpr -> GRing.ComRing.sort exec

val of_expr : stype -> pexpr -> sem_t exec

val to_expr : stype -> sem_t -> pexpr exec

val ssem_sop1 : sop1 -> pexpr -> pexpr

val ssem_sop2 : sop2 -> pexpr -> pexpr -> pexpr

val snot : pexpr -> pexpr

val sneg_int : pexpr -> pexpr

val s_op1 : sop1 -> pexpr -> pexpr

val sbeq : pexpr -> pexpr -> pexpr

val sand : pexpr -> pexpr -> pexpr

val sor : pexpr -> pexpr -> pexpr

val sadd_int : pexpr -> pexpr -> pexpr

val sadd_w : wsize -> pexpr -> pexpr -> pexpr

val sadd : op_kind -> pexpr -> pexpr -> pexpr

val ssub_int : pexpr -> pexpr -> pexpr

val ssub_w : wsize -> pexpr -> pexpr -> pexpr

val ssub : op_kind -> pexpr -> pexpr -> pexpr

val smul_int : pexpr -> pexpr -> pexpr

val smul_w : wsize -> pexpr -> pexpr -> pexpr

val smul : op_kind -> pexpr -> pexpr -> pexpr

val s_eq : op_kind -> pexpr -> pexpr -> pexpr

val sneq : op_kind -> pexpr -> pexpr -> pexpr

val is_cmp_const : cmp_kind -> pexpr -> coq_Z option

val slt : cmp_kind -> pexpr -> pexpr -> pexpr

val sle : cmp_kind -> pexpr -> pexpr -> pexpr

val sgt : cmp_kind -> pexpr -> pexpr -> pexpr

val sge : cmp_kind -> pexpr -> pexpr -> pexpr

val s_op2 : sop2 -> pexpr -> pexpr -> pexpr

val app_sopn : stype list -> 'a1 exec sem_prod -> pexpr list -> 'a1 exec

val s_opN : coq_FlagCombinationParams -> opN -> pexpr list -> pexpr

val s_if : stype -> pexpr -> pexpr -> pexpr -> pexpr

type const_v =
| Cbool of bool
| Cint of coq_Z
| Cword of wsize * GRing.ComRing.sort

val const_v_beq : const_v -> const_v -> bool

val const_v_eq_axiom : const_v Equality.axiom

val const_v_eqMixin : const_v Equality.mixin_of

val const_v_eqType : Equality.coq_type

val const : const_v -> pexpr

type globals = (Var.var -> glob_value option) option

val const_prop_e :
  coq_FlagCombinationParams -> globals -> const_v Mvar.t -> pexpr -> pexpr

val empty_cpm : const_v Mvar.t

val merge_cpm : const_v Mvar.t -> const_v Mvar.t -> const_v Mvar.t

val remove_cpm : const_v Mvar.t -> SvExtra.Sv.t -> const_v Mvar.t

val const_prop_rv :
  coq_FlagCombinationParams -> globals -> const_v Mvar.t -> lval -> const_v
  Mvar.t * lval

val const_prop_rvs :
  coq_FlagCombinationParams -> globals -> const_v Mvar.t -> lval list ->
  const_v Mvar.t * lval list

val wsize_of_stype : stype -> wsize

val add_cpm :
  const_v Mvar.t -> lval -> assgn_tag -> stype -> pexpr -> const_v Mvar.t

val const_prop :
  'a1 asmOp -> (const_v Mvar.t -> 'a1 instr -> const_v Mvar.t * 'a1 instr
  list) -> const_v Mvar.t -> 'a1 instr list -> const_v Mvar.t * 'a1 instr list

val is_update_imm :
  'a1 asmOp -> lval list -> 'a1 sopn -> pexpr list -> ((lval * bool) * pexpr)
  option

val const_prop_i :
  coq_FlagCombinationParams -> coq_MSFsize -> 'a1 asmOp -> glob_decl list ->
  const_v Mvar.t -> 'a1 instr -> const_v Mvar.t * 'a1 instr list

val const_prop_fun :
  coq_FlagCombinationParams -> coq_MSFsize -> 'a1 asmOp -> progT -> glob_decl
  list -> 'a1 fundef -> ('a1, extra_fun_t) _fundef

val const_prop_prog :
  coq_FlagCombinationParams -> coq_MSFsize -> 'a1 asmOp -> progT -> 'a1 prog
  -> 'a1 prog
