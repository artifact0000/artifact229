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

module E :
 sig
  val pass : char list

  val tunneling_error : char list -> pp_error_loc
 end

val labels_of_body : 'a1 asmOp -> 'a1 linstr list -> label list

val goto_targets : 'a1 asmOp -> 'a1 linstr list -> remote_label list

val coq_Linstr_align : 'a1 asmOp -> 'a1 linstr

val tunnel_chart :
  'a1 asmOp -> Equality.sort -> LUF.unionfind -> 'a1 linstr -> 'a1 linstr ->
  LUF.unionfind

val tunnel_plan :
  'a1 asmOp -> Equality.sort -> LUF.unionfind -> 'a1 lcmd -> LUF.unionfind

val tunnel_bore :
  'a1 asmOp -> Equality.sort -> LUF.unionfind -> 'a1 linstr -> 'a1 linstr

val tunnel_head :
  'a1 asmOp -> Equality.sort -> LUF.unionfind -> 'a1 linstr list -> 'a1
  linstr list

val tunnel_engine :
  'a1 asmOp -> Equality.sort -> 'a1 lcmd -> 'a1 lcmd -> 'a1 lcmd

val tunnel_lcmd : 'a1 asmOp -> Equality.sort -> 'a1 lcmd -> 'a1 lcmd

val tunnel_lfundef : 'a1 asmOp -> Equality.sort -> 'a1 lfundef -> 'a1 lfundef

val tunnel_funcs :
  'a1 asmOp -> (Equality.sort * 'a1 lfundef) list -> (Equality.sort * 'a1
  lfundef) list

val tunnel_lprog : 'a1 asmOp -> 'a1 lprog -> 'a1 lprog

val well_formed_body : 'a1 asmOp -> funname -> 'a1 linstr list -> bool

val well_formed_funcs :
  'a1 asmOp -> (Equality.sort * 'a1 lfundef) list -> bool

val well_formed_lprog : 'a1 asmOp -> 'a1 lprog -> bool

val tunnel_program :
  'a1 asmOp -> 'a1 lprog -> (pp_error_loc, 'a1 lprog) result
