open BinInt
open BinNums
open BinPos
open Datatypes
open String0
open Compiler_util
open Eqtype
open Expr
open Fexpr
open Label
open Linear
open Path
open Seq
open Sopn
open Ssrbool
open Ssrint
open Type
open Utils0
open Var0
open Word_ssrZ
open Wsize
open Xseq

module E :
 sig
  val pass : char list

  val assoc_failed : pp_error_loc

  val debug : pp_error_loc

  val cant_get_lti : pp_error_loc

  val invalid_use_vars : pp_error_loc

  val invalid_state : pp_error_loc

  val cant_get_lta : pp_error_loc

  val cant_get_tag_reg : pp_error_loc

  val gen_err_msg :
    char list -> instr_info -> char list option -> pp_error_loc

  val save_tag_failed : instr_info -> char list option -> pp_error_loc

  val lower_ret_failed : instr_info -> char list option -> pp_error_loc

  val lower_update_after_call_failed :
    instr_info -> char list option -> pp_error_loc
 end

type cs_info = remote_label * coq_Z

type cst_value = cs_info list * label

type cs_table = cst_value Mf.t

val cst_lookup : cs_table -> funname -> cst_value

val label_info :
  'a1 asmOp -> (funname * label) list -> label -> 'a1 lcmd ->
  (funname * label) list * label

val next_tag : cs_info list -> coq_Z

val acc_entry : funname -> cs_table -> (funname * label) -> cs_table

val add_call_sites :
  'a1 asmOp -> cs_table -> funname -> 'a1 lfundef -> cs_table

val call_sites_table : 'a1 asmOp -> 'a1 lprog -> cs_table

type load_tag_info =
| LTIstack of var_i * var_i
| LTIregister of var_i
| LTIextra_register of var_i * var_i

type lti_table = load_tag_info Mf.t

type lti_state = { ltist_scratch : var_i option; ltist_msf : var_i option }

val ltist_empty : lti_state

val ltist_get_lti :
  'a1 asmOp -> lti_state -> 'a1 linstr_r -> load_tag_info cexec

val ltist_set_scratch : lti_state -> lexpr list -> lti_state cexec

val ltist_set_msf : lti_state -> rexpr list -> lti_state cexec

val lti_lcmd :
  'a1 asmOp -> lti_state -> 'a1 lcmd -> (load_tag_info * 'a1 lcmd) cexec

val lti_lfd :
  'a1 asmOp -> funname list -> lti_table -> funname -> 'a1 lfundef ->
  (lti_table * (funname * 'a1 lfundef)) cexec

val lti_lfuncs :
  'a1 asmOp -> funname list -> (funname * 'a1 lfundef) list ->
  (lti_table * (funname * 'a1 lfundef) list) cexec

type save_tag_args =
| STAstack of var_i
| STAregister of var_i
| STAextra_register of var_i * var_i

type load_tag_args =
| LTAstack of var_i * var_i * var_i
| LTAregister of var_i
| LTAextra_register of var_i * var_i

type 'asm_op protect_calls_params = { pcp_is_update_after_call : ('asm_op
                                                                 sopn -> bool);
                                      pcp_lower_update_after_call : ((char list
                                                                    option ->
                                                                    pp_error_loc)
                                                                    -> coq_Z
                                                                    -> var_i
                                                                    ->
                                                                    cs_info
                                                                    bintree
                                                                    -> lexpr
                                                                    list ->
                                                                    rexpr
                                                                    list ->
                                                                    ((lexpr
                                                                    list * 'asm_op
                                                                    sopn) * rexpr
                                                                    list)
                                                                    list
                                                                    cexec);
                                      pcp_load_tag : ((char list option ->
                                                     pp_error_loc) ->
                                                     load_tag_args ->
                                                     (var_i * ((lexpr
                                                     list * 'asm_op
                                                     sopn) * rexpr list)
                                                     list) cexec);
                                      pcp_cmpi : ((char list option ->
                                                 pp_error_loc) -> var_i ->
                                                 coq_Z -> ((lexpr
                                                 list * 'asm_op sopn) * rexpr
                                                 list) cexec);
                                      pcp_cond_ne : fexpr;
                                      pcp_cond_gt : fexpr;
                                      pcp_save_ra : ((char list option ->
                                                    pp_error_loc) ->
                                                    save_tag_args -> coq_Z ->
                                                    ((lexpr list * 'asm_op
                                                    sopn) * rexpr list) list
                                                    cexec) }

val lcond_remote :
  'a1 asmOp -> fexpr -> label -> remote_label -> 'a1 linstr_r list cexec

val lcmd_of_tree :
  'a1 asmOp -> 'a1 protect_calls_params -> instr_info -> var_i -> label ->
  cs_info bintree -> ('a1 linstr_r list * label) cexec

val return_table :
  'a1 asmOp -> 'a1 protect_calls_params -> (funname -> cs_info list ->
  cs_info bintree) -> instr_info -> funname -> load_tag_args -> cst_value ->
  'a1 linstr_r list cexec

val fn_csi : cs_table -> funname -> cst_value

val get_lta : var_i -> lti_table -> funname -> load_tag_args cexec

val do_ret :
  'a1 asmOp -> 'a1 protect_calls_params -> (funname -> cs_info list ->
  cs_info bintree) -> var_i -> lti_table -> funname -> instr_info ->
  cst_value -> 'a1 lcmd cexec

val do_ret_li :
  'a1 asmOp -> 'a1 protect_calls_params -> (funname -> cs_info list ->
  cs_info bintree) -> var_i -> cs_table -> lti_table -> funname -> 'a1 linstr
  -> 'a1 lcmd cexec

val do_ret_lcmd :
  'a1 asmOp -> 'a1 protect_calls_params -> (funname -> cs_info list ->
  cs_info bintree) -> var_i -> cs_table -> lti_table -> funname -> 'a1 lcmd
  -> 'a1 lcmd cexec

type state =
| STempty
| STscratch of var_i
| STupdate_args of cs_info list * coq_Z * var_i

val get_sta : var_i -> state -> var_i option -> save_tag_args * state

val get_update_args :
  state -> (((cs_info list * coq_Z) * var_i) * state) cexec

val set_scratch : lexpr list -> state cexec

val set_update_args : state -> cs_info list -> coq_Z -> var_i -> state cexec

val get_tag_reg : lti_table -> funname -> var_i cexec

val do_call :
  'a1 asmOp -> 'a1 protect_calls_params -> var_i -> cs_table -> lti_table ->
  funname -> instr_info -> state -> var_i option -> remote_label -> label ->
  ('a1 lcmd * state) cexec

val do_update_after_call :
  'a1 asmOp -> 'a1 protect_calls_params -> (funname -> cs_info list ->
  cs_info bintree) -> funname -> instr_info -> state -> lexpr list -> rexpr
  list -> ('a1 lcmd * state) cexec

val do_call_lcmd :
  'a1 asmOp -> 'a1 protect_calls_params -> (funname -> cs_info list ->
  cs_info bintree) -> var_i -> cs_table -> lti_table -> funname -> state ->
  'a1 lcmd -> 'a1 lcmd cexec

val pc_lfd :
  'a1 asmOp -> 'a1 protect_calls_params -> (funname -> cs_info list ->
  cs_info bintree) -> funname list -> var_i -> cs_table -> lti_table ->
  funname -> 'a1 lfundef -> 'a1 lfundef cexec

val chk_f : 'a1 asmOp -> 'a1 lprog -> funname -> cst_value -> bool

val pc_lprog :
  coq_PointerData -> 'a1 asmOp -> 'a1 protect_calls_params -> (funname ->
  cs_info list -> cs_info bintree) -> funname list -> bool -> 'a1 lprog ->
  'a1 lprog cexec
