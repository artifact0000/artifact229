open BinInt
open BinNums
open BinPos
open Datatypes
open Compiler_util
open Constant_prop
open Eqtype
open Expr
open Fexpr
open Label
open Linear
open Linear_util
open Memory_model
open Oseq
open Seq
open Sopn
open Ssralg
open Ssrbool
open Ssrfun
open Ssrint
open Ssrnat
open Type
open Utils0
open Var0
open Word0
open Word_ssrZ
open Wsize

module E :
 sig
  val pass_name : char list

  val my_error : pp_error -> pp_error_loc

  val gen_error : bool -> instr_info option -> pp_error -> pp_error_loc

  val ii_error : instr_info -> char list -> pp_error_loc

  val error : char list -> pp_error_loc

  val internal_error : char list -> pp_error_loc

  val assign_remains : instr_info -> lval -> pexpr -> pp_error_loc
 end

type 'asm_op linearization_params = { lip_tmp : Ident.Ident.ident;
                                      lip_tmp2 : Ident.Ident.ident;
                                      lip_not_saved_stack : Ident.Ident.ident
                                                            list;
                                      lip_allocate_stack_frame : (var_i ->
                                                                 var_i option
                                                                 -> coq_Z ->
                                                                 ((lexpr
                                                                 list * 'asm_op
                                                                 sopn) * rexpr
                                                                 list) list);
                                      lip_free_stack_frame : (var_i -> var_i
                                                             option -> coq_Z
                                                             -> ((lexpr
                                                             list * 'asm_op
                                                             sopn) * rexpr
                                                             list) list);
                                      lip_set_up_sp_register : (var_i ->
                                                               coq_Z -> wsize
                                                               -> var_i ->
                                                               var_i ->
                                                               ((lexpr
                                                               list * 'asm_op
                                                               sopn) * rexpr
                                                               list) list);
                                      lip_lmove : (var_i -> var_i -> (lexpr
                                                  list * 'asm_op
                                                  sopn) * rexpr list);
                                      lip_check_ws : (wsize -> bool);
                                      lip_lstore : (var_i -> coq_Z -> var_i
                                                   -> (lexpr list * 'asm_op
                                                   sopn) * rexpr list);
                                      lip_lstores : (var_i ->
                                                    (Var.var * coq_Z) list ->
                                                    ((lexpr list * 'asm_op
                                                    sopn) * rexpr list) list);
                                      lip_lloads : (var_i ->
                                                   (Var.var * coq_Z) list ->
                                                   coq_Z -> ((lexpr
                                                   list * 'asm_op
                                                   sopn) * rexpr list) list) }

val lstores_dfl :
  'a1 asmOp -> (var_i -> coq_Z -> var_i -> (lexpr list * 'a1 sopn) * rexpr
  list) -> var_i -> (Var.var * coq_Z) list -> ((lexpr list * 'a1
  sopn) * rexpr list) list

val lstores_imm_dfl :
  coq_PointerData -> 'a1 asmOp -> Ident.Ident.ident -> (var_i -> coq_Z ->
  var_i -> (lexpr list * 'a1 sopn) * rexpr list) -> (var_i -> var_i -> coq_Z
  -> ((lexpr list * 'a1 sopn) * rexpr list) list) -> (coq_Z -> bool) -> var_i
  -> (Var.var * coq_Z) list -> ((lexpr list * 'a1 sopn) * rexpr list) list

val lloads_aux :
  'a1 asmOp -> (var_i -> var_i -> coq_Z -> (lexpr list * 'a1 sopn) * rexpr
  list) -> var_i -> (Var.var * coq_Z) list -> ((lexpr list * 'a1
  sopn) * rexpr list) list

val lloads_dfl :
  'a1 asmOp -> (var_i -> var_i -> coq_Z -> (lexpr list * 'a1 sopn) * rexpr
  list) -> var_i -> (Var.var * coq_Z) list -> coq_Z -> ((lexpr list * 'a1
  sopn) * rexpr list) list

val lloads_imm_dfl :
  coq_PointerData -> 'a1 asmOp -> Ident.Ident.ident -> (var_i -> var_i ->
  coq_Z -> (lexpr list * 'a1 sopn) * rexpr list) -> (var_i -> var_i -> coq_Z
  -> ((lexpr list * 'a1 sopn) * rexpr list) list) -> (coq_Z -> bool) -> var_i
  -> (Var.var * coq_Z) list -> coq_Z -> ((lexpr list * 'a1 sopn) * rexpr
  list) list

val lmove :
  'a1 asmOp -> 'a1 linearization_params -> var_i -> var_i -> 'a1 linstr

val lstore :
  'a1 asmOp -> 'a1 linearization_params -> var_i -> coq_Z -> var_i -> 'a1
  linstr

val set_up_sp_register :
  'a1 asmOp -> 'a1 linearization_params -> var_i -> coq_Z -> wsize -> var_i
  -> var_i -> 'a1 lcmd

val check_Some :
  (char list -> 'a1) -> ('a2 -> 'a3 option) -> char list -> 'a2 -> ('a1,
  unit) result

val to_fexpr : pexpr -> fexpr

val check_fexpr : instr_info -> pexpr -> (pp_error_loc, unit) result

val check_rexpr : instr_info -> pexpr -> (pp_error_loc, unit) result

val check_lexpr : instr_info -> lval -> (pp_error_loc, unit) result

val ovar_of_ra : return_address_location -> Var.var option

val ovari_of_ra : return_address_location -> var_i option

val tmp_of_ra : return_address_location -> Var.var option

val tmpi_of_ra : return_address_location -> var_i option

val stack_frame_allocation_size : stk_fun_extra -> coq_Z

val frame_size : stk_fun_extra -> coq_Z

val push_to_save :
  coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
  (Var.var * coq_Z) list -> (Var.var * coq_Z) -> 'a1 lcmd

val pop_to_save :
  coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
  (Var.var * coq_Z) list -> coq_Z -> 'a1 lcmd

val check_c :
  'a1 asmOp -> ('a1 instr -> unit cexec) -> 'a1 instr list -> unit cexec

val check_i :
  coq_PointerData -> 'a1 asmOp -> 'a1 sprog -> funname -> stk_fun_extra ->
  'a1 instr -> unit cexec

val check_to_save_slot : (Var.var * coq_Z) -> (coq_Z * wsize) cexec

val all_disjoint_aligned_between :
  coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> coq_Z -> coq_Z
  -> wsize -> (Var.var * coq_Z) list -> unit cexec

val check_to_save :
  coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> stk_fun_extra
  -> unit cexec

val linear_c :
  'a1 asmOp -> ('a1 instr -> label -> 'a1 lcmd -> label * 'a1 lcmd) -> 'a1
  instr list -> label -> 'a1 lcmd -> label * 'a1 lcmd

val add_align :
  'a1 asmOp -> instr_info -> align -> 'a1 lcmd -> 'a1 linstr list

val align :
  'a1 asmOp -> instr_info -> align -> (label * 'a1 lcmd) -> label * 'a1 lcmd

val ov_type_ptr : coq_PointerData -> Var.var option -> bool

val check_fd :
  coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
  funname -> 'a1 sfundef -> (pp_error_loc, unit) result

val check_prog :
  coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
  (pp_error_loc, unit) result

val allocate_stack_frame :
  coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
  bool -> instr_info -> coq_Z -> var_i option -> bool -> 'a1 lcmd

val linear_i :
  coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
  funname -> 'a1 instr -> label -> 'a1 lcmd -> label * 'a1 lcmd

val linear_body :
  coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
  funname -> stk_fun_extra -> 'a1 instr list -> label * 'a1 lcmd

val linear_fd :
  coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
  funname -> 'a1 sfundef -> label * 'a1 lfundef

val linear_prog :
  coq_PointerData -> 'a1 asmOp -> 'a1 linearization_params -> 'a1 sprog ->
  'a1 lprog cexec
