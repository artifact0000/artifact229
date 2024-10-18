open BinInt
open BinNums
open Datatypes
open Eqtype
open Expr
open Flag_combination
open Global
open Low_memory
open Memory_model
open Sem_op_typed
open Sem_params
open Sem_type
open Sopn
open Ssralg
open Syscall
open Syscall_sem
open Type
open Utils0
open Values
open Var0
open Varmap
open Warray_
open Word0
open Wsize
open Xseq

(** val sem_sop1 : sop1 -> value -> value exec **)

let sem_sop1 o v =
  match of_val (fst (type_of_op1 o)) v with
  | Ok x -> Ok (to_val (snd (type_of_op1 o)) (sem_sop1_typed o x))
  | Error s -> Error s

(** val sem_sop2 : sop2 -> value -> value -> value exec **)

let sem_sop2 o v1 v2 =
  match of_val (fst (fst (type_of_op2 o))) v1 with
  | Ok x ->
    (match of_val (snd (fst (type_of_op2 o))) v2 with
     | Ok x0 ->
       (match sem_sop2_typed o x x0 with
        | Ok x1 -> Ok (to_val (snd (type_of_op2 o)) x1)
        | Error s -> Error s)
     | Error s -> Error s)
  | Error s -> Error s

(** val sem_opN : coq_FlagCombinationParams -> opN -> values -> value exec **)

let sem_opN cfcd op vs =
  match app_sopn (fst (type_of_opN op)) (sem_opN_typed cfcd op) vs with
  | Ok x -> Ok (to_val (snd (type_of_opN op)) x)
  | Error s -> Error s

(** val get_global_value : glob_decl list -> Var.var -> glob_value option **)

let get_global_value gd g =
  assoc Var.var_eqType (Obj.magic gd) (Obj.magic g)

(** val gv2val : glob_value -> value **)

let gv2val = function
| Gword (ws, w) -> Vword (ws, w)
| Garr (p, a) -> Varr (p, a)

(** val get_global : glob_decl list -> Var.var -> value exec **)

let get_global gd g =
  match get_global_value gd g with
  | Some ga ->
    let v = gv2val ga in
    if eq_op stype_eqType (Obj.magic type_of_val v) (Obj.magic Var.vtype g)
    then Ok v
    else type_error
  | None -> type_error

type 'syscall_state estate = { escs : 'syscall_state; emem : Memory.mem;
                               evm : Vm.t }

(** val escs :
    coq_WithSubWord -> 'a1 coq_EstateParams -> 'a1 estate -> 'a1 **)

let escs _ _ e =
  e.escs

(** val emem :
    coq_WithSubWord -> 'a1 coq_EstateParams -> 'a1 estate -> Memory.mem **)

let emem _ _ e =
  e.emem

(** val evm :
    coq_WithSubWord -> 'a1 coq_EstateParams -> 'a1 estate -> Vm.t **)

let evm _ _ e =
  e.evm

(** val get_gvar :
    coq_WithSubWord -> bool -> glob_decl list -> Vm.t -> gvar -> (error,
    value) result **)

let get_gvar wsw wdb gd vm x =
  if is_lvar x
  then get_var wsw wdb vm x.gv.v_var
  else get_global gd x.gv.v_var

(** val get_var_is :
    coq_WithSubWord -> bool -> Vm.t -> var_i list -> (error, value list)
    result **)

let get_var_is wsw wdb vm =
  mapM (fun x -> get_var wsw wdb vm x.v_var)

(** val on_arr_var :
    value exec -> (positive -> WArray.array -> 'a1 exec) -> (error, 'a1)
    result **)

let on_arr_var v f =
  match v with
  | Ok x -> (match x with
             | Varr (n, t0) -> f n t0
             | _ -> type_error)
  | Error s -> Error s

(** val with_vm :
    coq_WithSubWord -> 'a1 coq_EstateParams -> 'a1 estate -> Vm.t -> 'a1
    estate **)

let with_vm _ _ s vm =
  { escs = s.escs; emem = s.emem; evm = vm }

(** val with_mem :
    coq_WithSubWord -> 'a1 coq_EstateParams -> 'a1 estate -> Memory.mem ->
    'a1 estate **)

let with_mem _ _ s m =
  { escs = s.escs; emem = m; evm = s.evm }

(** val with_scs :
    coq_WithSubWord -> 'a1 coq_EstateParams -> 'a1 estate -> 'a1 -> 'a1 estate **)

let with_scs _ _ s scs =
  { escs = scs; emem = s.emem; evm = s.evm }

(** val sem_pexpr :
    coq_WithSubWord -> 'a1 coq_EstateParams -> coq_SemPexprParams -> bool ->
    glob_decl list -> 'a1 estate -> pexpr -> value exec **)

let rec sem_pexpr wsw ep spp wdb gd s = function
| Pconst z -> Ok (Vint z)
| Pbool b -> Ok (Vbool b)
| Parr_init n -> Ok (Varr (n, (WArray.empty n)))
| Pvar v -> get_gvar wsw wdb gd s.evm v
| Pget (aa, ws, x, e0) ->
  on_arr_var (get_gvar wsw wdb gd s.evm x) (fun n t0 ->
    match match sem_pexpr wsw ep spp wdb gd s e0 with
          | Ok x0 -> to_int x0
          | Error s0 -> Error s0 with
    | Ok x0 ->
      (match WArray.get n aa ws t0 x0 with
       | Ok x1 -> Ok (Vword (ws, x1))
       | Error s0 -> Error s0)
    | Error s0 -> Error s0)
| Psub (aa, ws, len, x, e0) ->
  on_arr_var (get_gvar wsw wdb gd s.evm x) (fun n t0 ->
    match match sem_pexpr wsw ep spp wdb gd s e0 with
          | Ok x0 -> to_int x0
          | Error s0 -> Error s0 with
    | Ok x0 ->
      (match WArray.get_sub n aa ws len t0 x0 with
       | Ok x1 -> Ok (Varr ((Z.to_pos (arr_size ws len)), x1))
       | Error s0 -> Error s0)
    | Error s0 -> Error s0)
| Pload (sz, x, e0) ->
  (match match get_var wsw wdb s.evm x.v_var with
         | Ok x0 -> to_word (coq_Uptr ep._pd) x0
         | Error s0 -> Error s0 with
   | Ok x0 ->
     (match match sem_pexpr wsw ep spp wdb gd s e0 with
            | Ok x1 -> to_word (coq_Uptr ep._pd) x1
            | Error s0 -> Error s0 with
      | Ok x1 ->
        (match CoreMem.read
                 (GRing.Zmodule.eqType
                   (GRing.ComRing.zmodType (word (coq_Uptr ep._pd))))
                 (coq_Pointer ep._pd) (Memory.coq_CM ep._pd) s.emem
                 (GRing.add (GRing.ComRing.zmodType (word (coq_Uptr ep._pd)))
                   x0 x1) sz with
         | Ok x2 -> Ok (to_val (Coq_sword sz) x2)
         | Error s0 -> Error s0)
      | Error s0 -> Error s0)
   | Error s0 -> Error s0)
| Papp1 (o, e1) ->
  (match sem_pexpr wsw ep spp wdb gd s e1 with
   | Ok x -> sem_sop1 o x
   | Error s0 -> Error s0)
| Papp2 (o, e1, e2) ->
  (match sem_pexpr wsw ep spp wdb gd s e1 with
   | Ok x ->
     (match sem_pexpr wsw ep spp wdb gd s e2 with
      | Ok x0 -> sem_sop2 o x x0
      | Error s0 -> Error s0)
   | Error s0 -> Error s0)
| PappN (op, es) ->
  (match mapM (sem_pexpr wsw ep spp wdb gd s) es with
   | Ok x -> sem_opN (_fcp spp) op x
   | Error s0 -> Error s0)
| Pif (t0, e0, e1, e2) ->
  (match match sem_pexpr wsw ep spp wdb gd s e0 with
         | Ok x -> to_bool x
         | Error s0 -> Error s0 with
   | Ok x ->
     (match match sem_pexpr wsw ep spp wdb gd s e1 with
            | Ok x0 -> truncate_val t0 x0
            | Error s0 -> Error s0 with
      | Ok x0 ->
        (match match sem_pexpr wsw ep spp wdb gd s e2 with
               | Ok x1 -> truncate_val t0 x1
               | Error s0 -> Error s0 with
         | Ok x1 -> Ok (if x then x0 else x1)
         | Error s0 -> Error s0)
      | Error s0 -> Error s0)
   | Error s0 -> Error s0)

(** val sem_pexprs :
    coq_WithSubWord -> 'a1 coq_EstateParams -> coq_SemPexprParams -> bool ->
    glob_decl list -> 'a1 estate -> pexpr list -> (error, value list) result **)

let sem_pexprs wsw ep spp wdb gd s =
  mapM (sem_pexpr wsw ep spp wdb gd s)

(** val write_var :
    coq_WithSubWord -> 'a1 coq_EstateParams -> bool -> var_i -> value -> 'a1
    estate -> 'a1 estate exec **)

let write_var wsw ep wdb x v s =
  match set_var wsw wdb s.evm x.v_var v with
  | Ok x0 -> Ok (with_vm wsw ep s x0)
  | Error s0 -> Error s0

(** val write_vars :
    coq_WithSubWord -> 'a1 coq_EstateParams -> bool -> var_i list -> value
    list -> 'a1 estate -> (error, 'a1 estate) result **)

let write_vars wsw ep wdb xs vs s =
  fold2 ErrType (write_var wsw ep wdb) xs vs s

(** val write_none :
    coq_WithSubWord -> 'a1 coq_EstateParams -> bool -> 'a1 estate -> stype ->
    value -> (error, 'a1 estate) result **)

let write_none wsw _ wdb s ty v =
  if truncatable wsw wdb ty v
  then if coq_DB wdb v then Ok s else let s0 = ErrAddrUndef in Error s0
  else let s0 = ErrType in Error s0

(** val write_lval :
    coq_WithSubWord -> 'a1 coq_EstateParams -> coq_SemPexprParams -> bool ->
    glob_decl list -> lval -> value -> 'a1 estate -> 'a1 estate exec **)

let write_lval wsw ep spp wdb gd l v s =
  match l with
  | Lnone (_, ty) -> write_none wsw ep wdb s ty v
  | Lvar x -> write_var wsw ep wdb x v s
  | Lmem (sz, x, e) ->
    (match match get_var wsw wdb s.evm x.v_var with
           | Ok x0 -> to_word (coq_Uptr ep._pd) x0
           | Error s0 -> Error s0 with
     | Ok x0 ->
       (match match sem_pexpr wsw ep spp wdb gd s e with
              | Ok x1 -> to_word (coq_Uptr ep._pd) x1
              | Error s0 -> Error s0 with
        | Ok x1 ->
          let p =
            GRing.add (GRing.ComRing.zmodType (word (coq_Uptr ep._pd))) x0 x1
          in
          (match to_word sz v with
           | Ok x2 ->
             (match CoreMem.write
                      (GRing.Zmodule.eqType
                        (GRing.ComRing.zmodType (word (coq_Uptr ep._pd))))
                      (coq_Pointer ep._pd) (Memory.coq_CM ep._pd) s.emem p sz
                      x2 with
              | Ok x3 -> Ok (with_mem wsw ep s x3)
              | Error s0 -> Error s0)
           | Error s0 -> Error s0)
        | Error s0 -> Error s0)
     | Error s0 -> Error s0)
  | Laset (aa, ws, x, i) ->
    on_arr_var (get_var wsw wdb s.evm x.v_var) (fun n t0 ->
      match match sem_pexpr wsw ep spp wdb gd s i with
            | Ok x0 -> to_int x0
            | Error s0 -> Error s0 with
      | Ok x0 ->
        (match to_word ws v with
         | Ok x1 ->
           (match WArray.set n ws t0 aa x0 x1 with
            | Ok x2 ->
              write_var wsw ep wdb x (to_val (Coq_sarr n) (Obj.magic x2)) s
            | Error s0 -> Error s0)
         | Error s0 -> Error s0)
      | Error s0 -> Error s0)
  | Lasub (aa, ws, len, x, i) ->
    on_arr_var (get_var wsw wdb s.evm x.v_var) (fun n t0 ->
      match match sem_pexpr wsw ep spp wdb gd s i with
            | Ok x0 -> to_int x0
            | Error s0 -> Error s0 with
      | Ok x0 ->
        (match to_arr (Z.to_pos (arr_size ws len)) v with
         | Ok x1 ->
           (match WArray.set_sub n aa ws len t0 x0 (Obj.magic x1) with
            | Ok x2 ->
              write_var wsw ep wdb x (to_val (Coq_sarr n) (Obj.magic x2)) s
            | Error s0 -> Error s0)
         | Error s0 -> Error s0)
      | Error s0 -> Error s0)

(** val write_lvals :
    coq_WithSubWord -> 'a1 coq_EstateParams -> coq_SemPexprParams -> bool ->
    glob_decl list -> 'a1 estate -> lval list -> value list -> (error, 'a1
    estate) result **)

let write_lvals wsw ep spp wdb gd s xs vs =
  fold2 ErrType (write_lval wsw ep spp wdb gd) xs vs s

(** val exec_sopn :
    'a2 coq_EstateParams -> 'a1 asmOp -> 'a1 sopn -> values -> values exec **)

let exec_sopn ep asmop o vs =
  let semi = sopn_sem ep._msf_size asmop o in
  (match app_sopn (get_instr_desc ep._msf_size asmop o).tin semi vs with
   | Ok x -> Ok (list_ltuple (get_instr_desc ep._msf_size asmop o).tout x)
   | Error s -> Error s)

(** val sem_sopn :
    coq_WithSubWord -> 'a2 coq_EstateParams -> coq_SemPexprParams -> 'a1
    asmOp -> glob_decl list -> 'a1 sopn -> 'a2 estate -> lval list -> pexpr
    list -> (error, 'a2 estate) result **)

let sem_sopn wsw ep spp asmop gd o m lvs args =
  match match sem_pexprs wsw ep spp true gd m args with
        | Ok x -> exec_sopn ep asmop o x
        | Error s -> Error s with
  | Ok x -> write_lvals wsw ep spp true gd m lvs x
  | Error s -> Error s

(** val syscall_sem__ :
    'a1 syscall_sem -> coq_PointerData -> 'a1 syscall_state_t -> Memory.mem
    -> BinNums.positive Syscall_t.syscall_t -> values -> (('a1
    syscall_state_t * Memory.mem) * values) exec **)

let syscall_sem__ =
  exec_syscall_u
