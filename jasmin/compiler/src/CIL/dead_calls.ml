open Datatypes
open Compiler_util
open Expr
open Seq
open Sopn
open Utils0
open Var0

module E =
 struct
  (** val pass : char list **)

  let pass =
    'd'::('e'::('a'::('d'::(' '::('c'::('a'::('l'::('l'::('s'::[])))))))))

  (** val dead_calls_error : char list -> pp_error_loc **)

  let dead_calls_error =
    pp_internal_error_s pass
 end

(** val i_calls : 'a1 asmOp -> Sf.t -> 'a1 instr -> Sf.t **)

let i_calls _ =
  let rec i_calls0 c = function
  | MkI (_, i0) -> i_calls_r c i0
  and i_calls_r c i =
    let c_calls0 =
      let rec c_calls0 c0 = function
      | [] -> c0
      | i0 :: cmd' -> c_calls0 (i_calls0 c0 i0) cmd'
      in c_calls0
    in
    (match i with
     | Cif (_, c1, c2) -> c_calls0 (c_calls0 c c1) c2
     | Cfor (_, _, c1) -> c_calls0 c c1
     | Cwhile (_, c1, _, c2) -> c_calls0 (c_calls0 c c1) c2
     | Ccall (_, f, _) -> Sf.add (Obj.magic f) c
     | _ -> c)
  in i_calls0

(** val c_calls : 'a1 asmOp -> Sf.t -> 'a1 instr list -> Sf.t **)

let c_calls asmop c cmd =
  foldl (i_calls asmop) c cmd

(** val live_calls :
    'a1 asmOp -> progT -> Sf.t -> 'a1 fun_decl list -> Sf.t **)

let live_calls asmop _ s p =
  foldl (fun c x ->
    let (n, d) = x in
    if Sf.mem (Obj.magic n) c then c_calls asmop c d.f_body else c) s p

(** val dead_calls :
    'a1 asmOp -> progT -> Sf.t -> 'a1 fun_decl list -> (Sf.elt * 'a1 fundef)
    list **)

let dead_calls _ _ k p =
  filter (fun x -> Sf.mem (fst x) k) (Obj.magic p)

(** val dead_calls_err :
    'a1 asmOp -> progT -> Sf.t -> 'a1 prog -> 'a1 prog cexec **)

let dead_calls_err asmop pT c p =
  let fds = p.p_funcs in
  let k = live_calls asmop pT c fds in
  if Sf.subset (live_calls asmop pT k fds) k
  then Ok { p_funcs = (Obj.magic dead_calls asmop pT k fds); p_globs =
         p.p_globs; p_extra = p.p_extra }
  else Error
         (E.dead_calls_error
           ('p'::('r'::('o'::('g'::('r'::('a'::('m'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('t'::('o'::('p'::('o'::('l'::('o'::('g'::('i'::('c'::('a'::('l'::(' '::('s'::('o'::('r'::('t'::('i'::('n'::('g'::(' '::('o'::('f'::(' '::('t'::('h'::('e'::(' '::('c'::('a'::('l'::('l'::('-'::('g'::('r'::('a'::('p'::('h'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val dead_calls_err_seq :
    'a1 asmOp -> progT -> funname list -> 'a1 prog -> 'a1 prog cexec **)

let dead_calls_err_seq asmop pT c p =
  dead_calls_err asmop pT
    (foldl (fun f c0 -> Sf.add (Obj.magic c0) f) Sf.empty c) p
