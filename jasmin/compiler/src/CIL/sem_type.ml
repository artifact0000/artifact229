open Datatypes
open Eqtype
open Type
open Utils0

type __ = Obj.t

type coq_WithSubWord =
  bool
  (* singleton inductive, whose constructor was Build_WithSubWord *)

(** val sw_allowed : coq_WithSubWord -> bool **)

let sw_allowed withSubWord =
  withSubWord

(** val nosubword : coq_WithSubWord **)

let nosubword =
  false

(** val withsubword : coq_WithSubWord **)

let withsubword =
  true

(** val compat_type : bool -> stype -> stype -> bool **)

let compat_type = function
| true -> subtype
| false -> Obj.magic eq_op stype_eqType

type sem_t = __

type 'tr sem_prod = 'tr lprod

type sem_ot = __

type sem_tuple = ltuple

(** val curry : stype -> nat -> (sem_t list -> 'a1) -> 'a1 sem_prod **)

let curry _ n f =
  let rec loop = function
  | O -> Obj.magic f
  | S n' -> (fun acc -> Obj.magic (fun a -> loop n' (a :: acc)))
  in loop n []

(** val sem_prod_const : stype list -> 'a1 -> 'a1 sem_prod **)

let rec sem_prod_const lt a =
  match lt with
  | [] -> Obj.magic a
  | _ :: lt' -> Obj.magic (fun _ -> sem_prod_const lt' a)

(** val sem_prod_id : stype -> sem_t -> sem_ot **)

let sem_prod_id = function
| Coq_sbool -> Obj.magic (fun x -> Some x)
| _ -> (fun x -> x)

(** val sem_prod_app :
    stype list -> 'a1 sem_prod -> ('a1 -> 'a2) -> 'a2 sem_prod **)

let rec sem_prod_app lt a g =
  match lt with
  | [] -> Obj.magic g a
  | _ :: lt' -> Obj.magic (fun x -> sem_prod_app lt' (Obj.magic a x) g)

(** val sem_prod_tuple : stype list -> sem_tuple sem_prod **)

let rec sem_prod_tuple = function
| [] -> Obj.magic ()
| t :: lt' ->
  let f = fun x ->
    match lt' with
    | [] -> sem_prod_id t
    | s :: l ->
      (fun x0 -> sem_prod_app (s :: l) x (fun p -> ((sem_prod_id t x0), p)))
  in
  Obj.magic f (sem_prod_tuple lt')

(** val add_arguments :
    stype list -> stype list -> 'a1 sem_prod sem_prod -> 'a1 sem_prod **)

let add_arguments _ _ f =
  f

(** val behead_tuple :
    stype list -> stype list -> sem_tuple exec sem_prod -> sem_tuple exec
    sem_prod **)

let behead_tuple tin tout f =
  match tout with
  | [] ->
    sem_prod_app tin f (fun x ->
      match x with
      | Ok _ -> Ok ()
      | Error s -> Error s)
  | _ :: tout' ->
    (match tout' with
     | [] ->
       sem_prod_app tin f (fun x ->
         match x with
         | Ok _ -> Ok ()
         | Error s -> Error s)
     | _ :: _ ->
       sem_prod_app tin f (fun x ->
         match x with
         | Ok x0 -> let (_, p) = x0 in Ok p
         | Error s -> Error s))

(** val app_sopn :
    (stype -> 'a1 -> sem_t exec) -> stype list -> 'a2 exec sem_prod -> 'a1
    list -> 'a2 exec **)

let rec app_sopn of_T ts x x0 =
  match ts with
  | [] -> (match x0 with
           | [] -> Obj.magic x
           | _ :: _ -> type_error)
  | t :: ts0 ->
    (match x0 with
     | [] -> type_error
     | v :: vs ->
       (match of_T t v with
        | Ok x1 -> app_sopn of_T ts0 (Obj.magic x x1) vs
        | Error s -> Error s))
