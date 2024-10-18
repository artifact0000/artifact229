open Datatypes
open Eqtype
open Type
open Utils0

type __ = Obj.t

type coq_WithSubWord =
  bool
  (* singleton inductive, whose constructor was Build_WithSubWord *)

val sw_allowed : coq_WithSubWord -> bool

val nosubword : coq_WithSubWord

val withsubword : coq_WithSubWord

val compat_type : bool -> stype -> stype -> bool

type sem_t = __

type 'tr sem_prod = 'tr lprod

type sem_ot = __

type sem_tuple = ltuple

val curry : stype -> nat -> (sem_t list -> 'a1) -> 'a1 sem_prod

val sem_prod_const : stype list -> 'a1 -> 'a1 sem_prod

val sem_prod_id : stype -> sem_t -> sem_ot

val sem_prod_app : stype list -> 'a1 sem_prod -> ('a1 -> 'a2) -> 'a2 sem_prod

val sem_prod_tuple : stype list -> sem_tuple sem_prod

val add_arguments :
  stype list -> stype list -> 'a1 sem_prod sem_prod -> 'a1 sem_prod

val behead_tuple :
  stype list -> stype list -> sem_tuple exec sem_prod -> sem_tuple exec
  sem_prod

val app_sopn :
  (stype -> 'a1 -> sem_t exec) -> stype list -> 'a2 exec sem_prod -> 'a1 list
  -> 'a2 exec
