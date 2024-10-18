open BinNums
open Datatypes
open Eqtype
open Sem_type
open Ssralg
open Type
open Utils0
open Warray_
open Word0
open Wsize

val undef_t : stype -> stype

type value =
| Vbool of bool
| Vint of coq_Z
| Varr of positive * WArray.array
| Vword of wsize * GRing.ComRing.sort
| Vundef of stype

val undef_v : stype -> value

val undef_addr : stype -> value

type values = value list

val is_defined : value -> bool

val type_of_val : value -> stype

val coq_DB : bool -> value -> bool

val to_bool : value -> (error, bool) result

val to_int : value -> (error, coq_Z) result

val to_arr : positive -> value -> sem_t exec

val to_word : wsize -> value -> GRing.ComRing.sort exec

val of_val : stype -> value -> sem_t exec

val to_val : stype -> sem_t -> value

val oto_val : stype -> sem_ot -> value

val truncate_val : stype -> value -> value exec

val list_ltuple : stype list -> sem_tuple -> values

val app_sopn : stype list -> 'a1 exec sem_prod -> value list -> 'a1 exec

val swap_semi : stype -> sem_t -> sem_t -> sem_tuple exec
