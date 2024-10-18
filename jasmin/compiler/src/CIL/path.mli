open Ssrbool

val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list

val merge_sort_push : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list

val merge_sort_pop : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list

val merge_sort_rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

val sort : 'a1 rel -> 'a1 list -> 'a1 list
