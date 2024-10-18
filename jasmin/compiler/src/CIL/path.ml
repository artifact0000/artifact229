open Ssrbool

(** val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list **)

let rec merge leT s1 = match s1 with
| [] -> (fun x -> x)
| x1 :: s1' ->
  let rec merge_s1 s2 = match s2 with
  | [] -> s1
  | x2 :: s2' ->
    if leT x1 x2 then x1 :: (merge leT s1' s2) else x2 :: (merge_s1 s2')
  in merge_s1

(** val merge_sort_push :
    'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list **)

let rec merge_sort_push leT s1 ss = match ss with
| [] -> s1 :: ss
| s2 :: ss' ->
  (match s2 with
   | [] -> s1 :: ss'
   | _ :: _ -> [] :: (merge_sort_push leT (merge leT s2 s1) ss'))

(** val merge_sort_pop : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list **)

let rec merge_sort_pop leT s1 = function
| [] -> s1
| s2 :: ss' -> merge_sort_pop leT (merge leT s2 s1) ss'

(** val merge_sort_rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

let rec merge_sort_rec leT ss s = match s with
| [] -> merge_sort_pop leT s ss
| x1 :: l ->
  (match l with
   | [] -> merge_sort_pop leT s ss
   | x2 :: s' ->
     let s1 = if leT x1 x2 then x1 :: (x2 :: []) else x2 :: (x1 :: []) in
     merge_sort_rec leT (merge_sort_push leT s1 ss) s')

(** val sort : 'a1 rel -> 'a1 list -> 'a1 list **)

let sort leT =
  merge_sort_rec leT []
