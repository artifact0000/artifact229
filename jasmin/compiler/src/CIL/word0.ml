open BinInt
open BinNums
open BinPos
open Datatypes
open Nat0
open Div
open Eqtype
open Seq
open Ssralg
open Ssrint
open Ssrnat
open Ssrnum
open Tuple
open Utils0
open Word
open Word_ssrZ
open Wsize

(** val nat7 : nat **)

let nat7 =
  S (S (S (S (S (S (S O))))))

(** val nat15 : nat **)

let nat15 =
  S (S (S (S (S (S (S (S nat7)))))))

(** val nat31 : nat **)

let nat31 =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S nat15)))))))))))))))

(** val nat63 : nat **)

let nat63 =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S nat31)))))))))))))))))))))))))))))))

(** val nat127 : nat **)

let nat127 =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    nat63)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val nat255 : nat **)

let nat255 =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S
    nat127)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val wsize_size_minus_1 : wsize -> nat **)

let wsize_size_minus_1 = function
| U8 -> nat7
| U16 -> nat15
| U32 -> nat31
| U64 -> nat63
| U128 -> nat127
| U256 -> nat255

(** val nat_of_wsize : wsize -> nat **)

let nat_of_wsize sz =
  S (wsize_size_minus_1 sz)

(** val wsize_bits : wsize -> coq_Z **)

let wsize_bits s =
  Zpos (Pos.of_succ_nat (wsize_size_minus_1 s))

(** val wsize_size : wsize -> coq_Z **)

let wsize_size sz =
  Zpos
    (match sz with
     | U8 -> Coq_xH
     | U16 -> Coq_xO Coq_xH
     | U32 -> Coq_xO (Coq_xO Coq_xH)
     | U64 -> Coq_xO (Coq_xO (Coq_xO Coq_xH))
     | U128 -> Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
     | U256 -> Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))

(** val wsize_log2 : wsize -> nat **)

let wsize_log2 = function
| U8 -> O
| U16 -> S O
| U32 -> S (S O)
| U64 -> S (S (S O))
| U128 -> S (S (S (S O)))
| U256 -> S (S (S (S (S O))))

(** val wbase : wsize -> coq_Z **)

let wbase s =
  modulus (S (wsize_size_minus_1 s))

(** val nat_of_pelem : pelem -> nat **)

let nat_of_pelem = function
| PE1 -> S O
| PE2 -> S (S O)
| PE4 -> S (S (S (S O)))
| PE8 -> nat_of_wsize U8
| PE16 -> nat_of_wsize U16
| PE32 -> nat_of_wsize U32
| PE64 -> nat_of_wsize U64
| PE128 -> nat_of_wsize U128

(** val word : wsize -> GRing.ComRing.coq_type **)

let word sz =
  GRing.ComRing.clone (word_comRingType (wsize_size_minus_1 sz))
    (GRing.ComRing.coq_class (word_comRingType (wsize_size_minus_1 sz)))

(** val winit : wsize -> (nat -> bool) -> GRing.ComRing.sort **)

let winit ws f =
  let bits = map f (iota O (S (wsize_size_minus_1 ws))) in
  Obj.magic t2w (S (wsize_size_minus_1 ws)) bits

(** val wand :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wand s x y =
  Obj.magic wand (S (wsize_size_minus_1 s)) x y

(** val wor :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wor s x y =
  Obj.magic wor (S (wsize_size_minus_1 s)) x y

(** val wxor :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wxor s x y =
  Obj.magic wxor (S (wsize_size_minus_1 s)) x y

(** val wlt :
    wsize -> signedness -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool **)

let wlt sz sg x y =
  match sg with
  | Signed ->
    Order.Order.lt ring_display
      (Num.NumDomain.porderType coq_Z_numDomainType)
      (srepr (S (wsize_size_minus_1 sz)) (Obj.magic x))
      (srepr (S (wsize_size_minus_1 sz)) (Obj.magic y))
  | Unsigned ->
    Order.Order.lt ring_display coq_Z_porderType
      (Obj.magic urepr (S (wsize_size_minus_1 sz)) x)
      (Obj.magic urepr (S (wsize_size_minus_1 sz)) y)

(** val wle :
    wsize -> signedness -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool **)

let wle sz sg x y =
  match sg with
  | Signed ->
    Order.Order.le ring_display
      (Num.NumDomain.porderType coq_Z_numDomainType)
      (srepr (S (wsize_size_minus_1 sz)) (Obj.magic x))
      (srepr (S (wsize_size_minus_1 sz)) (Obj.magic y))
  | Unsigned ->
    Order.Order.le ring_display coq_Z_porderType
      (Obj.magic urepr (S (wsize_size_minus_1 sz)) x)
      (Obj.magic urepr (S (wsize_size_minus_1 sz)) y)

(** val wnot : wsize -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wnot sz w =
  wxor sz w
    (GRing.opp (GRing.Ring.zmodType (GRing.ComRing.ringType (word sz)))
      (GRing.one (GRing.ComRing.ringType (word sz))))

(** val wandn :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wandn sz x y =
  wand sz (wnot sz x) y

(** val wunsigned : wsize -> GRing.ComRing.sort -> coq_Z **)

let wunsigned s w =
  urepr (S (wsize_size_minus_1 s)) (Obj.magic w)

(** val wsigned : wsize -> GRing.ComRing.sort -> coq_Z **)

let wsigned s w =
  Obj.magic srepr (S (wsize_size_minus_1 s)) w

(** val wrepr : wsize -> coq_Z -> GRing.ComRing.sort **)

let wrepr s z =
  Obj.magic mkword (S (wsize_size_minus_1 s)) z

(** val wshr : wsize -> GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wshr sz x n =
  Obj.magic mkword (nat_of_wsize sz) (Z.shiftr (wunsigned sz x) n)

(** val wshl : wsize -> GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wshl sz x n =
  Obj.magic mkword (nat_of_wsize sz) (Z.shiftl (wunsigned sz x) n)

(** val wsar : wsize -> GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wsar sz x n =
  Obj.magic mkword (nat_of_wsize sz) (Z.shiftr (wsigned sz x) n)

(** val high_bits : wsize -> coq_Z -> GRing.ComRing.sort **)

let high_bits sz n =
  wrepr sz (Z.shiftr n (wsize_bits sz))

(** val wmulhu :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wmulhu sz x y =
  high_bits sz (Z.mul (wunsigned sz x) (wunsigned sz y))

(** val wmulhs :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wmulhs sz x y =
  high_bits sz (Z.mul (wsigned sz x) (wsigned sz y))

(** val wmulhrs :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wmulhrs sz x y =
  wrepr sz
    (Z.shiftr
      (Obj.magic GRing.add coq_Z_zmodType
        (Z.shiftr (Z.mul (wsigned sz x) (wsigned sz y))
          (int_to_Z (Posz (pred (wsize_size_minus_1 sz)))))
        (GRing.one coq_Z_ringType)) (Zpos Coq_xH))

(** val wmax_unsigned : wsize -> coq_Z **)

let wmax_unsigned sz =
  Z.sub (wbase sz) (Zpos Coq_xH)

(** val wmin_signed : wsize -> coq_Z **)

let wmin_signed sz =
  Z.opp (modulus (wsize_size_minus_1 sz))

(** val wmax_signed : wsize -> coq_Z **)

let wmax_signed sz =
  Z.sub (modulus (wsize_size_minus_1 sz)) (Zpos Coq_xH)

(** val wbit_n : wsize -> GRing.ComRing.sort -> nat -> bool **)

let wbit_n sz w n =
  wbit (wunsigned sz w) n

(** val lsb : wsize -> GRing.ComRing.sort -> bool **)

let lsb s w =
  wbit_n s w O

(** val msb : wsize -> GRing.ComRing.sort -> bool **)

let msb s w =
  wbit_n s w (wsize_size_minus_1 s)

(** val wdwordu :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> coq_Z **)

let wdwordu sz hi lo =
  Z.add (Z.mul (wunsigned sz hi) (wbase sz)) (wunsigned sz lo)

(** val wdwords :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> coq_Z **)

let wdwords sz hi lo =
  Z.add (Z.mul (wsigned sz hi) (wbase sz)) (wunsigned sz lo)

(** val waddcarry :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool ->
    bool * GRing.ComRing.sort **)

let waddcarry sz x y c =
  let n = Z.add (Z.add (wunsigned sz x) (wunsigned sz y)) (Z.b2z c) in
  ((Z.leb (wbase sz) n), (wrepr sz n))

(** val wdaddu :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> GRing.ComRing.sort -> GRing.ComRing.sort * GRing.ComRing.sort **)

let wdaddu sz hi_1 lo_1 hi_2 lo_2 =
  let n = Z.add (wdwordu sz hi_1 lo_1) (wdwordu sz hi_2 lo_2) in
  ((wrepr sz n), (high_bits sz n))

(** val wdadds :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> GRing.ComRing.sort -> GRing.ComRing.sort * GRing.ComRing.sort **)

let wdadds sz hi_1 lo_1 hi_2 lo_2 =
  let n = Z.add (wdwords sz hi_1 lo_1) (wdwords sz hi_2 lo_2) in
  ((wrepr sz n), (high_bits sz n))

(** val wsubcarry :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool ->
    bool * GRing.ComRing.sort **)

let wsubcarry sz x y c =
  let n = Z.sub (Z.sub (wunsigned sz x) (wunsigned sz y)) (Z.b2z c) in
  ((Z.ltb n Z0), (wrepr sz n))

(** val wumul :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort * GRing.ComRing.sort **)

let wumul sz x y =
  let n = Z.mul (wunsigned sz x) (wunsigned sz y) in
  ((high_bits sz n), (wrepr sz n))

(** val wsmul :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort * GRing.ComRing.sort **)

let wsmul sz x y =
  let n = Z.mul (wsigned sz x) (wsigned sz y) in
  ((high_bits sz n), (wrepr sz n))

(** val wdiv :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wdiv sz p q =
  let p0 = wunsigned sz p in let q0 = wunsigned sz q in wrepr sz (Z.div p0 q0)

(** val wdivi :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wdivi sz p q =
  let p0 = wsigned sz p in let q0 = wsigned sz q in wrepr sz (Z.quot p0 q0)

(** val wmod :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wmod sz p q =
  let p0 = wunsigned sz p in
  let q0 = wunsigned sz q in wrepr sz (Z.modulo p0 q0)

(** val wmodi :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wmodi sz p q =
  let p0 = wsigned sz p in let q0 = wsigned sz q in wrepr sz (Z.rem p0 q0)

(** val zero_extend :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let zero_extend sz sz' w =
  wrepr sz (wunsigned sz' w)

(** val sign_extend :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let sign_extend sz sz' w =
  wrepr sz (wsigned sz' w)

(** val truncate_word :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort exec **)

let truncate_word s s' w =
  match gcmp wsize_cmp s s' with
  | Eq -> Ok w
  | Lt -> Ok (zero_extend s s' w)
  | Gt -> type_error

(** val wbit : wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool **)

let wbit sz w i =
  wbit_n sz w (Z.to_nat (Z.modulo (wunsigned sz i) (wsize_bits sz)))

(** val wror : wsize -> GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wror sz w z =
  let i = Z.modulo z (wsize_bits sz) in
  wor sz (wshr sz w i) (wshl sz w (Z.sub (wsize_bits sz) i))

(** val wrol : wsize -> GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wrol sz w z =
  let i = Z.modulo z (wsize_bits sz) in
  wor sz (wshl sz w i) (wshr sz w (Z.sub (wsize_bits sz) i))

(** val check_scale : coq_Z -> bool **)

let check_scale s =
  (||)
    ((||)
      ((||) (eq_op coq_Z_eqType (Obj.magic s) (Obj.magic (Zpos Coq_xH)))
        (eq_op coq_Z_eqType (Obj.magic s) (Obj.magic (Zpos (Coq_xO Coq_xH)))))
      (eq_op coq_Z_eqType (Obj.magic s)
        (Obj.magic (Zpos (Coq_xO (Coq_xO Coq_xH))))))
    (eq_op coq_Z_eqType (Obj.magic s)
      (Obj.magic (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))

(** val split_vec : wsize -> nat -> GRing.ComRing.sort -> word list **)

let split_vec sz ve w =
  let wsz = addn (divn (nat_of_wsize sz) ve) (modn (nat_of_wsize sz) ve) in
  map (fun i ->
    subword (S (wsize_size_minus_1 sz)) (muln i ve) ve (Obj.magic w))
    (iota O wsz)

(** val make_vec :
    wsize -> wsize -> GRing.ComRing.sort list -> GRing.ComRing.sort **)

let make_vec sz sz' s =
  wrepr sz' (wcat_r (S (wsize_size_minus_1 sz)) (Obj.magic s))

(** val lift1_vec' :
    wsize -> wsize -> (GRing.ComRing.sort -> GRing.ComRing.sort) -> wsize ->
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let lift1_vec' ve ve' op sz sz' w =
  make_vec ve' sz' (map (Obj.magic op) (split_vec sz (nat_of_wsize ve) w))

(** val lift1_vec :
    wsize -> (GRing.ComRing.sort -> GRing.ComRing.sort) -> wsize ->
    GRing.ComRing.sort -> GRing.ComRing.sort **)

let lift1_vec ve op sz w =
  lift1_vec' ve ve op sz sz w

(** val lift2_vec :
    wsize -> (GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort)
    -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let lift2_vec ve op sz w1 w2 =
  make_vec ve sz
    (map2 (Obj.magic op) (split_vec sz (nat_of_wsize ve) w1)
      (split_vec sz (nat_of_wsize ve) w2))

(** val wbswap : wsize -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wbswap sz w =
  make_vec U8 sz (rev (Obj.magic split_vec sz (nat_of_wsize U8) w))

(** val popcnt : wsize -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let popcnt sz w =
  wrepr sz
    (int_to_Z (Posz
      (count (fun x -> x)
        (tval (S (wsize_size_minus_1 sz))
          (w2t (S (wsize_size_minus_1 sz)) (Obj.magic w))))))

(** val pextr :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let pextr sz w1 w2 =
  wrepr sz
    (toword
      (size
        (mask
          (tval (S (wsize_size_minus_1 sz))
            (w2t (S (wsize_size_minus_1 sz)) (Obj.magic w2)))
          (tval (S (wsize_size_minus_1 sz))
            (w2t (S (wsize_size_minus_1 sz)) (Obj.magic w1)))))
      (t2w
        (size
          (mask
            (tval (S (wsize_size_minus_1 sz))
              (w2t (S (wsize_size_minus_1 sz)) (Obj.magic w2)))
            (tval (S (wsize_size_minus_1 sz))
              (w2t (S (wsize_size_minus_1 sz)) (Obj.magic w1)))))
        (in_tuple
          (mask
            (tval (S (wsize_size_minus_1 sz))
              (w2t (S (wsize_size_minus_1 sz)) (Obj.magic w2)))
            (tval (S (wsize_size_minus_1 sz))
              (w2t (S (wsize_size_minus_1 sz)) (Obj.magic w1)))))))

(** val bitpdep :
    wsize -> GRing.ComRing.sort -> nat -> bitseq -> bool list **)

let rec bitpdep sz w i = function
| [] -> []
| b :: mask1 ->
  if b
  then (wbit_n sz w i) :: (bitpdep sz w (S i) mask1)
  else false :: (bitpdep sz w i mask1)

(** val pdep :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let pdep sz w1 w2 =
  wrepr sz
    (toword
      (size
        (bitpdep sz w1 O
          (tval (S (wsize_size_minus_1 sz))
            (w2t (S (wsize_size_minus_1 sz)) (Obj.magic w2)))))
      (t2w
        (size
          (bitpdep sz w1 O
            (tval (S (wsize_size_minus_1 sz))
              (w2t (S (wsize_size_minus_1 sz)) (Obj.magic w2)))))
        (in_tuple
          (bitpdep sz w1 O
            (tval (S (wsize_size_minus_1 sz))
              (w2t (S (wsize_size_minus_1 sz)) (Obj.magic w2)))))))

(** val leading_zero_aux : coq_Z -> nat -> nat -> nat **)

let rec leading_zero_aux n res sz =
  if Z.ltb n
       (Z.pow (Zpos (Coq_xO Coq_xH))
         (Z.sub (int_to_Z (Posz sz)) (int_to_Z (Posz res))))
  then res
  else (match res with
        | O -> O
        | S res' -> leading_zero_aux n res' sz)

(** val leading_zero : wsize -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let leading_zero sz w =
  wrepr sz
    (int_to_Z (Posz
      (leading_zero_aux (wunsigned sz w) (nat_of_wsize sz) (nat_of_wsize sz))))

(** val halve_list : 'a1 list -> 'a1 list **)

let rec halve_list m = match m with
| [] -> m
| a :: l -> (match l with
             | [] -> m
             | _ :: m' -> a :: (halve_list m'))

(** val wpmul :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpmul sz x y =
  let xs = halve_list (split_vec sz (nat_of_wsize U32) x) in
  let ys = halve_list (split_vec sz (nat_of_wsize U32) y) in
  let f = fun a b -> wrepr U64 (Z.mul (wsigned U32 a) (wsigned U32 b)) in
  make_vec U64 sz (map2 (Obj.magic f) xs ys)

(** val wpmulu :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpmulu sz x y =
  let xs = halve_list (split_vec sz (nat_of_wsize U32) x) in
  let ys = halve_list (split_vec sz (nat_of_wsize U32) y) in
  let f = fun a b -> wrepr U64 (Z.mul (wunsigned U32 a) (wunsigned U32 b)) in
  make_vec U64 sz (map2 (Obj.magic f) xs ys)

(** val wpshufb1 :
    GRing.ComRing.sort list -> GRing.ComRing.sort -> GRing.Zmodule.sort **)

let wpshufb1 s idx =
  if msb U8 idx
  then GRing.zero (GRing.ComRing.zmodType (word U8))
  else let off =
         wunsigned U8
           (wand U8 idx
             (GRing.add (GRing.ComRing.zmodType (word U8))
               (wshl U8 (GRing.one (GRing.ComRing.ringType (word U8))) (Zpos
                 (Coq_xO (Coq_xO Coq_xH))))
               (GRing.opp
                 (GRing.Ring.zmodType (GRing.ComRing.ringType (word U8)))
                 (GRing.one (GRing.ComRing.ringType (word U8))))))
       in
       nth (GRing.zero (GRing.ComRing.zmodType (word U8))) s (Z.to_nat off)

(** val wpshufb :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpshufb sz w idx =
  let s = split_vec sz (S (S (S (S (S (S (S (S O)))))))) w in
  let i = split_vec sz (S (S (S (S (S (S (S (S O)))))))) idx in
  let r = map (Obj.magic wpshufb1 s) i in make_vec U8 sz r

(** val wpshufd1 : GRing.ComRing.sort -> GRing.ComRing.sort -> nat -> word **)

let wpshufd1 s o i =
  subword (S (wsize_size_minus_1 U128)) O (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))
    (Obj.magic wshr U128 s
      (Z.mul (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
        (urepr (S (S O))
          (subword (S (wsize_size_minus_1 U8)) (muln (S (S O)) i) (S (S O))
            (Obj.magic o)))))

(** val wpshufd_128 : GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wpshufd_128 s o =
  let o0 = wrepr U8 o in
  let d = map (fun i -> wpshufd1 s o0 i) (iota O (S (S (S (S O))))) in
  wrepr U128
    (wcat_r (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) d)

(** val wpshufd_256 : GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wpshufd_256 s o =
  make_vec U128 U256
    (map (fun w -> wpshufd_128 (Obj.magic w) o)
      (split_vec U256 (nat_of_wsize U128) s))

(** val wpshufd :
    wsize -> GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wpshufd = function
| U128 -> wpshufd_128
| U256 -> wpshufd_256
| _ -> (fun w _ -> w)

(** val wpshufl_u64 : GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wpshufl_u64 w z =
  let v = split_vec U64 (nat_of_wsize U16) w in
  let j = split_vec U8 (S (S O)) (wrepr U8 z) in
  make_vec U16 U64
    (map (fun n ->
      nth (GRing.zero (word_ordType (nat_of_wsize U16))) (Obj.magic v)
        (Z.to_nat (urepr (S (S O)) n))) j)

(** val wpshufl_u128 : GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wpshufl_u128 w z =
  match split_vec U128 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) w with
  | [] -> w
  | l :: l0 ->
    (match l0 with
     | [] -> w
     | h :: l1 ->
       (match l1 with
        | [] ->
          make_vec U64 U128
            ((wpshufl_u64 (Obj.magic l) z) :: ((Obj.magic h) :: []))
        | _ :: _ -> w))

(** val wpshufh_u128 : GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wpshufh_u128 w z =
  match split_vec U128 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) w with
  | [] -> w
  | l :: l0 ->
    (match l0 with
     | [] -> w
     | h :: l1 ->
       (match l1 with
        | [] ->
          make_vec U64 U128
            ((Obj.magic l) :: ((wpshufl_u64 (Obj.magic h) z) :: []))
        | _ :: _ -> w))

(** val wpshufl_u256 : GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wpshufl_u256 s z =
  make_vec U128 U256
    (map (fun w -> wpshufl_u128 (Obj.magic w) z)
      (split_vec U256 (nat_of_wsize U128) s))

(** val wpshufh_u256 : GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wpshufh_u256 s z =
  make_vec U128 U256
    (map (fun w -> wpshufh_u128 (Obj.magic w) z)
      (split_vec U256 (nat_of_wsize U128) s))

(** val wpshuflw :
    wsize -> GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wpshuflw = function
| U128 -> wpshufl_u128
| U256 -> wpshufl_u256
| _ -> (fun w _ -> w)

(** val wpshufhw :
    wsize -> GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort **)

let wpshufhw = function
| U128 -> wpshufh_u128
| U256 -> wpshufh_u256
| _ -> (fun w _ -> w)

(** val interleave : 'a1 list -> 'a1 list -> 'a1 list **)

let rec interleave l1 l2 =
  match l1 with
  | [] -> l2
  | a1 :: l3 ->
    (match l2 with
     | [] -> l1
     | a2 :: l4 -> a1 :: (a2 :: (interleave l3 l4)))

(** val interleave_gen :
    (GRing.ComRing.sort -> GRing.ComRing.sort) -> velem -> GRing.ComRing.sort
    -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let interleave_gen get ve src1 src2 =
  let ve0 = nat_of_wsize (wsize_of_velem ve) in
  let l1 = split_vec U64 ve0 (get src1) in
  let l2 = split_vec U64 ve0 (get src2) in
  make_vec (wsize_of_velem ve) U128 (interleave (Obj.magic l1) (Obj.magic l2))

(** val wpunpckl_128 :
    velem -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpunpckl_128 =
  interleave_gen
    (Obj.magic subword (S (wsize_size_minus_1 U128)) O (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val wpunpckl_256 :
    velem -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpunpckl_256 ve src1 src2 =
  make_vec U128 U256
    (map2 (Obj.magic wpunpckl_128 ve)
      (split_vec U256 (nat_of_wsize U128) src1)
      (split_vec U256 (nat_of_wsize U128) src2))

(** val wpunpckh_128 :
    velem -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpunpckh_128 =
  interleave_gen
    (Obj.magic subword (S (wsize_size_minus_1 U128)) (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val wpunpckh_256 :
    velem -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpunpckh_256 ve src1 src2 =
  make_vec U128 U256
    (map2 (Obj.magic wpunpckh_128 ve)
      (split_vec U256 (nat_of_wsize U128) src1)
      (split_vec U256 (nat_of_wsize U128) src2))

(** val wpunpckl :
    wsize -> velem -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let wpunpckl = function
| U128 -> wpunpckl_128
| U256 -> wpunpckl_256
| _ -> (fun _ w1 _ -> w1)

(** val wpunpckh :
    wsize -> velem -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let wpunpckh = function
| U128 -> wpunpckh_128
| U256 -> wpunpckh_256
| _ -> (fun _ w1 _ -> w1)

(** val update_at : 'a1 -> 'a1 list -> nat -> 'a1 list **)

let rec update_at t xs i =
  match xs with
  | [] -> []
  | x :: xs' ->
    (match i with
     | O -> t :: xs'
     | S i' -> x :: (update_at t xs' i'))

(** val wpinsr :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> GRing.ComRing.sort **)

let wpinsr ve v w i =
  let v0 = split_vec U128 (nat_of_wsize ve) v in
  let i0 = Z.to_nat (wunsigned U8 i) in
  make_vec ve U128 (update_at w (Obj.magic v0) i0)

(** val winserti128 :
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let winserti128 v w i =
  let v0 = split_vec U256 (nat_of_wsize U128) v in
  make_vec U128 U256
    (if lsb U8 i
     then (nth (GRing.zero (word_ordType (nat_of_wsize U128))) (Obj.magic v0)
            O) :: (w :: [])
     else w :: ((nth (GRing.zero (word_ordType (nat_of_wsize U128)))
                  (Obj.magic v0) (S O)) :: []))

(** val wpblendd :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> GRing.ComRing.sort **)

let wpblendd sz w1 w2 m =
  let v1 = split_vec sz (nat_of_wsize U32) w1 in
  let v2 = split_vec sz (nat_of_wsize U32) w2 in
  let b = split_vec U8 (S O) m in
  let r =
    map3 (fun b0 v3 v4 ->
      if eq_op (GRing.Ring.eqType (word_ringType O)) (Obj.magic b0)
           (GRing.one (word_ringType O))
      then v4
      else v3) b v1 v2
  in
  make_vec U32 sz (Obj.magic r)

(** val wpbroadcast :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpbroadcast ve sz w =
  let r = nseq (divn (nat_of_wsize sz) (nat_of_wsize ve)) w in
  make_vec ve sz r

(** val seq_dup_hi : 'a1 list -> 'a1 list **)

let rec seq_dup_hi = function
| [] -> []
| _ :: l -> (match l with
             | [] -> []
             | a :: m' -> a :: (a :: (seq_dup_hi m')))

(** val seq_dup_lo : 'a1 list -> 'a1 list **)

let rec seq_dup_lo = function
| [] -> []
| a :: l -> (match l with
             | [] -> []
             | _ :: m' -> a :: (a :: (seq_dup_lo m')))

(** val wdup_hi :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wdup_hi ve sz w =
  let v = split_vec sz (nat_of_wsize ve) w in
  make_vec ve sz (seq_dup_hi (Obj.magic v))

(** val wdup_lo :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wdup_lo ve sz w =
  let v = split_vec sz (nat_of_wsize ve) w in
  make_vec ve sz (seq_dup_lo (Obj.magic v))

(** val wperm2i128 :
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let wperm2i128 w1 w2 i =
  let choose = fun n ->
    match urepr (S (S O))
            (subword (S (wsize_size_minus_1 U8)) n (S (S O)) (Obj.magic i)) with
    | Z0 ->
      subword (S (wsize_size_minus_1 U256)) O (nat_of_wsize U128)
        (Obj.magic w1)
    | Zpos p ->
      (match p with
       | Coq_xI _ ->
         subword (S (wsize_size_minus_1 U256)) (nat_of_wsize U128)
           (nat_of_wsize U128) (Obj.magic w2)
       | Coq_xO p0 ->
         (match p0 with
          | Coq_xH ->
            subword (S (wsize_size_minus_1 U256)) O (nat_of_wsize U128)
              (Obj.magic w2)
          | _ ->
            subword (S (wsize_size_minus_1 U256)) (nat_of_wsize U128)
              (nat_of_wsize U128) (Obj.magic w2))
       | Coq_xH ->
         subword (S (wsize_size_minus_1 U256)) (nat_of_wsize U128)
           (nat_of_wsize U128) (Obj.magic w1))
    | Zneg _ ->
      subword (S (wsize_size_minus_1 U256)) (nat_of_wsize U128)
        (nat_of_wsize U128) (Obj.magic w2)
  in
  let lo =
    if wbit_n U8 i (S (S (S O)))
    then GRing.zero (word_ordType (nat_of_wsize U128))
    else Obj.magic choose O
  in
  let hi =
    if wbit_n U8 i (S (S (S (S (S (S (S O)))))))
    then GRing.zero (word_ordType (nat_of_wsize U128))
    else Obj.magic choose (S (S (S (S O))))
  in
  make_vec U128 U256 (lo :: (hi :: []))

(** val wpermd1 :
    GRing.ComRing.sort list -> GRing.ComRing.sort -> GRing.Zmodule.sort **)

let wpermd1 v idx =
  let off =
    Z.modulo (wunsigned U32 idx) (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
  in
  nth (GRing.zero (GRing.ComRing.zmodType (word U32))) v (Z.to_nat off)

(** val wpermd :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpermd sz idx w =
  let v = split_vec sz (nat_of_wsize U32) w in
  let i = split_vec sz (nat_of_wsize U32) idx in
  make_vec U32 sz (map (Obj.magic wpermd1 v) i)

(** val wpermq :
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpermq w i =
  let v = split_vec U256 (nat_of_wsize U64) w in
  let j = split_vec U8 (S (S O)) i in
  make_vec U64 U256
    (map (fun n ->
      nth (GRing.zero (word_ordType (nat_of_wsize U64))) (Obj.magic v)
        (Z.to_nat (urepr (S (S O)) n))) j)

(** val wpsxldq :
    (GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort) -> wsize ->
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpsxldq op sz w i =
  let n =
    Z.mul
      (Z.min (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
        (wunsigned U8 i)) (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
  in
  lift1_vec U128 (fun w0 -> op w0 n) sz w

(** val wpslldq :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpslldq =
  wpsxldq (wshl U128)

(** val wpsrldq :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpsrldq =
  wpsxldq (wshr U128)

(** val wpcmps1 :
    (coq_Z -> coq_Z -> bool) -> wsize -> GRing.ComRing.sort ->
    GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpcmps1 cmp ve x y =
  if cmp (wsigned ve x) (wsigned ve y)
  then GRing.opp (GRing.Ring.zmodType (GRing.ComRing.ringType (word ve)))
         (GRing.one (GRing.ComRing.ringType (word ve)))
  else GRing.zero (GRing.Ring.zmodType (GRing.ComRing.ringType (word ve)))

(** val wpcmpeq :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let wpcmpeq ve sz w1 w2 =
  lift2_vec ve (wpcmps1 Z.eqb ve) sz w1 w2

(** val wpcmpgt :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let wpcmpgt ve sz w1 w2 =
  lift2_vec ve (wpcmps1 Z.gtb ve) sz w1 w2

(** val wminmax1 :
    wsize -> (GRing.ComRing.sort -> GRing.ComRing.sort -> bool) ->
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wminmax1 _ cmp x y =
  if cmp x y then x else y

(** val wmin :
    signedness -> wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> GRing.ComRing.sort **)

let wmin sg ve sz x y =
  lift2_vec ve (wminmax1 ve (wlt ve sg)) sz x y

(** val wmax :
    signedness -> wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> GRing.ComRing.sort **)

let wmax sg ve sz x y =
  lift2_vec ve (wminmax1 ve (fun u v -> wlt ve sg v u)) sz x y

(** val saturated_signed : wsize -> coq_Z -> coq_Z **)

let saturated_signed sz x =
  Z.max (wmin_signed sz) (Z.min (wmax_signed sz) x)

(** val wrepr_saturated_signed : wsize -> coq_Z -> GRing.ComRing.sort **)

let wrepr_saturated_signed sz x =
  wrepr sz (saturated_signed sz x)

(** val add_pairs : coq_Z list -> coq_Z list **)

let rec add_pairs = function
| [] -> []
| x :: l -> (match l with
             | [] -> []
             | y :: z -> (Z.add x y) :: (add_pairs z))

(** val wpmaddubsw :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpmaddubsw sz v1 v2 =
  let w1 = map (Obj.magic wunsigned U8) (split_vec sz (nat_of_wsize U8) v1) in
  let w2 = map (Obj.magic wsigned U8) (split_vec sz (nat_of_wsize U8) v2) in
  let result =
    map (fun z -> wrepr_saturated_signed U16 z)
      (add_pairs (map2 (Obj.magic GRing.mul coq_Z_ringType) w1 w2))
  in
  make_vec U16 sz result

(** val wpmaddwd :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpmaddwd sz v1 v2 =
  let w1 = map (Obj.magic wsigned U16) (split_vec sz (nat_of_wsize U16) v1) in
  let w2 = map (Obj.magic wsigned U16) (split_vec sz (nat_of_wsize U16) v2) in
  let result =
    map (fun z -> wrepr U32 z)
      (add_pairs (map2 (Obj.magic GRing.mul coq_Z_ringType) w1 w2))
  in
  make_vec U32 sz result

(** val wpack : wsize -> nat -> coq_Z list -> GRing.ComRing.sort **)

let wpack sz pe arg =
  let w = map (mkword pe) arg in wrepr sz (wcat_r pe w)

(** val wpmovmskb :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wpmovmskb dsz ssz w =
  wrepr dsz
    (t2w_def
      (addn (divn (nat_of_wsize ssz) (nat_of_wsize U8))
        (modn (nat_of_wsize ssz) (nat_of_wsize U8)))
      (tuple
        (addn (divn (nat_of_wsize ssz) (nat_of_wsize U8))
          (modn (nat_of_wsize ssz) (nat_of_wsize U8)))
        (map_tuple
          (addn (divn (nat_of_wsize ssz) (nat_of_wsize U8))
            (modn (nat_of_wsize ssz) (nat_of_wsize U8))) (Obj.magic msb U8)
          (map_tuple
            (addn (divn (nat_of_wsize ssz) (nat_of_wsize U8))
              (modn (nat_of_wsize ssz) (nat_of_wsize U8))) (fun i ->
            subword (S (wsize_size_minus_1 ssz)) (muln i (nat_of_wsize U8))
              (nat_of_wsize U8) (Obj.magic w))
            (iota_tuple
              (addn (divn (nat_of_wsize ssz) (nat_of_wsize U8))
                (modn (nat_of_wsize ssz) (nat_of_wsize U8))) O))) (fun _ ->
        map (Obj.magic msb U8) (split_vec ssz (nat_of_wsize U8) w))))

(** val wpblendvb :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> GRing.ComRing.sort **)

let wpblendvb sz w1 w2 m =
  let v1 = split_vec sz (nat_of_wsize U8) w1 in
  let v2 = split_vec sz (nat_of_wsize U8) w2 in
  let b = map (Obj.magic msb U8) (split_vec sz (nat_of_wsize U8) m) in
  let r = map3 (fun bi v1i v2i -> if bi then v2i else v1i) b v1 v2 in
  make_vec U8 sz (Obj.magic r)

(** val align_word :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let align_word sz sz' p =
  wand sz p (wrepr sz (Z.opp (wsize_size sz')))
