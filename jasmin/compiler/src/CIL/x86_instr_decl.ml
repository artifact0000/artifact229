open BinInt
open BinNums
open Datatypes
open List0
open Nat0
open String0
open Arch_decl
open Eqtype
open Expr
open Sem_type
open Seq
open Sopn
open Ssralg
open Ssrbool
open Ssrint
open Ssrnat
open Tuple
open Type
open Utils0
open Waes
open Word0
open Word
open Word_ssrZ
open Wsize
open X86_decl

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type x86_op =
| MOV of wsize
| MOVSX of wsize * wsize
| MOVZX of wsize * wsize
| CMOVcc of wsize
| XCHG of wsize
| ADD of wsize
| SUB of wsize
| MUL of wsize
| IMUL of wsize
| IMULr of wsize
| IMULri of wsize
| DIV of wsize
| IDIV of wsize
| CQO of wsize
| ADC of wsize
| SBB of wsize
| NEG of wsize
| INC of wsize
| DEC of wsize
| LZCNT of wsize
| SETcc
| BT of wsize
| CLC
| STC
| LEA of wsize
| TEST of wsize
| CMP of wsize
| AND of wsize
| ANDN of wsize
| OR of wsize
| XOR of wsize
| NOT of wsize
| ROR of wsize
| ROL of wsize
| RCR of wsize
| RCL of wsize
| SHL of wsize
| SHR of wsize
| SAL of wsize
| SAR of wsize
| SHLD of wsize
| SHRD of wsize
| MULX_lo_hi of wsize
| ADCX of wsize
| ADOX of wsize
| BSWAP of wsize
| POPCNT of wsize
| PEXT of wsize
| PDEP of wsize
| MOVX of wsize
| MOVD of wsize
| MOVV of wsize
| VMOV of wsize
| VMOVDQA of wsize
| VMOVDQU of wsize
| VPMOVSX of velem * wsize * velem * wsize
| VPMOVZX of velem * wsize * velem * wsize
| VPAND of wsize
| VPANDN of wsize
| VPOR of wsize
| VPXOR of wsize
| VPADD of velem * wsize
| VPSUB of velem * wsize
| VPAVG of velem * wsize
| VPMULL of velem * wsize
| VPMULH of wsize
| VPMULHU of wsize
| VPMULHRS of wsize
| VPMUL of wsize
| VPMULU of wsize
| VPEXTR of wsize
| VPINSR of velem
| VPSLL of velem * wsize
| VPSRL of velem * wsize
| VPSRA of velem * wsize
| VPSLLV of velem * wsize
| VPSRLV of velem * wsize
| VPSLLDQ of wsize
| VPSRLDQ of wsize
| VPSHUFB of wsize
| VPSHUFD of wsize
| VPSHUFHW of wsize
| VPSHUFLW of wsize
| VPBLEND of velem * wsize
| VPBLENDVB of wsize
| VPACKUS of velem * wsize
| VPACKSS of velem * wsize
| VSHUFPS of wsize
| VPBROADCAST of velem * wsize
| VMOVSHDUP of wsize
| VMOVSLDUP of wsize
| VPALIGNR of wsize
| VBROADCASTI128
| VPUNPCKH of velem * wsize
| VPUNPCKL of velem * wsize
| VEXTRACTI128
| VINSERTI128
| VPERM2I128
| VPERMD
| VPERMQ
| VPMOVMSKB of wsize * wsize
| VPCMPEQ of velem * wsize
| VPCMPGT of velem * wsize
| VPMADDUBSW of wsize
| VPMADDWD of wsize
| VMOVLPD
| VMOVHPD
| VPMINU of velem * wsize
| VPMINS of velem * wsize
| VPMAXU of velem * wsize
| VPMAXS of velem * wsize
| VPTEST of wsize
| CLFLUSH
| LFENCE
| MFENCE
| SFENCE
| RDTSC of wsize
| RDTSCP of wsize
| AESDEC
| VAESDEC
| AESDECLAST
| VAESDECLAST
| AESENC
| VAESENC
| AESENCLAST
| VAESENCLAST
| AESIMC
| VAESIMC
| AESKEYGENASSIST
| VAESKEYGENASSIST
| PCLMULQDQ
| VPCLMULQDQ of wsize

(** val x86_op_beq : x86_op -> x86_op -> bool **)

let x86_op_beq x y =
  match x with
  | MOV x0 -> (match y with
               | MOV x1 -> wsize_beq x0 x1
               | _ -> false)
  | MOVSX (x0, x1) ->
    (match y with
     | MOVSX (x2, x3) -> (&&) (wsize_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | MOVZX (x0, x1) ->
    (match y with
     | MOVZX (x2, x3) -> (&&) (wsize_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | CMOVcc x0 -> (match y with
                  | CMOVcc x1 -> wsize_beq x0 x1
                  | _ -> false)
  | XCHG x0 -> (match y with
                | XCHG x1 -> wsize_beq x0 x1
                | _ -> false)
  | ADD x0 -> (match y with
               | ADD x1 -> wsize_beq x0 x1
               | _ -> false)
  | SUB x0 -> (match y with
               | SUB x1 -> wsize_beq x0 x1
               | _ -> false)
  | MUL x0 -> (match y with
               | MUL x1 -> wsize_beq x0 x1
               | _ -> false)
  | IMUL x0 -> (match y with
                | IMUL x1 -> wsize_beq x0 x1
                | _ -> false)
  | IMULr x0 -> (match y with
                 | IMULr x1 -> wsize_beq x0 x1
                 | _ -> false)
  | IMULri x0 -> (match y with
                  | IMULri x1 -> wsize_beq x0 x1
                  | _ -> false)
  | DIV x0 -> (match y with
               | DIV x1 -> wsize_beq x0 x1
               | _ -> false)
  | IDIV x0 -> (match y with
                | IDIV x1 -> wsize_beq x0 x1
                | _ -> false)
  | CQO x0 -> (match y with
               | CQO x1 -> wsize_beq x0 x1
               | _ -> false)
  | ADC x0 -> (match y with
               | ADC x1 -> wsize_beq x0 x1
               | _ -> false)
  | SBB x0 -> (match y with
               | SBB x1 -> wsize_beq x0 x1
               | _ -> false)
  | NEG x0 -> (match y with
               | NEG x1 -> wsize_beq x0 x1
               | _ -> false)
  | INC x0 -> (match y with
               | INC x1 -> wsize_beq x0 x1
               | _ -> false)
  | DEC x0 -> (match y with
               | DEC x1 -> wsize_beq x0 x1
               | _ -> false)
  | LZCNT x0 -> (match y with
                 | LZCNT x1 -> wsize_beq x0 x1
                 | _ -> false)
  | SETcc -> (match y with
              | SETcc -> true
              | _ -> false)
  | BT x0 -> (match y with
              | BT x1 -> wsize_beq x0 x1
              | _ -> false)
  | CLC -> (match y with
            | CLC -> true
            | _ -> false)
  | STC -> (match y with
            | STC -> true
            | _ -> false)
  | LEA x0 -> (match y with
               | LEA x1 -> wsize_beq x0 x1
               | _ -> false)
  | TEST x0 -> (match y with
                | TEST x1 -> wsize_beq x0 x1
                | _ -> false)
  | CMP x0 -> (match y with
               | CMP x1 -> wsize_beq x0 x1
               | _ -> false)
  | AND x0 -> (match y with
               | AND x1 -> wsize_beq x0 x1
               | _ -> false)
  | ANDN x0 -> (match y with
                | ANDN x1 -> wsize_beq x0 x1
                | _ -> false)
  | OR x0 -> (match y with
              | OR x1 -> wsize_beq x0 x1
              | _ -> false)
  | XOR x0 -> (match y with
               | XOR x1 -> wsize_beq x0 x1
               | _ -> false)
  | NOT x0 -> (match y with
               | NOT x1 -> wsize_beq x0 x1
               | _ -> false)
  | ROR x0 -> (match y with
               | ROR x1 -> wsize_beq x0 x1
               | _ -> false)
  | ROL x0 -> (match y with
               | ROL x1 -> wsize_beq x0 x1
               | _ -> false)
  | RCR x0 -> (match y with
               | RCR x1 -> wsize_beq x0 x1
               | _ -> false)
  | RCL x0 -> (match y with
               | RCL x1 -> wsize_beq x0 x1
               | _ -> false)
  | SHL x0 -> (match y with
               | SHL x1 -> wsize_beq x0 x1
               | _ -> false)
  | SHR x0 -> (match y with
               | SHR x1 -> wsize_beq x0 x1
               | _ -> false)
  | SAL x0 -> (match y with
               | SAL x1 -> wsize_beq x0 x1
               | _ -> false)
  | SAR x0 -> (match y with
               | SAR x1 -> wsize_beq x0 x1
               | _ -> false)
  | SHLD x0 -> (match y with
                | SHLD x1 -> wsize_beq x0 x1
                | _ -> false)
  | SHRD x0 -> (match y with
                | SHRD x1 -> wsize_beq x0 x1
                | _ -> false)
  | MULX_lo_hi x0 ->
    (match y with
     | MULX_lo_hi x1 -> wsize_beq x0 x1
     | _ -> false)
  | ADCX x0 -> (match y with
                | ADCX x1 -> wsize_beq x0 x1
                | _ -> false)
  | ADOX x0 -> (match y with
                | ADOX x1 -> wsize_beq x0 x1
                | _ -> false)
  | BSWAP x0 -> (match y with
                 | BSWAP x1 -> wsize_beq x0 x1
                 | _ -> false)
  | POPCNT x0 -> (match y with
                  | POPCNT x1 -> wsize_beq x0 x1
                  | _ -> false)
  | PEXT x0 -> (match y with
                | PEXT x1 -> wsize_beq x0 x1
                | _ -> false)
  | PDEP x0 -> (match y with
                | PDEP x1 -> wsize_beq x0 x1
                | _ -> false)
  | MOVX x0 -> (match y with
                | MOVX x1 -> wsize_beq x0 x1
                | _ -> false)
  | MOVD x0 -> (match y with
                | MOVD x1 -> wsize_beq x0 x1
                | _ -> false)
  | MOVV x0 -> (match y with
                | MOVV x1 -> wsize_beq x0 x1
                | _ -> false)
  | VMOV x0 -> (match y with
                | VMOV x1 -> wsize_beq x0 x1
                | _ -> false)
  | VMOVDQA x0 -> (match y with
                   | VMOVDQA x1 -> wsize_beq x0 x1
                   | _ -> false)
  | VMOVDQU h -> (match y with
                  | VMOVDQU h0 -> wsize_beq h h0
                  | _ -> false)
  | VPMOVSX (x0, x1, x2, x3) ->
    (match y with
     | VPMOVSX (x4, x5, x6, x7) ->
       (&&) (internal_velem_beq x0 x4)
         ((&&) (wsize_beq x1 x5)
           ((&&) (internal_velem_beq x2 x6) (wsize_beq x3 x7)))
     | _ -> false)
  | VPMOVZX (x0, x1, x2, x3) ->
    (match y with
     | VPMOVZX (x4, x5, x6, x7) ->
       (&&) (internal_velem_beq x0 x4)
         ((&&) (wsize_beq x1 x5)
           ((&&) (internal_velem_beq x2 x6) (wsize_beq x3 x7)))
     | _ -> false)
  | VPAND h -> (match y with
                | VPAND h0 -> wsize_beq h h0
                | _ -> false)
  | VPANDN h -> (match y with
                 | VPANDN h0 -> wsize_beq h h0
                 | _ -> false)
  | VPOR h -> (match y with
               | VPOR h0 -> wsize_beq h h0
               | _ -> false)
  | VPXOR h -> (match y with
                | VPXOR h0 -> wsize_beq h h0
                | _ -> false)
  | VPADD (h, h0) ->
    (match y with
     | VPADD (h1, h2) -> (&&) (internal_velem_beq h h1) (wsize_beq h0 h2)
     | _ -> false)
  | VPSUB (h, h0) ->
    (match y with
     | VPSUB (h1, h2) -> (&&) (internal_velem_beq h h1) (wsize_beq h0 h2)
     | _ -> false)
  | VPAVG (x0, x1) ->
    (match y with
     | VPAVG (x2, x3) -> (&&) (internal_velem_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | VPMULL (h, h0) ->
    (match y with
     | VPMULL (h1, h2) -> (&&) (internal_velem_beq h h1) (wsize_beq h0 h2)
     | _ -> false)
  | VPMULH x0 -> (match y with
                  | VPMULH x1 -> wsize_beq x0 x1
                  | _ -> false)
  | VPMULHU x0 -> (match y with
                   | VPMULHU x1 -> wsize_beq x0 x1
                   | _ -> false)
  | VPMULHRS x0 -> (match y with
                    | VPMULHRS x1 -> wsize_beq x0 x1
                    | _ -> false)
  | VPMUL h -> (match y with
                | VPMUL h0 -> wsize_beq h h0
                | _ -> false)
  | VPMULU h -> (match y with
                 | VPMULU h0 -> wsize_beq h h0
                 | _ -> false)
  | VPEXTR x0 -> (match y with
                  | VPEXTR x1 -> wsize_beq x0 x1
                  | _ -> false)
  | VPINSR x0 ->
    (match y with
     | VPINSR x1 -> internal_velem_beq x0 x1
     | _ -> false)
  | VPSLL (h, h0) ->
    (match y with
     | VPSLL (h1, h2) -> (&&) (internal_velem_beq h h1) (wsize_beq h0 h2)
     | _ -> false)
  | VPSRL (h, h0) ->
    (match y with
     | VPSRL (h1, h2) -> (&&) (internal_velem_beq h h1) (wsize_beq h0 h2)
     | _ -> false)
  | VPSRA (h, h0) ->
    (match y with
     | VPSRA (h1, h2) -> (&&) (internal_velem_beq h h1) (wsize_beq h0 h2)
     | _ -> false)
  | VPSLLV (h, h0) ->
    (match y with
     | VPSLLV (h1, h2) -> (&&) (internal_velem_beq h h1) (wsize_beq h0 h2)
     | _ -> false)
  | VPSRLV (h, h0) ->
    (match y with
     | VPSRLV (h1, h2) -> (&&) (internal_velem_beq h h1) (wsize_beq h0 h2)
     | _ -> false)
  | VPSLLDQ h -> (match y with
                  | VPSLLDQ h0 -> wsize_beq h h0
                  | _ -> false)
  | VPSRLDQ h -> (match y with
                  | VPSRLDQ h0 -> wsize_beq h h0
                  | _ -> false)
  | VPSHUFB h -> (match y with
                  | VPSHUFB h0 -> wsize_beq h h0
                  | _ -> false)
  | VPSHUFD h -> (match y with
                  | VPSHUFD h0 -> wsize_beq h h0
                  | _ -> false)
  | VPSHUFHW h -> (match y with
                   | VPSHUFHW h0 -> wsize_beq h h0
                   | _ -> false)
  | VPSHUFLW h -> (match y with
                   | VPSHUFLW h0 -> wsize_beq h h0
                   | _ -> false)
  | VPBLEND (h, h0) ->
    (match y with
     | VPBLEND (h1, h2) -> (&&) (internal_velem_beq h h1) (wsize_beq h0 h2)
     | _ -> false)
  | VPBLENDVB h -> (match y with
                    | VPBLENDVB h0 -> wsize_beq h h0
                    | _ -> false)
  | VPACKUS (h, h0) ->
    (match y with
     | VPACKUS (h1, h2) -> (&&) (internal_velem_beq h h1) (wsize_beq h0 h2)
     | _ -> false)
  | VPACKSS (h, h0) ->
    (match y with
     | VPACKSS (h1, h2) -> (&&) (internal_velem_beq h h1) (wsize_beq h0 h2)
     | _ -> false)
  | VSHUFPS h -> (match y with
                  | VSHUFPS h0 -> wsize_beq h h0
                  | _ -> false)
  | VPBROADCAST (x0, x1) ->
    (match y with
     | VPBROADCAST (x2, x3) ->
       (&&) (internal_velem_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | VMOVSHDUP x0 ->
    (match y with
     | VMOVSHDUP x1 -> wsize_beq x0 x1
     | _ -> false)
  | VMOVSLDUP x0 ->
    (match y with
     | VMOVSLDUP x1 -> wsize_beq x0 x1
     | _ -> false)
  | VPALIGNR h -> (match y with
                   | VPALIGNR h0 -> wsize_beq h h0
                   | _ -> false)
  | VBROADCASTI128 -> (match y with
                       | VBROADCASTI128 -> true
                       | _ -> false)
  | VPUNPCKH (h, h0) ->
    (match y with
     | VPUNPCKH (h1, h2) -> (&&) (internal_velem_beq h h1) (wsize_beq h0 h2)
     | _ -> false)
  | VPUNPCKL (h, h0) ->
    (match y with
     | VPUNPCKL (h1, h2) -> (&&) (internal_velem_beq h h1) (wsize_beq h0 h2)
     | _ -> false)
  | VEXTRACTI128 -> (match y with
                     | VEXTRACTI128 -> true
                     | _ -> false)
  | VINSERTI128 -> (match y with
                    | VINSERTI128 -> true
                    | _ -> false)
  | VPERM2I128 -> (match y with
                   | VPERM2I128 -> true
                   | _ -> false)
  | VPERMD -> (match y with
               | VPERMD -> true
               | _ -> false)
  | VPERMQ -> (match y with
               | VPERMQ -> true
               | _ -> false)
  | VPMOVMSKB (x0, x1) ->
    (match y with
     | VPMOVMSKB (x2, x3) -> (&&) (wsize_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | VPCMPEQ (x0, x1) ->
    (match y with
     | VPCMPEQ (x2, x3) -> (&&) (internal_velem_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | VPCMPGT (x0, x1) ->
    (match y with
     | VPCMPGT (x2, x3) -> (&&) (internal_velem_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | VPMADDUBSW x0 ->
    (match y with
     | VPMADDUBSW x1 -> wsize_beq x0 x1
     | _ -> false)
  | VPMADDWD x0 -> (match y with
                    | VPMADDWD x1 -> wsize_beq x0 x1
                    | _ -> false)
  | VMOVLPD -> (match y with
                | VMOVLPD -> true
                | _ -> false)
  | VMOVHPD -> (match y with
                | VMOVHPD -> true
                | _ -> false)
  | VPMINU (x0, x1) ->
    (match y with
     | VPMINU (x2, x3) -> (&&) (internal_velem_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | VPMINS (x0, x1) ->
    (match y with
     | VPMINS (x2, x3) -> (&&) (internal_velem_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | VPMAXU (x0, x1) ->
    (match y with
     | VPMAXU (x2, x3) -> (&&) (internal_velem_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | VPMAXS (x0, x1) ->
    (match y with
     | VPMAXS (x2, x3) -> (&&) (internal_velem_beq x0 x2) (wsize_beq x1 x3)
     | _ -> false)
  | VPTEST h -> (match y with
                 | VPTEST h0 -> wsize_beq h h0
                 | _ -> false)
  | CLFLUSH -> (match y with
                | CLFLUSH -> true
                | _ -> false)
  | LFENCE -> (match y with
               | LFENCE -> true
               | _ -> false)
  | MFENCE -> (match y with
               | MFENCE -> true
               | _ -> false)
  | SFENCE -> (match y with
               | SFENCE -> true
               | _ -> false)
  | RDTSC x0 -> (match y with
                 | RDTSC x1 -> wsize_beq x0 x1
                 | _ -> false)
  | RDTSCP x0 -> (match y with
                  | RDTSCP x1 -> wsize_beq x0 x1
                  | _ -> false)
  | AESDEC -> (match y with
               | AESDEC -> true
               | _ -> false)
  | VAESDEC -> (match y with
                | VAESDEC -> true
                | _ -> false)
  | AESDECLAST -> (match y with
                   | AESDECLAST -> true
                   | _ -> false)
  | VAESDECLAST -> (match y with
                    | VAESDECLAST -> true
                    | _ -> false)
  | AESENC -> (match y with
               | AESENC -> true
               | _ -> false)
  | VAESENC -> (match y with
                | VAESENC -> true
                | _ -> false)
  | AESENCLAST -> (match y with
                   | AESENCLAST -> true
                   | _ -> false)
  | VAESENCLAST -> (match y with
                    | VAESENCLAST -> true
                    | _ -> false)
  | AESIMC -> (match y with
               | AESIMC -> true
               | _ -> false)
  | VAESIMC -> (match y with
                | VAESIMC -> true
                | _ -> false)
  | AESKEYGENASSIST -> (match y with
                        | AESKEYGENASSIST -> true
                        | _ -> false)
  | VAESKEYGENASSIST -> (match y with
                         | VAESKEYGENASSIST -> true
                         | _ -> false)
  | PCLMULQDQ -> (match y with
                  | PCLMULQDQ -> true
                  | _ -> false)
  | VPCLMULQDQ x0 ->
    (match y with
     | VPCLMULQDQ x1 -> wsize_beq x0 x1
     | _ -> false)

(** val x86_op_eq_dec : x86_op -> x86_op -> bool **)

let x86_op_eq_dec x y =
  let b = x86_op_beq x y in if b then true else false

(** val x86_op_eq_axiom : x86_op Equality.axiom **)

let x86_op_eq_axiom =
  eq_axiom_of_scheme x86_op_beq

(** val x86_op_eqMixin : x86_op Equality.mixin_of **)

let x86_op_eqMixin =
  { Equality.op = x86_op_beq; Equality.mixin_of__1 = x86_op_eq_axiom }

(** val x86_op_eqType : Equality.coq_type **)

let x86_op_eqType =
  Obj.magic x86_op_eqMixin

(** val b_ty : stype list **)

let b_ty =
  Coq_sbool :: []

(** val b4_ty : stype list **)

let b4_ty =
  Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: [])))

(** val b5_ty : stype list **)

let b5_ty =
  Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: []))))

(** val bw_ty : wsize -> stype list **)

let bw_ty sz =
  Coq_sbool :: ((Coq_sword sz) :: [])

(** val bw2_ty : wsize -> stype list **)

let bw2_ty sz =
  Coq_sbool :: ((Coq_sword sz) :: ((Coq_sword sz) :: []))

(** val b2w_ty : wsize -> stype list **)

let b2w_ty sz =
  Coq_sbool :: (Coq_sbool :: ((Coq_sword sz) :: []))

(** val b4w_ty : wsize -> stype list **)

let b4w_ty sz =
  Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: ((Coq_sword
    sz) :: []))))

(** val b5w_ty : wsize -> stype list **)

let b5w_ty sz =
  Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: ((Coq_sword
    sz) :: [])))))

(** val b5w2_ty : wsize -> stype list **)

let b5w2_ty sz =
  Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: (Coq_sbool :: ((Coq_sword
    sz) :: ((Coq_sword sz) :: []))))))

(** val w_ty : wsize -> stype list **)

let w_ty sz =
  (Coq_sword sz) :: []

(** val w2_ty : wsize -> wsize -> stype list **)

let w2_ty sz sz' =
  (Coq_sword sz) :: ((Coq_sword sz') :: [])

(** val w3_ty : wsize -> stype list **)

let w3_ty sz =
  (Coq_sword sz) :: ((Coq_sword sz) :: ((Coq_sword sz) :: []))

(** val w8_ty : stype list **)

let w8_ty =
  (Coq_sword U8) :: []

(** val w128_ty : stype list **)

let w128_ty =
  (Coq_sword U128) :: []

(** val w256_ty : stype list **)

let w256_ty =
  (Coq_sword U256) :: []

(** val w2b_ty : wsize -> wsize -> stype list **)

let w2b_ty sz sz' =
  (Coq_sword sz) :: ((Coq_sword sz') :: (Coq_sbool :: []))

(** val ww8_ty : wsize -> stype list **)

let ww8_ty sz =
  (Coq_sword sz) :: ((Coq_sword U8) :: [])

(** val ww8b_ty : wsize -> stype list **)

let ww8b_ty sz =
  (Coq_sword sz) :: ((Coq_sword U8) :: (Coq_sbool :: []))

(** val w2w8_ty : wsize -> stype list **)

let w2w8_ty sz =
  (Coq_sword sz) :: ((Coq_sword sz) :: ((Coq_sword U8) :: []))

(** val w128w8_ty : stype list **)

let w128w8_ty =
  (Coq_sword U128) :: ((Coq_sword U8) :: [])

(** val w128ww8_ty : wsize -> stype list **)

let w128ww8_ty sz =
  (Coq_sword U128) :: ((Coq_sword sz) :: ((Coq_sword U8) :: []))

(** val w256w8_ty : stype list **)

let w256w8_ty =
  (Coq_sword U256) :: ((Coq_sword U8) :: [])

(** val w256w128w8_ty : stype list **)

let w256w128w8_ty =
  (Coq_sword U256) :: ((Coq_sword U128) :: ((Coq_sword U8) :: []))

(** val w256x2w8_ty : stype list **)

let w256x2w8_ty =
  (Coq_sword U256) :: ((Coq_sword U256) :: ((Coq_sword U8) :: []))

(** val coq_SF_of_word : wsize -> GRing.ComRing.sort -> bool **)

let coq_SF_of_word =
  msb

(** val coq_PF_of_word : wsize -> GRing.ComRing.sort -> bool **)

let coq_PF_of_word sz w =
  foldl xorb true
    (map (fun i0 -> wbit_n sz w i0)
      (iota O (S (S (S (S (S (S (S (S O))))))))))

(** val coq_ZF_of_word : wsize -> GRing.ComRing.sort -> bool **)

let coq_ZF_of_word sz w =
  eq_op (GRing.ComRing.eqType (word sz)) w
    (GRing.zero (GRing.ComRing.zmodType (word sz)))

(** val rflags_of_bwop : wsize -> GRing.ComRing.sort -> sem_tuple **)

let rflags_of_bwop sz w =
  Obj.magic ((Some false), ((Some false), ((Some (coq_SF_of_word sz w)),
    ((Some (coq_PF_of_word sz w)), (Some (coq_ZF_of_word sz w))))))

(** val rflags_of_aluop :
    wsize -> GRing.ComRing.sort -> coq_Z -> coq_Z -> sem_tuple **)

let rflags_of_aluop sz w vu vs =
  Obj.magic ((Some
    (negb (eq_op coq_Z_eqType (Obj.magic wsigned sz w) (Obj.magic vs)))),
    ((Some
    (negb (eq_op coq_Z_eqType (Obj.magic wunsigned sz w) (Obj.magic vu)))),
    ((Some (coq_SF_of_word sz w)), ((Some (coq_PF_of_word sz w)), (Some
    (coq_ZF_of_word sz w))))))

(** val rflags_of_mul : bool -> sem_tuple **)

let rflags_of_mul ov =
  Obj.magic ((Some ov), ((Some ov), (None, (None, None))))

(** val rflags_of_div : sem_tuple **)

let rflags_of_div =
  Obj.magic (None, (None, (None, (None, None))))

(** val rflags_of_andn : wsize -> GRing.ComRing.sort -> sem_tuple **)

let rflags_of_andn sz w =
  Obj.magic ((Some false), ((Some false), ((Some (coq_SF_of_word sz w)),
    (None, (Some (coq_ZF_of_word sz w))))))

(** val rflags_None_w : wsize -> sem_ot -> sem_tuple **)

let rflags_None_w _ w =
  Obj.magic (None, (None, (None, (None, (None, w)))))

(** val rflags_of_aluop_nocf :
    wsize -> GRing.ComRing.sort -> coq_Z -> sem_tuple **)

let rflags_of_aluop_nocf sz w vs =
  Obj.magic ((Some
    (negb (eq_op coq_Z_eqType (Obj.magic wsigned sz w) (Obj.magic vs)))),
    ((Some (coq_SF_of_word sz w)), ((Some (coq_PF_of_word sz w)), (Some
    (coq_ZF_of_word sz w)))))

(** val flags_w :
    __ list -> ltuple -> wsize -> GRing.ComRing.sort -> ltuple **)

let flags_w l1 bs sz w =
  merge_tuple l1 (map (Obj.magic __) (w_ty sz)) bs w

(** val flags_w2 : __ list -> ltuple -> wsize -> sem_tuple -> ltuple **)

let flags_w2 l1 bs sz w =
  merge_tuple l1 (map (Obj.magic __) (w2_ty sz sz)) bs w

(** val rflags_of_aluop_w :
    wsize -> GRing.ComRing.sort -> coq_Z -> coq_Z -> ltuple **)

let rflags_of_aluop_w sz w vu vs =
  flags_w (map (Obj.magic __) b5_ty) (rflags_of_aluop sz w vu vs) sz w

(** val rflags_of_aluop_nocf_w :
    wsize -> GRing.ComRing.sort -> coq_Z -> ltuple **)

let rflags_of_aluop_nocf_w sz w vs =
  flags_w (map (Obj.magic __) b4_ty) (rflags_of_aluop_nocf sz w vs) sz w

(** val rflags_of_bwop_w : wsize -> GRing.ComRing.sort -> ltuple **)

let rflags_of_bwop_w sz w =
  flags_w (map (Obj.magic __) b5_ty) (rflags_of_bwop sz w) sz w

(** val prim_8_64 : (wsize -> 'a1) -> 'a1 prim_constructor **)

let prim_8_64 f =
  let range = U64 :: (U32 :: (U16 :: (U8 :: []))) in
  PrimX86 ((map (fun x -> PVp x) range), (fun s ->
  match s with
  | PVp sz -> Some (f sz)
  | PVv (_, _) -> None
  | PVsv (_, _, _) -> None
  | PVx (_, _) -> None
  | PVvv (_, _, _, _) -> None))

(** val prim_16_64 : (wsize -> 'a1) -> 'a1 prim_constructor **)

let prim_16_64 f =
  let range = U64 :: (U32 :: (U16 :: [])) in
  PrimX86 ((map (fun x -> PVp x) range), (fun s ->
  match s with
  | PVp sz -> Some (f sz)
  | PVv (_, _) -> None
  | PVsv (_, _, _) -> None
  | PVx (_, _) -> None
  | PVvv (_, _, _, _) -> None))

(** val prim_32_64 : (wsize -> 'a1) -> 'a1 prim_constructor **)

let prim_32_64 f =
  let range = U64 :: (U32 :: []) in
  PrimX86 ((map (fun x -> PVp x) range), (fun s ->
  match s with
  | PVp sz -> Some (f sz)
  | PVv (_, _) -> None
  | PVsv (_, _, _) -> None
  | PVx (_, _) -> None
  | PVvv (_, _, _, _) -> None))

(** val prim_128_256 : (wsize -> 'a1) -> 'a1 prim_constructor **)

let prim_128_256 f =
  let range = U128 :: (U256 :: []) in
  PrimX86 ((map (fun x -> PVp x) range), (fun s ->
  match s with
  | PVp sz -> Some (f sz)
  | PVv (_, _) -> None
  | PVsv (_, _, _) -> None
  | PVx (_, _) -> None
  | PVvv (_, _, _, _) -> None))

(** val prim_movsx : (wsize -> wsize -> x86_op) -> x86_op prim_constructor **)

let prim_movsx =
  let range = (PVx (U16, U8)) :: ((PVx (U32, U8)) :: ((PVx (U64,
    U8)) :: ((PVx (U16, U16)) :: ((PVx (U32, U16)) :: ((PVx (U64,
    U16)) :: ((PVx (U32, U32)) :: ((PVx (U64, U32)) :: [])))))))
  in
  (fun f -> PrimX86 (range, (fun s ->
  match s with
  | PVp _ -> None
  | PVv (_, _) -> None
  | PVsv (_, _, _) -> None
  | PVx (szo, szi) -> Some (f szo szi)
  | PVvv (_, _, _, _) -> None)))

(** val prim_movzx : (wsize -> wsize -> x86_op) -> x86_op prim_constructor **)

let prim_movzx =
  let range = (PVx (U16, U8)) :: ((PVx (U32, U8)) :: ((PVx (U64,
    U8)) :: ((PVx (U32, U16)) :: ((PVx (U64, U16)) :: []))))
  in
  (fun f -> PrimX86 (range, (fun s ->
  match s with
  | PVp _ -> None
  | PVv (_, _) -> None
  | PVsv (_, _, _) -> None
  | PVx (szo, szi) -> Some (f szo szi)
  | PVvv (_, _, _, _) -> None)))

(** val prim_vv :
    (velem -> wsize -> velem -> wsize -> x86_op) -> x86_op prim_constructor **)

let prim_vv f =
  PrimX86 (((PVvv (VE8, U64, VE16, U128)) :: ((PVvv (VE8, U32, VE32,
    U128)) :: ((PVvv (VE8, U16, VE64, U128)) :: ((PVvv (VE16, U64, VE32,
    U128)) :: ((PVvv (VE16, U32, VE64, U128)) :: ((PVvv (VE32, U64, VE64,
    U128)) :: ((PVvv (VE8, U128, VE16, U256)) :: ((PVvv (VE8, U64, VE32,
    U256)) :: ((PVvv (VE8, U32, VE64, U256)) :: ((PVvv (VE16, U128, VE32,
    U256)) :: ((PVvv (VE16, U64, VE64, U256)) :: ((PVvv (VE32, U128, VE64,
    U256)) :: [])))))))))))), (fun s ->
    match s with
    | PVvv (ve, sz, ve', sz') -> Some (f ve sz ve' sz')
    | _ -> None))

(** val primV_range :
    prim_x86_suffix list -> (velem -> wsize -> x86_op) -> x86_op
    prim_constructor **)

let primV_range range f =
  PrimX86 (range, (fun s ->
    match s with
    | PVv (ve, sz) -> Some (f ve sz)
    | _ -> None))

(** val primV : (velem -> wsize -> x86_op) -> x86_op prim_constructor **)

let primV =
  primV_range
    (flatten
      (map (fun ve -> map (fun sz -> PVv (ve, sz)) (U128 :: (U256 :: [])))
        (VE8 :: (VE16 :: (VE32 :: (VE64 :: []))))))

(** val primV_8_16 : (velem -> wsize -> x86_op) -> x86_op prim_constructor **)

let primV_8_16 =
  primV_range
    (flatten
      (map (fun ve -> map (fun sz -> PVv (ve, sz)) (U128 :: (U256 :: [])))
        (VE8 :: (VE16 :: []))))

(** val primV_8_32 : (velem -> wsize -> x86_op) -> x86_op prim_constructor **)

let primV_8_32 =
  primV_range
    (flatten
      (map (fun ve -> map (fun sz -> PVv (ve, sz)) (U128 :: (U256 :: [])))
        (VE8 :: (VE16 :: (VE32 :: [])))))

(** val primV_16 : (velem -> wsize -> x86_op) -> x86_op prim_constructor **)

let primV_16 =
  primV_range (map (fun sz -> PVv (VE16, sz)) (U128 :: (U256 :: [])))

(** val primV_16_32 :
    (velem -> wsize -> x86_op) -> x86_op prim_constructor **)

let primV_16_32 =
  primV_range
    (flatten
      (map (fun ve -> map (fun sz -> PVv (ve, sz)) (U128 :: (U256 :: [])))
        (VE16 :: (VE32 :: []))))

(** val primV_16_64 :
    (velem -> wsize -> x86_op) -> x86_op prim_constructor **)

let primV_16_64 =
  primV_range
    (flatten
      (map (fun ve -> map (fun sz -> PVv (ve, sz)) (U128 :: (U256 :: [])))
        (VE16 :: (VE32 :: (VE64 :: [])))))

(** val primV_128 : (velem -> wsize -> x86_op) -> x86_op prim_constructor **)

let primV_128 =
  primV_range
    (map (fun ve -> PVv (ve, U128)) (VE8 :: (VE16 :: (VE32 :: (VE64 :: [])))))

(** val primSV_8_32 :
    (signedness -> velem -> wsize -> x86_op) -> x86_op prim_constructor **)

let primSV_8_32 f =
  PrimX86
    ((flatten
       (map (fun pv -> map pv (U128 :: (U256 :: [])))
         (flatten
           (map (fun sg ->
             map (fun ve x -> PVsv (sg, ve, x))
               (VE8 :: (VE16 :: (VE32 :: [])))) (Signed :: (Unsigned :: [])))))),
    (fun s ->
    match s with
    | PVsv (sg, ve, sz) -> Some (f sg ve sz)
    | _ -> None))

(** val primX : (wsize -> wsize -> x86_op) -> x86_op prim_constructor **)

let primX f =
  PrimX86
    ((flatten
       (map (fun ssz -> map (fun dsz -> PVx (ssz, dsz)) (U64 :: (U32 :: [])))
         (U128 :: (U256 :: [])))), (fun s ->
    match s with
    | PVx (ssz, dsz) -> Some (f ssz dsz)
    | _ -> None))

(** val x86_MOV : wsize -> GRing.ComRing.sort -> GRing.ComRing.sort exec **)

let x86_MOV sz x =
  match check_size_8_64 sz with
  | Ok _ -> Ok x
  | Error s -> Error s

(** val x86_MOVSX : wsize -> wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_MOVSX szi szo x =
  match match szi with
        | U8 -> check_size_16_64 szo
        | U16 -> check_size_16_64 szo
        | U32 -> check_size_32_64 szo
        | _ -> type_error with
  | Ok _ -> Ok (sign_extend szo szi x)
  | Error s -> Error s

(** val x86_MOVZX : wsize -> wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_MOVZX szi szo x =
  match match szi with
        | U8 -> check_size_16_64 szo
        | U16 -> check_size_32_64 szo
        | _ -> type_error with
  | Ok _ -> Ok (zero_extend szo szi x)
  | Error s -> Error s

(** val x86_XCHG :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_XCHG sz v1 v2 =
  match check_size_8_64 sz with
  | Ok _ -> Ok (Obj.magic (v2, v1))
  | Error s -> Error s

(** val x86_ADD :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_ADD sz v1 v2 =
  match check_size_8_64 sz with
  | Ok _ ->
    Ok
      (rflags_of_aluop_w sz
        (GRing.add (GRing.ComRing.zmodType (word sz)) v1 v2)
        (Z.add (wunsigned sz v1) (wunsigned sz v2))
        (Z.add (wsigned sz v1) (wsigned sz v2)))
  | Error s -> Error s

(** val x86_SUB :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_SUB sz v1 v2 =
  match check_size_8_64 sz with
  | Ok _ ->
    Ok
      (rflags_of_aluop_w sz
        (GRing.add (GRing.ComRing.zmodType (word sz)) v1
          (GRing.opp (GRing.ComRing.zmodType (word sz)) v2))
        (Z.sub (wunsigned sz v1) (wunsigned sz v2))
        (Z.sub (wsigned sz v1) (wsigned sz v2)))
  | Error s -> Error s

(** val x86_CMOVcc :
    wsize -> bool -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_CMOVcc sz b w2 w3 =
  match check_size_16_64 sz with
  | Ok _ -> if b then Ok w2 else Ok w3
  | Error s -> Error s

(** val x86_MUL :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_MUL sz v1 v2 =
  match check_size_16_64 sz with
  | Ok _ ->
    let lo = GRing.mul (GRing.ComRing.ringType (word sz)) v1 v2 in
    let hi = wmulhu sz v1 v2 in
    let ov = wdwordu sz hi lo in
    let ov0 = Z.gtb ov (Z.sub (wbase sz) (Zpos Coq_xH)) in
    Ok
    (flags_w2 (map (Obj.magic __) b5_ty) (rflags_of_mul ov0) sz
      (Obj.magic (hi, lo)))
  | Error s -> Error s

(** val x86_IMUL_overflow :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool **)

let x86_IMUL_overflow sz hi lo =
  let ov = wdwords sz hi lo in
  (||) (Z.ltb ov (wmin_signed sz)) (Z.gtb ov (wmax_signed sz))

(** val x86_IMUL :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_IMUL sz v1 v2 =
  match check_size_16_64 sz with
  | Ok _ ->
    let lo = GRing.mul (GRing.ComRing.ringType (word sz)) v1 v2 in
    let hi = wmulhs sz v1 v2 in
    let ov = x86_IMUL_overflow sz hi lo in
    Ok
    (flags_w2 (map (Obj.magic __) b5_ty) (rflags_of_mul ov) sz
      (Obj.magic (hi, lo)))
  | Error s -> Error s

(** val x86_IMULt :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_IMULt sz v1 v2 =
  match check_size_16_64 sz with
  | Ok _ ->
    let lo = GRing.mul (GRing.ComRing.ringType (word sz)) v1 v2 in
    let hi = wmulhs sz v1 v2 in
    let ov = x86_IMUL_overflow sz hi lo in
    Ok (flags_w (map (Obj.magic __) b5_ty) (rflags_of_mul ov) sz lo)
  | Error s -> Error s

(** val x86_DIV :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> sem_tuple exec **)

let x86_DIV sz hi lo dv =
  match check_size_16_64 sz with
  | Ok _ ->
    let dd = wdwordu sz hi lo in
    let dv0 = wunsigned sz dv in
    let q = Z.div dd dv0 in
    let r0 = Z.modulo dd dv0 in
    let ov = Z.gtb q (wmax_unsigned sz) in
    if (||) (eq_op coq_Z_eqType (Obj.magic dv0) (Obj.magic Z0)) ov
    then Error ErrArith
    else Ok
           (flags_w2 (map (Obj.magic __) b5_ty) rflags_of_div sz
             (Obj.magic ((wrepr sz q), (wrepr sz r0))))
  | Error s -> Error s

(** val x86_IDIV :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> sem_tuple exec **)

let x86_IDIV sz hi lo dv =
  match check_size_16_64 sz with
  | Ok _ ->
    let dd = wdwords sz hi lo in
    let dv0 = wsigned sz dv in
    let q = Z.quot dd dv0 in
    let r0 = Z.rem dd dv0 in
    let ov = (||) (Z.ltb q (wmin_signed sz)) (Z.gtb q (wmax_signed sz)) in
    if (||) (eq_op coq_Z_eqType (Obj.magic dv0) (Obj.magic Z0)) ov
    then Error ErrArith
    else Ok
           (flags_w2 (map (Obj.magic __) b5_ty) rflags_of_div sz
             (Obj.magic ((wrepr sz q), (wrepr sz r0))))
  | Error s -> Error s

(** val x86_CQO : wsize -> GRing.ComRing.sort -> GRing.ComRing.sort exec **)

let x86_CQO sz w =
  match check_size_16_64 sz with
  | Ok _ ->
    let r0 =
      if msb sz w
      then GRing.opp (GRing.Ring.zmodType (GRing.ComRing.ringType (word sz)))
             (GRing.one (GRing.ComRing.ringType (word sz)))
      else GRing.zero (GRing.Ring.zmodType (GRing.ComRing.ringType (word sz)))
    in
    Ok r0
  | Error s -> Error s

(** val add_carry : wsize -> coq_Z -> coq_Z -> coq_Z -> GRing.ComRing.sort **)

let add_carry sz x y c0 =
  wrepr sz (Z.add (Z.add x y) c0)

(** val x86_ADC :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool -> sem_tuple
    exec **)

let x86_ADC sz v1 v2 c0 =
  match check_size_8_64 sz with
  | Ok _ ->
    let c1 = Z.b2z c0 in
    Ok
    (rflags_of_aluop_w sz
      (add_carry sz (wunsigned sz v1) (wunsigned sz v2) c1)
      (Z.add (Z.add (wunsigned sz v1) (wunsigned sz v2)) c1)
      (Z.add (Z.add (wsigned sz v1) (wsigned sz v2)) c1))
  | Error s -> Error s

(** val x86_ADCX :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool -> sem_tuple
    exec **)

let x86_ADCX sz v1 v2 c0 =
  match check_size_32_64 sz with
  | Ok _ ->
    let (c1, w) = waddcarry sz v1 v2 c0 in Ok (Obj.magic ((Some c1), w))
  | Error s -> Error s

(** val x86_MULX_lo_hi :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_MULX_lo_hi sz v1 v2 =
  match check_size_32_64 sz with
  | Ok _ -> let (hi, lo) = wumul sz v1 v2 in Ok (Obj.magic (lo, hi))
  | Error s -> Error s

(** val sub_borrow :
    wsize -> coq_Z -> coq_Z -> coq_Z -> GRing.ComRing.sort **)

let sub_borrow sz x y c0 =
  wrepr sz (Z.sub (Z.sub x y) c0)

(** val x86_SBB :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool -> sem_tuple
    exec **)

let x86_SBB sz v1 v2 c0 =
  match check_size_8_64 sz with
  | Ok _ ->
    let c1 = Z.b2z c0 in
    Ok
    (rflags_of_aluop_w sz
      (sub_borrow sz (wunsigned sz v1) (wunsigned sz v2) c1)
      (Z.sub (wunsigned sz v1) (Z.add (wunsigned sz v2) c1))
      (Z.sub (wsigned sz v1) (Z.add (wsigned sz v2) c1)))
  | Error s -> Error s

(** val x86_NEG : wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_NEG sz w =
  match check_size_8_64 sz with
  | Ok _ ->
    let vs = Z.opp (wsigned sz w) in
    let v = GRing.opp (GRing.ComRing.zmodType (word sz)) w in
    Ok
    (flags_w (map (Obj.magic __) b5_ty)
      (Obj.magic ((Some
        (negb (eq_op coq_Z_eqType (Obj.magic wsigned sz v) (Obj.magic vs)))),
        ((Some
        (negb
          (eq_op (GRing.ComRing.eqType (word sz)) w
            (GRing.zero (GRing.ComRing.zmodType (word sz)))))), ((Some
        (coq_SF_of_word sz v)), ((Some (coq_PF_of_word sz v)), (Some
        (coq_ZF_of_word sz v))))))) sz v)
  | Error s -> Error s

(** val x86_INC : wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_INC sz w =
  match check_size_8_64 sz with
  | Ok _ ->
    Ok
      (rflags_of_aluop_nocf_w sz
        (GRing.add (GRing.ComRing.zmodType (word sz)) w
          (GRing.one (GRing.ComRing.ringType (word sz))))
        (Z.add (wsigned sz w) (Zpos Coq_xH)))
  | Error s -> Error s

(** val x86_DEC : wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_DEC sz w =
  match check_size_8_64 sz with
  | Ok _ ->
    Ok
      (rflags_of_aluop_nocf_w sz
        (GRing.add (GRing.ComRing.zmodType (word sz)) w
          (GRing.opp (GRing.Ring.zmodType (GRing.ComRing.ringType (word sz)))
            (GRing.one (GRing.ComRing.ringType (word sz)))))
        (Z.sub (wsigned sz w) (Zpos Coq_xH)))
  | Error s -> Error s

(** val x86_LZCNT : wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_LZCNT sz w =
  match check_size_16_64 sz with
  | Ok _ ->
    let v = leading_zero sz w in
    Ok
    (flags_w (map (Obj.magic __) b5_ty)
      (Obj.magic (None, ((Some (coq_ZF_of_word sz w)), (None, (None, (Some
        (coq_ZF_of_word sz v))))))) sz v)
  | Error s -> Error s

(** val x86_SETcc : bool -> sem_tuple exec **)

let x86_SETcc b =
  Ok (wrepr U8 (Z.b2z b))

(** val x86_BT :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_BT sz x y =
  match check_size_16_64 sz with
  | Ok _ -> Ok (Obj.magic (Some (Word0.wbit sz x y)))
  | Error s -> Error s

(** val x86_CLC : sem_tuple exec **)

let x86_CLC =
  Ok (Obj.magic (Some false))

(** val x86_STC : sem_tuple exec **)

let x86_STC =
  Ok (Obj.magic (Some true))

(** val x86_LEA : wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_LEA sz addr =
  match check_size_16_64 sz with
  | Ok _ -> Ok addr
  | Error s -> Error s

(** val x86_TEST :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_TEST sz x y =
  match check_size_8_64 sz with
  | Ok _ -> Ok (rflags_of_bwop sz (Word0.wand sz x y))
  | Error s -> Error s

(** val x86_CMP :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_CMP sz x y =
  match check_size_8_64 sz with
  | Ok _ ->
    Ok
      (rflags_of_aluop sz
        (GRing.add (GRing.ComRing.zmodType (word sz)) x
          (GRing.opp (GRing.ComRing.zmodType (word sz)) y))
        (Z.sub (wunsigned sz x) (wunsigned sz y))
        (Z.sub (wsigned sz x) (wsigned sz y)))
  | Error s -> Error s

(** val x86_AND :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_AND sz v1 v2 =
  match check_size_8_64 sz with
  | Ok _ -> Ok (rflags_of_bwop_w sz (Word0.wand sz v1 v2))
  | Error s -> Error s

(** val x86_ANDN :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_ANDN sz v1 v2 =
  match check_size_32_64 sz with
  | Ok _ ->
    let w = wandn sz v1 v2 in
    Ok (flags_w (map (Obj.magic __) b5_ty) (rflags_of_andn sz w) sz w)
  | Error s -> Error s

(** val x86_OR :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_OR sz v1 v2 =
  match check_size_8_64 sz with
  | Ok _ -> Ok (rflags_of_bwop_w sz (Word0.wor sz v1 v2))
  | Error s -> Error s

(** val x86_XOR :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_XOR sz v1 v2 =
  match check_size_8_64 sz with
  | Ok _ -> Ok (rflags_of_bwop_w sz (Word0.wxor sz v1 v2))
  | Error s -> Error s

(** val x86_NOT : wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_NOT sz v =
  match check_size_8_64 sz with
  | Ok _ -> Ok (wnot sz v)
  | Error s -> Error s

(** val x86_shift_mask : wsize -> GRing.ComRing.sort **)

let x86_shift_mask = function
| U64 -> wrepr U8 (Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
| U128 ->
  wrepr U8 (Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))))
| U256 ->
  wrepr U8 (Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
    Coq_xH))))))))
| _ -> wrepr U8 (Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))

(** val x86_ROR :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_ROR sz v i0 =
  match check_size_8_64 sz with
  | Ok _ ->
    let i1 = Word0.wand U8 i0 (x86_shift_mask sz) in
    if eq_op (GRing.ComRing.eqType (word U8)) i1
         (GRing.zero (GRing.ComRing.zmodType (word U8)))
    then Ok (Obj.magic (None, (None, v)))
    else let r0 = wror sz v (wunsigned U8 i1) in
         let cF = msb sz r0 in
         let oF =
           if eq_op (GRing.ComRing.eqType (word U8)) i1
                (GRing.one (GRing.ComRing.ringType (word U8)))
           then Some
                  (negb
                    (eq_op bool_eqType (Obj.magic cF) (Obj.magic msb sz v)))
           else None
         in
         Ok (Obj.magic (oF, ((Some cF), r0)))
  | Error s -> Error s

(** val x86_ROL :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_ROL sz v i0 =
  match check_size_8_64 sz with
  | Ok _ ->
    let i1 = Word0.wand U8 i0 (x86_shift_mask sz) in
    if eq_op (GRing.ComRing.eqType (word U8)) i1
         (GRing.zero (GRing.ComRing.zmodType (word U8)))
    then Ok (Obj.magic (None, (None, v)))
    else let r0 = wrol sz v (wunsigned U8 i1) in
         let cF = lsb sz r0 in
         let oF =
           if eq_op (GRing.ComRing.eqType (word U8)) i1
                (GRing.one (GRing.ComRing.ringType (word U8)))
           then Some
                  (negb
                    (eq_op bool_eqType (Obj.magic msb sz r0) (Obj.magic cF)))
           else None
         in
         Ok (Obj.magic (oF, ((Some cF), r0)))
  | Error s -> Error s

(** val x86_rotate_with_carry :
    wsize -> (word -> nat -> word) -> (GRing.ComRing.sort -> bool -> bool) ->
    GRing.ComRing.sort -> GRing.ComRing.sort -> bool -> sem_tuple exec **)

let x86_rotate_with_carry sz rot ovf v i0 cf =
  match check_size_8_64 sz with
  | Ok _ ->
    let i1 = Word0.wand U8 i0 (x86_shift_mask sz) in
    let i2 =
      match sz with
      | U8 ->
        Z.modulo (wunsigned U8 i1) (Zpos (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | U16 ->
        Z.modulo (wunsigned U8 i1) (Zpos (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))
      | _ -> wunsigned U8 i1
    in
    let r0 =
      t2w (S (S (wsize_size_minus_1 sz)))
        (tuple (S (S (wsize_size_minus_1 sz)))
          (cons_tuple (S (wsize_size_minus_1 sz)) cf
            (w2t (S (wsize_size_minus_1 sz)) (Obj.magic v))) (fun _ ->
          cf :: (tval (S (wsize_size_minus_1 sz))
                  (w2t (S (wsize_size_minus_1 sz)) (Obj.magic v)))))
    in
    let r1 = rot r0 (Z.to_nat i2) in
    let r2 = w2t (S (nat_of_wsize sz)) r1 in
    let cF = head false (tval (S (nat_of_wsize sz)) r2) in
    let r3 =
      t2w (pred (S (nat_of_wsize sz)))
        (tuple (pred (S (nat_of_wsize sz)))
          (behead_tuple (S (nat_of_wsize sz)) r2) (fun _ ->
          behead (tval (S (nat_of_wsize sz)) r2)))
    in
    let oF =
      if eq_op coq_Z_eqType (Obj.magic i2) (GRing.one coq_Z_ringType)
      then Some (Obj.magic ovf r3 cF)
      else None
    in
    Ok (Obj.magic (oF, ((Some cF), r3)))
  | Error s -> Error s

(** val x86_RCL :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool -> sem_tuple
    exec **)

let x86_RCL sz v i0 cf =
  x86_rotate_with_carry sz (rotl (S (nat_of_wsize sz))) (fun r0 c0 ->
    negb (eq_op bool_eqType (Obj.magic msb sz r0) (Obj.magic c0))) v i0 cf

(** val x86_RCR :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool -> sem_tuple
    exec **)

let x86_RCR sz v i0 cf =
  x86_rotate_with_carry sz (rotr (S (nat_of_wsize sz))) (fun _ _ ->
    negb (eq_op bool_eqType (Obj.magic msb sz v) (Obj.magic cf))) v i0 cf

(** val rflags_OF :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool ->
    bool -> sem_tuple exec **)

let rflags_OF s sz i0 r0 rc oF =
  let oF0 =
    if eq_op (GRing.ComRing.eqType (word s)) i0
         (GRing.one (GRing.ComRing.ringType (word s)))
    then Some oF
    else None
  in
  let cF = Some rc in
  let sF = Some (coq_SF_of_word sz r0) in
  let pF = Some (coq_PF_of_word sz r0) in
  let zF = Some (coq_ZF_of_word sz r0) in
  Ok (Obj.magic (oF0, (cF, (sF, (pF, (zF, r0))))))

(** val x86_SHL :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_SHL sz v i0 =
  match check_size_8_64 sz with
  | Ok _ ->
    let i1 = Word0.wand U8 i0 (x86_shift_mask sz) in
    if eq_op (GRing.ComRing.eqType (word U8)) i1
         (GRing.zero (GRing.ComRing.zmodType (word U8)))
    then Ok (rflags_None_w sz v)
    else let rc = msb sz (wshl sz v (Z.sub (wunsigned U8 i1) (Zpos Coq_xH)))
         in
         let r0 = wshl sz v (wunsigned U8 i1) in
         rflags_OF U8 sz i1 r0 rc (addb (msb sz r0) rc)
  | Error s -> Error s

(** val x86_SHLD :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> sem_tuple exec **)

let x86_SHLD sz v1 v2 i0 =
  match check_size_16_64 sz with
  | Ok _ ->
    let i1 = Word0.wand U8 i0 (x86_shift_mask sz) in
    if eq_op (GRing.ComRing.eqType (word U8)) i1
         (GRing.zero (GRing.ComRing.zmodType (word U8)))
    then Ok (rflags_None_w sz v1)
    else let j = Z.sub (wsize_bits sz) (wunsigned U8 i1) in
         if Z.ltb j Z0
         then Error ErrArith
         else let rc =
                msb sz (wshl sz v1 (Z.sub (wunsigned U8 i1) (Zpos Coq_xH)))
              in
              let r1 = wshl sz v1 (wunsigned U8 i1) in
              let r2 = wshr sz v2 j in
              let r0 = Word0.wor sz r1 r2 in
              rflags_OF U8 sz i1 r0 rc (addb (msb sz r0) rc)
  | Error s -> Error s

(** val x86_SHR :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_SHR sz v i0 =
  match check_size_8_64 sz with
  | Ok _ ->
    let i1 = Word0.wand U8 i0 (x86_shift_mask sz) in
    if eq_op (GRing.ComRing.eqType (word U8)) i1
         (GRing.zero (GRing.ComRing.zmodType (word U8)))
    then Ok (rflags_None_w sz v)
    else let rc = lsb sz (wshr sz v (Z.sub (wunsigned U8 i1) (Zpos Coq_xH)))
         in
         let r0 = wshr sz v (wunsigned U8 i1) in
         rflags_OF U8 sz i1 r0 rc (msb sz v)
  | Error s -> Error s

(** val x86_SHRD :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> sem_tuple exec **)

let x86_SHRD sz v1 v2 i0 =
  match check_size_16_64 sz with
  | Ok _ ->
    let i1 = Word0.wand U8 i0 (x86_shift_mask sz) in
    if eq_op (GRing.ComRing.eqType (word U8)) i1
         (GRing.zero (GRing.ComRing.zmodType (word U8)))
    then Ok (rflags_None_w sz v1)
    else let j = Z.sub (wsize_bits sz) (wunsigned U8 i1) in
         if Z.ltb j Z0
         then Error ErrArith
         else let rc =
                lsb sz (wshr sz v1 (Z.sub (wunsigned U8 i1) (Zpos Coq_xH)))
              in
              let r1 = wshr sz v1 (wunsigned U8 i1) in
              let r2 = wshl sz v2 j in
              let r0 = Word0.wor sz r1 r2 in
              rflags_OF U8 sz i1 r0 rc (addb (msb sz r0) (msb sz v1))
  | Error s -> Error s

(** val x86_SAR :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_SAR sz v i0 =
  match check_size_8_64 sz with
  | Ok _ ->
    let i1 = Word0.wand U8 i0 (x86_shift_mask sz) in
    if eq_op (GRing.ComRing.eqType (word U8)) i1
         (GRing.zero (GRing.ComRing.zmodType (word U8)))
    then Ok (rflags_None_w sz v)
    else let rc = lsb sz (wsar sz v (Z.sub (wunsigned U8 i1) (Zpos Coq_xH)))
         in
         let r0 = wsar sz v (wunsigned U8 i1) in
         rflags_OF U8 sz i1 r0 rc false
  | Error s -> Error s

(** val x86_BSWAP : wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_BSWAP sz v =
  match check_size_32_64 sz with
  | Ok _ -> Ok (wbswap sz v)
  | Error s -> Error s

(** val x86_POPCNT : wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_POPCNT sz v =
  match check_size_16_64 sz with
  | Ok _ ->
    let r0 = popcnt sz v in
    Ok
    (Obj.magic ((Some false), ((Some false), ((Some false), ((Some false),
      ((Some (coq_ZF_of_word sz v)), r0))))))
  | Error s -> Error s

(** val x86_PEXT :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_PEXT sz v1 v2 =
  match check_size_32_64 sz with
  | Ok _ -> Ok (pextr sz v1 v2)
  | Error s -> Error s

(** val x86_PDEP :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_PDEP sz v1 v2 =
  match check_size_32_64 sz with
  | Ok _ -> Ok (pdep sz v1 v2)
  | Error s -> Error s

(** val x86_MOVX : wsize -> GRing.ComRing.sort -> GRing.ComRing.sort exec **)

let x86_MOVX sz x =
  match check_size_32_64 sz with
  | Ok _ -> Ok x
  | Error s -> Error s

(** val x86_MOVD : wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_MOVD sz v =
  match check_size_32_64 sz with
  | Ok _ -> Ok (zero_extend U128 sz v)
  | Error s -> Error s

(** val vector_size : velem -> wsize -> coq_Z option **)

let vector_size ve ws =
  let (q, r0) = Z.div_eucl (wsize_size ws) (wsize_size (wsize_of_velem ve)) in
  if eq_op coq_Z_eqType (Obj.magic r0) (Obj.magic int_to_Z (Posz O))
  then Some q
  else None

(** val same_vector_length :
    velem -> wsize -> velem -> wsize -> (error, unit) result **)

let same_vector_length ve sz ve' sz' =
  match vector_size ve sz with
  | Some i0 ->
    (match vector_size ve' sz' with
     | Some j ->
       if eq_op coq_Z_eqType (Obj.magic i0) (Obj.magic j)
       then Ok ()
       else Error ErrType
     | None -> Error ErrType)
  | None -> Error ErrType

(** val x86_VPMOVSX :
    velem -> wsize -> velem -> wsize -> GRing.ComRing.sort ->
    GRing.ComRing.sort exec **)

let x86_VPMOVSX ve sz ve' sz' w =
  match check_size_128_256 sz' with
  | Ok _ ->
    (match same_vector_length ve sz ve' sz' with
     | Ok _ ->
       Ok
         (lift1_vec' (wsize_of_velem ve) (wsize_of_velem ve')
           (sign_extend (wsize_of_velem ve') (wsize_of_velem ve)) sz sz' w)
     | Error s -> Error s)
  | Error s -> Error s

(** val x86_VPMOVZX :
    velem -> wsize -> velem -> wsize -> GRing.ComRing.sort ->
    GRing.ComRing.sort exec **)

let x86_VPMOVZX ve sz ve' sz' w =
  match check_size_128_256 sz' with
  | Ok _ ->
    (match same_vector_length ve sz ve' sz' with
     | Ok _ ->
       Ok
         (lift1_vec' (wsize_of_velem ve) (wsize_of_velem ve')
           (zero_extend (wsize_of_velem ve') (wsize_of_velem ve)) sz sz' w)
     | Error s -> Error s)
  | Error s -> Error s

(** val x86_VMOVDQ : wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VMOVDQ sz v =
  match check_size_128_256 sz with
  | Ok _ -> Ok v
  | Error s -> Error s

(** val x86_u128_binop :
    wsize -> (GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort)
    -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_u128_binop sz op0 v1 v2 =
  match check_size_128_256 sz with
  | Ok _ -> Ok (op0 v1 v2)
  | Error s -> Error s

(** val x86_VPAND :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPAND sz =
  x86_u128_binop sz (Word0.wand sz)

(** val x86_VPANDN :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPANDN sz =
  x86_u128_binop sz (wandn sz)

(** val x86_VPOR :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPOR sz =
  x86_u128_binop sz (Word0.wor sz)

(** val x86_VPXOR :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPXOR sz =
  x86_u128_binop sz (Word0.wxor sz)

(** val x86_VPADD :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPADD ve sz =
  x86_u128_binop sz
    (lift2_vec (wsize_of_velem ve)
      (GRing.add (GRing.ComRing.zmodType (word (wsize_of_velem ve)))) sz)

(** val x86_VPSUB :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPSUB ve sz =
  x86_u128_binop sz
    (lift2_vec (wsize_of_velem ve) (fun x y ->
      GRing.add (GRing.ComRing.zmodType (word (wsize_of_velem ve))) x
        (GRing.opp (GRing.ComRing.zmodType (word (wsize_of_velem ve))) y)) sz)

(** val x86_VPMULL :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> (error,
    sem_tuple) result **)

let x86_VPMULL ve sz v1 v2 =
  match check_size_16_32 (wsize_of_velem ve) with
  | Ok _ ->
    x86_u128_binop sz
      (lift2_vec (wsize_of_velem ve)
        (GRing.mul (GRing.ComRing.ringType (word (wsize_of_velem ve)))) sz)
      v1 v2
  | Error s -> Error s

(** val x86_VPMUL :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPMUL sz =
  x86_u128_binop sz (wpmul sz)

(** val x86_VPMULU :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPMULU sz =
  x86_u128_binop sz (wpmulu sz)

(** val x86_VPAVG :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> (error,
    sem_tuple) result **)

let x86_VPAVG ve sz v1 v2 =
  if cmp_le wsize_cmp (wsize_of_velem ve) U16
  then let avg = fun x y ->
         wrepr (wsize_of_velem ve)
           (Z.div
             (Z.add
               (Z.add (wunsigned (wsize_of_velem ve) x)
                 (wunsigned (wsize_of_velem ve) y)) (Zpos Coq_xH)) (Zpos
             (Coq_xO Coq_xH)))
       in
       x86_u128_binop sz (lift2_vec (wsize_of_velem ve) avg sz) v1 v2
  else let s = ErrType in Error s

(** val x86_VPMULH :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPMULH sz v1 v2 =
  x86_u128_binop sz (lift2_vec U16 (wmulhs U16) sz) v1 v2

(** val x86_VPMULHU :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPMULHU sz v1 v2 =
  x86_u128_binop sz (lift2_vec U16 (wmulhu U16) sz) v1 v2

(** val x86_VPMULHRS :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPMULHRS sz v1 v2 =
  x86_u128_binop sz (lift2_vec U16 (wmulhrs U16) sz) v1 v2

(** val x86_nelem_mask : wsize -> wsize -> GRing.ComRing.sort **)

let x86_nelem_mask sze szc =
  wrepr U8
    (Z.sub
      (Z.pow (Zpos (Coq_xO Coq_xH))
        (Z.sub (int_to_Z (Posz (wsize_log2 szc)))
          (int_to_Z (Posz (wsize_log2 sze))))) (Zpos Coq_xH))

(** val x86_VPEXTR :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPEXTR ve v i0 =
  match check_size_8_64 ve with
  | Ok _ ->
    let i1 = Word0.wand U8 i0 (x86_nelem_mask ve U128) in
    Ok
    (nth (GRing.zero (GRing.ComRing.zmodType (word ve)))
      (Obj.magic split_vec U128 (nat_of_wsize ve) v)
      (Z.to_nat (wunsigned U8 i1)))
  | Error s -> Error s

(** val x86_VPINSR :
    velem -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> sem_tuple exec **)

let x86_VPINSR ve v1 v2 i0 =
  let i1 = Word0.wand U8 i0 (x86_nelem_mask (wsize_of_velem ve) U128) in
  Ok (wpinsr (wsize_of_velem ve) v1 v2 i1)

(** val x86_u128_shift :
    wsize -> wsize -> (GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort) ->
    GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_u128_shift sz' sz op0 v c0 =
  match check_size_16_64 sz' with
  | Ok _ ->
    (match check_size_128_256 sz with
     | Ok _ -> Ok (lift1_vec sz' (fun v0 -> op0 v0 (wunsigned U8 c0)) sz v)
     | Error s -> Error s)
  | Error s -> Error s

(** val x86_VPSLL :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPSLL ve sz =
  x86_u128_shift (wsize_of_velem ve) sz (wshl (wsize_of_velem ve))

(** val x86_VPSRL :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPSRL ve sz =
  x86_u128_shift (wsize_of_velem ve) sz (wshr (wsize_of_velem ve))

(** val x86_VPSRA :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPSRA ve sz =
  x86_u128_shift (wsize_of_velem ve) sz (wsar (wsize_of_velem ve))

(** val x86_u128_shift_variable :
    wsize -> wsize -> (GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort) ->
    GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_u128_shift_variable ve sz op0 v1 v2 =
  match check_size_16_64 ve with
  | Ok _ ->
    (match check_size_128_256 sz with
     | Ok _ ->
       Ok
         (lift2_vec ve (fun v3 v4 ->
           op0 v3 (Z.min (wunsigned ve v4) (wsize_bits ve))) sz v1 v2)
     | Error s -> Error s)
  | Error s -> Error s

(** val x86_VPSLLV :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPSLLV ve sz =
  x86_u128_shift_variable ve sz (wshl ve)

(** val x86_VPSRLV :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPSRLV ve sz =
  x86_u128_shift_variable ve sz (wshr ve)

(** val x86_vpsxldq :
    wsize -> (GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple) ->
    GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_vpsxldq sz op0 v1 v2 =
  match check_size_128_256 sz with
  | Ok _ -> Ok (op0 v1 v2)
  | Error s -> Error s

(** val x86_VPSLLDQ :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPSLLDQ sz =
  x86_vpsxldq sz (wpslldq sz)

(** val x86_VPSRLDQ :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPSRLDQ sz =
  x86_vpsxldq sz (wpsrldq sz)

(** val x86_VPSHUFB :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPSHUFB sz =
  x86_u128_binop sz (lift2_vec U128 (wpshufb U128) sz)

(** val x86_vpshuf :
    wsize -> (GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort) ->
    GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_vpshuf sz op0 v1 v2 =
  match check_size_128_256 sz with
  | Ok _ -> Ok (op0 v1 (wunsigned U8 v2))
  | Error s -> Error s

(** val x86_VPSHUFHW :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPSHUFHW sz =
  x86_vpshuf sz (wpshufhw sz)

(** val x86_VPSHUFLW :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPSHUFLW sz =
  x86_vpshuf sz (wpshuflw sz)

(** val x86_VPSHUFD :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPSHUFD sz =
  x86_vpshuf sz (wpshufd sz)

(** val wshufps_128 :
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let wshufps_128 o s1 s2 =
  make_vec U32 U128
    ((Obj.magic wpshufd1 s1 o O) :: ((Obj.magic wpshufd1 s1 o (S O)) :: (
    (Obj.magic wpshufd1 s2 o (S (S O))) :: ((Obj.magic wpshufd1 s2 o (S (S (S
                                              O)))) :: []))))

(** val x86_VSHUFPS :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> (error, GRing.ComRing.sort) result **)

let x86_VSHUFPS sz s1 s2 o =
  match check_size_128_256 sz with
  | Ok _ -> Ok (lift2_vec U128 (wshufps_128 o) sz s1 s2)
  | Error s -> Error s

(** val x86_VPUNPCKH :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPUNPCKH ve sz =
  x86_u128_binop sz (wpunpckh sz ve)

(** val x86_VPUNPCKL :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPUNPCKL ve sz =
  x86_u128_binop sz (wpunpckl sz ve)

(** val wpblendw :
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let wpblendw m0 w1 w2 =
  let v1 = split_vec U128 (nat_of_wsize U16) w1 in
  let v2 = split_vec U128 (nat_of_wsize U16) w2 in
  let b = split_vec U8 (S O) m0 in
  let r0 =
    map3 (fun b0 v3 v4 ->
      if eq_op (GRing.Ring.eqType (word_ringType O)) (Obj.magic b0)
           (GRing.one (word_ringType O))
      then v4
      else v3) b v1 v2
  in
  make_vec U16 U128 (Obj.magic r0)

(** val x86_VPBLEND :
    Equality.sort -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPBLEND ve sz v1 v2 m0 =
  match check_size_16_32 (Obj.magic ve) with
  | Ok _ ->
    (match check_size_128_256 sz with
     | Ok _ ->
       if eq_op wsize_eqType ve (Obj.magic U32)
       then Ok (wpblendd sz v1 v2 m0)
       else Ok (lift2_vec U128 (wpblendw m0) sz v1 v2)
     | Error s -> Error s)
  | Error s -> Error s

(** val x86_VPBLENDVB :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> sem_tuple exec **)

let x86_VPBLENDVB sz x y m0 =
  match check_size_128_256 sz with
  | Ok _ -> Ok (wpblendvb sz x y m0)
  | Error s -> Error s

(** val coq_SaturatedSignedToUnsigned :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let coq_SaturatedSignedToUnsigned sz1 sz2 w =
  let i1 = wsigned sz1 w in
  let i2 = cmp_max Z.compare Z0 (cmp_min Z.compare i1 (wmax_unsigned sz2)) in
  wrepr sz2 i2

(** val coq_SaturatedSignedToSigned :
    wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let coq_SaturatedSignedToSigned sz1 sz2 w =
  let i1 = wsigned sz1 w in
  let i2 =
    cmp_max Z.compare (wmin_signed sz2)
      (cmp_min Z.compare i1 (wmax_signed sz2))
  in
  wrepr sz2 i2

(** val vpack2 :
    wsize -> wsize -> wsize -> (GRing.ComRing.sort -> GRing.ComRing.sort) ->
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let vpack2 sz1 sz2 sz op0 w1 w2 =
  make_vec sz2 sz
    (cat (map (Obj.magic op0) (split_vec sz (nat_of_wsize sz1) w1))
      (map (Obj.magic op0) (split_vec sz (nat_of_wsize sz1) w2)))

(** val x86_VPACKUS :
    Equality.sort -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    sem_tuple exec **)

let x86_VPACKUS ve sz v1 v2 =
  match check_size_16_32 (Obj.magic ve) with
  | Ok _ ->
    (match check_size_128_256 sz with
     | Ok _ ->
       let doit = fun sz0 v3 v4 ->
         if eq_op wsize_eqType ve (Obj.magic U32)
         then vpack2 U32 U16 sz0 (coq_SaturatedSignedToUnsigned U32 U16) v3 v4
         else vpack2 U16 U8 sz0 (coq_SaturatedSignedToUnsigned U16 U8) v3 v4
       in
       Ok
       (if eq_op wsize_eqType (Obj.magic sz) (Obj.magic U128)
        then doit sz v1 v2
        else lift2_vec U128 (doit U128) sz v1 v2)
     | Error s -> Error s)
  | Error s -> Error s

(** val x86_VPACKSS :
    Equality.sort -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    sem_tuple exec **)

let x86_VPACKSS ve sz v1 v2 =
  match check_size_16_32 (Obj.magic ve) with
  | Ok _ ->
    (match check_size_128_256 sz with
     | Ok _ ->
       let doit = fun sz0 v3 v4 ->
         if eq_op wsize_eqType ve (Obj.magic U32)
         then vpack2 U32 U16 sz0 (coq_SaturatedSignedToSigned U32 U16) v3 v4
         else vpack2 U16 U8 sz0 (coq_SaturatedSignedToSigned U16 U8) v3 v4
       in
       Ok
       (if eq_op wsize_eqType (Obj.magic sz) (Obj.magic U128)
        then doit sz v1 v2
        else lift2_vec U128 (doit U128) sz v1 v2)
     | Error s -> Error s)
  | Error s -> Error s

(** val x86_VPBROADCAST :
    wsize -> wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPBROADCAST ve sz v =
  match check_size_128_256 sz with
  | Ok _ -> Ok (wpbroadcast ve sz v)
  | Error s -> Error s

(** val x86_VMOVSHDUP : wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VMOVSHDUP sz v =
  match check_size_128_256 sz with
  | Ok _ -> Ok (wdup_hi (wsize_of_velem VE32) sz v)
  | Error s -> Error s

(** val x86_VMOVSLDUP : wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VMOVSLDUP sz v =
  match check_size_128_256 sz with
  | Ok _ -> Ok (wdup_lo (wsize_of_velem VE32) sz v)
  | Error s -> Error s

(** val x86_VEXTRACTI128 :
    GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VEXTRACTI128 v i0 =
  let r0 =
    if lsb U8 i0 then wshr U256 v (int_to_Z (Posz (nat_of_wsize U128))) else v
  in
  Ok (zero_extend U128 U256 r0)

(** val x86_VINSERTI128 :
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    sem_tuple exec **)

let x86_VINSERTI128 v1 v2 m0 =
  Ok (winserti128 v1 v2 m0)

(** val x86_VPERM2I128 :
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    sem_tuple exec **)

let x86_VPERM2I128 v1 v2 m0 =
  Ok (wperm2i128 v1 v2 m0)

(** val x86_VPERMD :
    GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPERMD v1 v2 =
  Ok (wpermd U256 v1 v2)

(** val x86_VPERMQ :
    GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPERMQ v m0 =
  Ok (wpermq v m0)

(** val x86_VPALIGNR128 :
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
    GRing.ComRing.sort **)

let x86_VPALIGNR128 m0 v1 v2 =
  let v = make_vec U128 U256 (v2 :: (v1 :: [])) in
  let v' =
    wshr U256 v
      (Z.mul (wunsigned U8 m0) (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
  in
  nth (GRing.zero (GRing.ComRing.zmodType (word U128)))
    (Obj.magic split_vec U256 (nat_of_wsize U128) v') O

(** val x86_VPALIGNR :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> sem_tuple exec **)

let x86_VPALIGNR sz v1 v2 m0 =
  match check_size_128_256 sz with
  | Ok _ -> Ok (lift2_vec U128 (x86_VPALIGNR128 m0) sz v1 v2)
  | Error s -> Error s

(** val x86_VPMOVMSKB :
    wsize -> wsize -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPMOVMSKB ssz dsz v =
  match check_size_32_64 dsz with
  | Ok _ ->
    (match check_size_128_256 ssz with
     | Ok _ -> Ok (wpmovmskb dsz ssz v)
     | Error s -> Error s)
  | Error s -> Error s

(** val x86_VPCMPEQ :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPCMPEQ ve sz v1 v2 =
  match check_size_8_64 (wsize_of_velem ve) with
  | Ok _ ->
    (match check_size_128_256 sz with
     | Ok _ -> Ok (wpcmpeq (wsize_of_velem ve) sz v1 v2)
     | Error s -> Error s)
  | Error s -> Error s

(** val x86_VPCMPGT :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPCMPGT ve sz v1 v2 =
  match check_size_8_64 (wsize_of_velem ve) with
  | Ok _ ->
    (match check_size_128_256 sz with
     | Ok _ -> Ok (wpcmpgt (wsize_of_velem ve) sz v1 v2)
     | Error s -> Error s)
  | Error s -> Error s

(** val x86_VPMADDUBSW :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPMADDUBSW sz v v1 =
  match check_size_128_256 sz with
  | Ok _ -> Ok (wpmaddubsw sz v v1)
  | Error s -> Error s

(** val x86_VPMADDWD :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPMADDWD sz v v1 =
  match check_size_128_256 sz with
  | Ok _ -> Ok (wpmaddwd sz v v1)
  | Error s -> Error s

(** val x86_VMOVLPD : GRing.ComRing.sort -> sem_tuple exec **)

let x86_VMOVLPD v =
  Ok (zero_extend U64 U128 v)

(** val x86_VMOVHPD : GRing.ComRing.sort -> sem_tuple exec **)

let x86_VMOVHPD v =
  Ok
    (zero_extend U64 U128
      (wshr U128 v (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        Coq_xH)))))))))

(** val x86_VPMINU :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPMINU ve sz x y =
  match check_size_8_32 (wsize_of_velem ve) with
  | Ok _ ->
    (match check_size_128_256 sz with
     | Ok _ -> Ok (wmin Unsigned (wsize_of_velem ve) sz x y)
     | Error s -> Error s)
  | Error s -> Error s

(** val x86_VPMINS :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPMINS ve sz x y =
  match check_size_8_32 (wsize_of_velem ve) with
  | Ok _ ->
    (match check_size_128_256 sz with
     | Ok _ -> Ok (wmin Signed (wsize_of_velem ve) sz x y)
     | Error s -> Error s)
  | Error s -> Error s

(** val x86_VPMAXU :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPMAXU ve sz x y =
  match check_size_8_32 (wsize_of_velem ve) with
  | Ok _ ->
    (match check_size_128_256 sz with
     | Ok _ -> Ok (wmax Unsigned (wsize_of_velem ve) sz x y)
     | Error s -> Error s)
  | Error s -> Error s

(** val x86_VPMAXS :
    velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
    exec **)

let x86_VPMAXS ve sz x y =
  match check_size_8_32 (wsize_of_velem ve) with
  | Ok _ ->
    (match check_size_128_256 sz with
     | Ok _ -> Ok (wmax Signed (wsize_of_velem ve) sz x y)
     | Error s -> Error s)
  | Error s -> Error s

(** val x86_VPTEST :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_VPTEST sz x y =
  match check_size_128_256 sz with
  | Ok _ ->
    Ok
      (Obj.magic ((Some false), ((Some
        (eq_op (GRing.ComRing.eqType (word sz)) (wandn sz x y)
          (GRing.zero (GRing.ComRing.zmodType (word sz))))), ((Some false),
        ((Some false), (Some (coq_ZF_of_word sz (Word0.wand sz x y))))))))
  | Error s -> Error s

(** val x86_AESDEC :
    GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_AESDEC v1 v2 =
  Ok (wAESDEC v1 v2)

(** val x86_AESDECLAST :
    GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_AESDECLAST v1 v2 =
  Ok (wAESDECLAST v1 v2)

(** val x86_AESENC :
    GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_AESENC v1 v2 =
  Ok (wAESENC v1 v2)

(** val x86_AESENCLAST :
    GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_AESENCLAST v1 v2 =
  Ok (wAESENCLAST v1 v2)

(** val x86_AESIMC : GRing.ComRing.sort -> sem_tuple exec **)

let x86_AESIMC v1 =
  Ok (coq_InvMixColumns v1)

(** val x86_AESKEYGENASSIST :
    GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec **)

let x86_AESKEYGENASSIST v1 v2 =
  Ok (wAESKEYGENASSIST v1 v2)

(** val wclmulq :
    GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort **)

let wclmulq x1 x2 =
  let x = zero_extend U128 U64 x1 in
  foldr (fun k r0 ->
    Word0.wxor U128
      (if wbit_n U64 x2 k
       then wshl U128 x (Z.of_nat k)
       else GRing.zero (GRing.ComRing.zmodType (word U128))) r0)
    (GRing.zero (GRing.ComRing.zmodType (word U128)))
    (iota O (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val wVPCLMULDQD :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> GRing.ComRing.sort **)

let wVPCLMULDQD sz w1 w2 k =
  let get1 = fun w ->
    nth (Obj.magic GRing.zero (GRing.ComRing.zmodType (word U64)))
      (split_vec U128 (nat_of_wsize U64) w) (nat_of_bool (wbit_n U8 k O))
  in
  let get2 = fun w ->
    nth (Obj.magic GRing.zero (GRing.ComRing.zmodType (word U64)))
      (split_vec U128 (nat_of_wsize U64) w)
      (nat_of_bool (wbit_n U8 k (S (S (S (S O))))))
  in
  let f = fun w3 w4 -> wclmulq (Obj.magic get1 w3) (Obj.magic get2 w4) in
  make_vec U128 sz
    (map2 (Obj.magic f) (split_vec sz (nat_of_wsize U128) w1)
      (split_vec sz (nat_of_wsize U128) w2))

(** val x86_VPCLMULQDQ :
    wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort
    -> sem_tuple exec **)

let x86_VPCLMULQDQ sz v1 v2 k =
  match check_size_128_256 sz with
  | Ok _ -> Ok (wVPCLMULDQD sz v1 v2 k)
  | Error s -> Error s

(** val implicit_flags :
    (register, register_ext, xmm_register, rflag, condt) Arch_decl.arg_desc
    list **)

let implicit_flags =
  map (coq_F x86_decl) (OF :: (CF :: (SF :: (PF :: (ZF :: [])))))

(** val implicit_flags_noCF :
    (register, register_ext, xmm_register, rflag, condt) Arch_decl.arg_desc
    list **)

let implicit_flags_noCF =
  map (coq_F x86_decl) (OF :: (SF :: (PF :: (ZF :: []))))

(** val iCF :
    (register, register_ext, xmm_register, rflag, condt) Arch_decl.arg_desc **)

let iCF =
  coq_F x86_decl CF

(** val reg_msb_flag : wsize -> msb_flag **)

let reg_msb_flag sz =
  if cmp_le wsize_cmp sz U16 then MSB_MERGE else MSB_CLEAR

(** val max_32 : wsize -> wsize **)

let max_32 sz =
  if cmp_le wsize_cmp sz U32 then sz else U32

(** val map_sz :
    wsize -> (register, register_ext, xmm_register, rflag, condt) asm_args ->
    (wsize * (register, register_ext, xmm_register, rflag, condt) asm_arg)
    list **)

let map_sz sz a =
  List0.map (fun a0 -> (sz, a0)) a

(** val pp_name :
    char list -> wsize -> (register, register_ext, xmm_register, rflag,
    condt) asm_args -> (register, register_ext, xmm_register, rflag, condt)
    pp_asm_op **)

let pp_name name sz args =
  { pp_aop_name = name; pp_aop_ext = PP_name; pp_aop_args = (map_sz sz args) }

(** val pp_name_ty :
    char list -> wsize list -> (register, register_ext, xmm_register, rflag,
    condt) asm_arg list -> (register, register_ext, xmm_register, rflag,
    condt) pp_asm_op **)

let pp_name_ty name ws args =
  { pp_aop_name = name; pp_aop_ext = PP_name; pp_aop_args = (zip ws args) }

(** val pp_iname :
    char list -> wsize -> (register, register_ext, xmm_register, rflag,
    condt) asm_args -> (register, register_ext, xmm_register, rflag, condt)
    pp_asm_op **)

let pp_iname name sz args =
  { pp_aop_name = name; pp_aop_ext = (PP_iname sz); pp_aop_args =
    (map_sz sz args) }

(** val pp_viname_long :
    char list -> velem -> wsize -> (register, register_ext, xmm_register,
    rflag, condt) asm_args -> (register, register_ext, xmm_register, rflag,
    condt) pp_asm_op **)

let pp_viname_long name ve sz args =
  { pp_aop_name = name; pp_aop_ext = (PP_viname (ve, true)); pp_aop_args =
    (map_sz sz args) }

(** val pp_viname :
    char list -> velem -> wsize -> (register, register_ext, xmm_register,
    rflag, condt) asm_args -> (register, register_ext, xmm_register, rflag,
    condt) pp_asm_op **)

let pp_viname name ve sz args =
  { pp_aop_name = name; pp_aop_ext = (PP_viname (ve, false)); pp_aop_args =
    (map_sz sz args) }

(** val pp_iname_w_8 :
    char list -> wsize -> (register, register_ext, xmm_register, rflag,
    condt) asm_arg list -> (register, register_ext, xmm_register, rflag,
    condt) pp_asm_op **)

let pp_iname_w_8 name sz args =
  { pp_aop_name = name; pp_aop_ext = (PP_iname sz); pp_aop_args =
    (zip (sz :: (U8 :: [])) args) }

(** val pp_iname_ww_8 :
    char list -> wsize -> (register, register_ext, xmm_register, rflag,
    condt) asm_arg list -> (register, register_ext, xmm_register, rflag,
    condt) pp_asm_op **)

let pp_iname_ww_8 name sz args =
  { pp_aop_name = name; pp_aop_ext = (PP_iname sz); pp_aop_args =
    (zip (sz :: (sz :: (U8 :: []))) args) }

(** val get_ct :
    (register, register_ext, xmm_register, rflag, condt) asm_arg list ->
    (register, register_ext, xmm_register, rflag, condt)
    pp_asm_op_ext * (register, register_ext, xmm_register, rflag, condt)
    asm_arg list **)

let get_ct args = match args with
| [] -> (PP_error, args)
| a :: args0 -> ((PP_ct a), args0)

(** val pp_ct :
    char list -> wsize -> (register, register_ext, xmm_register, rflag,
    condt) asm_arg list -> (register, register_ext, xmm_register, rflag,
    condt) pp_asm_op **)

let pp_ct name sz args =
  let (ext, args0) = get_ct args in
  { pp_aop_name = name; pp_aop_ext = ext; pp_aop_args = (map_sz sz args0) }

(** val pp_cqo :
    wsize -> (register, register_ext, xmm_register, rflag, condt) asm_args ->
    (register, register_ext, xmm_register, rflag, condt) pp_asm_op **)

let pp_cqo sz _ =
  match sz with
  | U8 ->
    let name = 'C'::('Q'::('O'::[])) in
    let ext = PP_error in
    { pp_aop_name = name; pp_aop_ext = ext; pp_aop_args = (map_sz sz []) }
  | U16 ->
    let name = 'c'::('w'::('d'::[])) in
    let ext = PP_name in
    { pp_aop_name = name; pp_aop_ext = ext; pp_aop_args = (map_sz sz []) }
  | U32 ->
    let name = 'c'::('d'::('q'::[])) in
    let ext = PP_name in
    { pp_aop_name = name; pp_aop_ext = ext; pp_aop_args = (map_sz sz []) }
  | U64 ->
    let name = 'c'::('q'::('o'::[])) in
    let ext = PP_name in
    { pp_aop_name = name; pp_aop_ext = ext; pp_aop_args = (map_sz sz []) }
  | U128 ->
    let name = 'C'::('Q'::('O'::[])) in
    let ext = PP_error in
    { pp_aop_name = name; pp_aop_ext = ext; pp_aop_args = (map_sz sz []) }
  | U256 ->
    let name = 'C'::('Q'::('O'::[])) in
    let ext = PP_error in
    { pp_aop_name = name; pp_aop_ext = ext; pp_aop_args = (map_sz sz []) }

(** val c : arg_kind list **)

let c =
  CAcond :: []

(** val r : arg_kind list **)

let r =
  CAreg :: []

(** val rx : arg_kind list **)

let rx =
  CAregx :: []

(** val m : bool -> arg_kind list **)

let m b =
  (CAmem b) :: []

(** val i : wsize -> arg_kind list **)

let i sz =
  (CAimm sz) :: []

(** val rm : bool -> arg_kind list **)

let rm b =
  CAreg :: ((CAmem b) :: [])

(** val rmi : wsize -> arg_kind list **)

let rmi sz =
  CAreg :: ((CAmem true) :: ((CAimm sz) :: []))

(** val ri : wsize -> arg_kind list **)

let ri sz =
  CAreg :: ((CAimm sz) :: [])

(** val m_r : arg_kind list list **)

let m_r =
  (m false) :: (r :: [])

(** val r_rm_false : arg_kind list list **)

let r_rm_false =
  r :: ((rm false) :: [])

(** val r_rm : arg_kind list list **)

let r_rm =
  r :: ((rm true) :: [])

(** val r_rmi : wsize -> arg_kind list list **)

let r_rmi sz =
  r :: ((rmi sz) :: [])

(** val m_ri : wsize -> arg_kind list list **)

let m_ri sz =
  (m false) :: ((ri sz) :: [])

(** val xmm : arg_kind list **)

let xmm =
  CAxmm :: []

(** val xmmm : bool -> arg_kind list **)

let xmmm b =
  CAxmm :: ((CAmem b) :: [])

(** val xmm_xmmm : arg_kind list list **)

let xmm_xmmm =
  xmm :: ((xmmm true) :: [])

(** val xmmm_xmm : arg_kind list list **)

let xmmm_xmm =
  (xmmm false) :: (xmm :: [])

(** val xmm_xmm_xmmm : arg_kind list list **)

let xmm_xmm_xmmm =
  xmm :: (xmm :: ((xmmm true) :: []))

(** val check_mov : wsize -> arg_kind list list list **)

let check_mov sz =
  (r_rmi sz) :: ((m_ri (max_32 sz)) :: [])

(** val coq_Ox86_MOV_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_MOV_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = (w_ty sz); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_MOV sz);
    id_args_kinds = (check_mov sz); id_nargs = (S (S O)); id_str_jas =
    (pp_sz ('M'::('O'::('V'::[]))) sz); id_safe = []; id_pp_asm =
    (pp_iname ('m'::('o'::('v'::[]))) sz) }), (('M'::('O'::('V'::[]))),
    (prim_8_64 (fun x -> MOV x))))

(** val check_movx : wsize -> arg_kind list list list **)

let check_movx _ =
  (rx :: ((rm true) :: [])) :: (((rm true) :: (rx :: [])) :: [])

(** val pp_movd :
    char list -> Equality.sort -> (register, register_ext, xmm_register,
    rflag, condt) asm_arg list -> (register, register_ext, xmm_register,
    rflag, condt) pp_asm_op **)

let pp_movd name sz args =
  pp_name_ty
    (if eq_op wsize_eqType sz (Obj.magic U64)
     then append name ('q'::[])
     else append name ('d'::[]))
    (match args with
     | [] -> (Obj.magic sz) :: ((Obj.magic sz) :: [])
     | y :: l ->
       (match y with
        | Arch_decl.Reg _ ->
          (match l with
           | [] -> (Obj.magic sz) :: ((Obj.magic sz) :: [])
           | a :: l0 ->
             (match a with
              | XReg _ ->
                (match l0 with
                 | [] -> (Obj.magic sz) :: (U128 :: [])
                 | _ :: _ -> (Obj.magic sz) :: ((Obj.magic sz) :: []))
              | _ -> (Obj.magic sz) :: ((Obj.magic sz) :: [])))
        | XReg _ ->
          (match l with
           | [] -> (Obj.magic sz) :: ((Obj.magic sz) :: [])
           | a :: l0 ->
             (match a with
              | Arch_decl.Reg _ ->
                (match l0 with
                 | [] -> U128 :: ((Obj.magic sz) :: [])
                 | _ :: _ -> (Obj.magic sz) :: ((Obj.magic sz) :: []))
              | _ -> (Obj.magic sz) :: ((Obj.magic sz) :: [])))
        | _ -> (Obj.magic sz) :: ((Obj.magic sz) :: []))) args

(** val coq_Ox86_MOVX_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_MOVX_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = (w_ty sz); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_MOVX sz);
    id_args_kinds = (check_movx sz); id_nargs = (S (S O)); id_str_jas =
    (pp_sz ('M'::('O'::('V'::('X'::[])))) sz); id_safe = []; id_pp_asm =
    (pp_movd ('m'::('o'::('v'::[]))) (Obj.magic sz)) }),
    (('M'::('O'::('V'::('X'::[])))), (prim_32_64 (fun x -> MOVX x))))

(** val check_movsx : wsize -> wsize -> arg_kind list list list **)

let check_movsx _ _ =
  r_rm :: []

(** val pp_movsx :
    Equality.sort -> Equality.sort -> (register, register_ext, xmm_register,
    rflag, condt) asm_arg list -> (register, register_ext, xmm_register,
    rflag, condt) pp_asm_op **)

let pp_movsx szs szd args =
  let ext =
    if (||) (eq_op wsize_eqType szd szs)
         ((&&) (eq_op wsize_eqType szd (Obj.magic U64))
           (eq_op wsize_eqType szs (Obj.magic U32)))
    then 'x'::('d'::[])
    else 'x'::[]
  in
  { pp_aop_name = ('m'::('o'::('v'::('s'::[])))); pp_aop_ext = (PP_iname2
  (ext, (Obj.magic szs), (Obj.magic szd))); pp_aop_args =
  (zip ((Obj.magic szd) :: ((Obj.magic szs) :: [])) args) }

(** val coq_Ox86_MOVSX_instr :
    (wsize -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_MOVSX_instr =
  ((fun szo szi -> { id_msb_flag = (reg_msb_flag szo); id_tin = (w_ty szi);
    id_in = ((coq_E x86_decl (S O)) :: []); id_tout = (w_ty szo); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_MOVSX szi szo);
    id_args_kinds = (check_movsx szi szo); id_nargs = (S (S O)); id_str_jas =
    (pp_sz_sz ('M'::('O'::('V'::('S'::('X'::[]))))) true szo szi); id_safe =
    []; id_pp_asm = (pp_movsx (Obj.magic szi) (Obj.magic szo)) }),
    (('M'::('O'::('V'::('S'::('X'::[]))))),
    (prim_movsx (fun x x0 -> MOVSX (x, x0)))))

(** val pp_movzx :
    wsize -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    asm_arg list -> (register, register_ext, xmm_register, rflag, condt)
    pp_asm_op **)

let pp_movzx szs szd args =
  { pp_aop_name = ('m'::('o'::('v'::('z'::[])))); pp_aop_ext = (PP_iname2
    (('x'::[]), szs, szd)); pp_aop_args = (zip (szd :: (szs :: [])) args) }

(** val coq_Ox86_MOVZX_instr :
    (wsize -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_MOVZX_instr =
  ((fun szo szi -> { id_msb_flag = (reg_msb_flag szo); id_tin = (w_ty szi);
    id_in = ((coq_E x86_decl (S O)) :: []); id_tout = (w_ty szo); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_MOVZX szi szo);
    id_args_kinds = (check_movsx szi szo); id_nargs = (S (S O)); id_str_jas =
    (pp_sz_sz ('M'::('O'::('V'::('Z'::('X'::[]))))) false szo szi); id_safe =
    []; id_pp_asm = (pp_movzx szi szo) }),
    (('M'::('O'::('V'::('Z'::('X'::[]))))),
    (prim_movzx (fun x x0 -> MOVZX (x, x0)))))

(** val check_xchg : arg_kind list list list **)

let check_xchg =
  m_r :: (r_rm :: [])

(** val coq_Ox86_XCHG_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_XCHG_instr =
  let name = 'X'::('C'::('H'::('G'::[]))) in
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
  id_in = ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])); id_tout =
  (w2_ty sz sz); id_out =
  ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])); id_semi =
  (Obj.magic x86_XCHG sz); id_args_kinds = check_xchg; id_nargs = (S (S O));
  id_str_jas = (pp_sz name sz); id_safe = []; id_pp_asm =
  (pp_name ('x'::('c'::('h'::('g'::[])))) sz) }), (name,
  (primP (arch_pd x86_decl) (fun x -> XCHG x))))

(** val c_r_rm : arg_kind list list **)

let c_r_rm =
  c :: (r :: ((rm true) :: []))

(** val coq_Ox86_CMOVcc_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_CMOVcc_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (bw2_ty sz);
    id_in =
    ((coq_E x86_decl O) :: ((coq_E x86_decl (S (S O))) :: ((coq_E x86_decl (S
                                                             O)) :: [])));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl (S O)) :: []); id_semi =
    (Obj.magic x86_CMOVcc sz); id_args_kinds = (c_r_rm :: []); id_nargs = (S
    (S (S O))); id_str_jas =
    (pp_sz ('C'::('M'::('O'::('V'::('c'::('c'::[])))))) sz); id_safe = [];
    id_pp_asm = (pp_ct ('c'::('m'::('o'::('v'::[])))) sz) }),
    (('C'::('M'::('O'::('V'::('c'::('c'::[])))))),
    (prim_16_64 (fun x -> CMOVcc x))))

(** val check_add : wsize -> arg_kind list list list **)

let check_add sz =
  (m_ri (max_32 sz)) :: ((r_rmi (max_32 sz)) :: [])

(** val coq_Ox86_ADD_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_ADD_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])); id_tout =
    (b5w_ty sz); id_out = (cat implicit_flags ((coq_E x86_decl O) :: []));
    id_semi = (Obj.magic x86_ADD sz); id_args_kinds = (check_add sz);
    id_nargs = (S (S O)); id_str_jas = (pp_sz ('A'::('D'::('D'::[]))) sz);
    id_safe = []; id_pp_asm = (pp_iname ('a'::('d'::('d'::[]))) sz) }),
    (('A'::('D'::('D'::[]))), (prim_8_64 (fun x -> ADD x))))

(** val coq_Ox86_SUB_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_SUB_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])); id_tout =
    (b5w_ty sz); id_out = (cat implicit_flags ((coq_E x86_decl O) :: []));
    id_semi = (Obj.magic x86_SUB sz); id_args_kinds = (check_add sz);
    id_nargs = (S (S O)); id_str_jas = (pp_sz ('S'::('U'::('B'::[]))) sz);
    id_safe = []; id_pp_asm = (pp_iname ('s'::('u'::('b'::[]))) sz) }),
    (('S'::('U'::('B'::[]))), (prim_8_64 (fun x -> SUB x))))

(** val check_mul : wsize -> arg_kind list list list **)

let check_mul _ =
  ((rm true) :: []) :: []

(** val coq_Ox86_MUL_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_MUL_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_R x86_decl RAX) :: ((coq_E x86_decl O) :: [])); id_tout =
    (b5w2_ty sz); id_out =
    (cat implicit_flags
      ((coq_R x86_decl RDX) :: ((coq_R x86_decl RAX) :: []))); id_semi =
    (Obj.magic x86_MUL sz); id_args_kinds = (check_mul sz); id_nargs = (S O);
    id_str_jas = (pp_sz ('M'::('U'::('L'::[]))) sz); id_safe = [];
    id_pp_asm = (pp_iname ('m'::('u'::('l'::[]))) sz) }),
    (('M'::('U'::('L'::[]))), (prim_16_64 (fun x -> MUL x))))

(** val coq_Ox86_IMUL_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_IMUL_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_R x86_decl RAX) :: ((coq_E x86_decl O) :: [])); id_tout =
    (b5w2_ty sz); id_out =
    (cat implicit_flags
      ((coq_R x86_decl RDX) :: ((coq_R x86_decl RAX) :: []))); id_semi =
    (Obj.magic x86_IMUL sz); id_args_kinds = (check_mul sz); id_nargs = (S
    O); id_str_jas = (pp_sz ('I'::('M'::('U'::('L'::[])))) sz); id_safe = [];
    id_pp_asm = (pp_iname ('i'::('m'::('u'::('l'::[])))) sz) }),
    (('I'::('M'::('U'::('L'::[])))), (prim_16_64 (fun x -> IMUL x))))

(** val coq_Ox86_IMULr_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_IMULr_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])); id_tout =
    (b5w_ty sz); id_out = (cat implicit_flags ((coq_E x86_decl O) :: []));
    id_semi = (Obj.magic x86_IMULt sz); id_args_kinds = (r_rm :: []);
    id_nargs = (S (S O)); id_str_jas =
    (pp_sz ('I'::('M'::('U'::('L'::('r'::[]))))) sz); id_safe = [];
    id_pp_asm = (pp_iname ('i'::('m'::('u'::('l'::[])))) sz) }),
    (('I'::('M'::('U'::('L'::('r'::[]))))), (prim_16_64 (fun x -> IMULr x))))

(** val coq_Ox86_IMULri_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_IMULri_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (b5w_ty sz); id_out =
    (cat implicit_flags ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_IMULt sz); id_args_kinds =
    ((r :: ((rm true) :: ((i (max_32 sz)) :: []))) :: []); id_nargs = (S (S
    (S O))); id_str_jas =
    (pp_sz ('I'::('M'::('U'::('L'::('r'::('i'::[])))))) sz); id_safe = [];
    id_pp_asm = (pp_iname ('i'::('m'::('u'::('l'::[])))) sz) }),
    (('I'::('M'::('U'::('L'::('r'::('i'::[])))))),
    (prim_16_64 (fun x -> IMULri x))))

(** val coq_Ox86_DIV_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_DIV_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w3_ty sz); id_in =
    ((coq_R x86_decl RDX) :: ((coq_R x86_decl RAX) :: ((coq_E x86_decl O) :: [])));
    id_tout = (b5w2_ty sz); id_out =
    (cat implicit_flags
      ((coq_R x86_decl RAX) :: ((coq_R x86_decl RDX) :: []))); id_semi =
    (Obj.magic x86_DIV sz); id_args_kinds = (check_mul sz); id_nargs = (S O);
    id_str_jas = (pp_sz ('D'::('I'::('V'::[]))) sz); id_safe = ((X86Division
    (sz, Unsigned)) :: []); id_pp_asm =
    (pp_iname ('d'::('i'::('v'::[]))) sz) }), (('D'::('I'::('V'::[]))),
    (prim_16_64 (fun x -> DIV x))))

(** val coq_Ox86_IDIV_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_IDIV_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w3_ty sz); id_in =
    ((coq_R x86_decl RDX) :: ((coq_R x86_decl RAX) :: ((coq_E x86_decl O) :: [])));
    id_tout = (b5w2_ty sz); id_out =
    (cat implicit_flags
      ((coq_R x86_decl RAX) :: ((coq_R x86_decl RDX) :: []))); id_semi =
    (Obj.magic x86_IDIV sz); id_args_kinds = (check_mul sz); id_nargs = (S
    O); id_str_jas = (pp_sz ('I'::('D'::('I'::('V'::[])))) sz); id_safe =
    ((X86Division (sz, Signed)) :: []); id_pp_asm =
    (pp_iname ('i'::('d'::('i'::('v'::[])))) sz) }),
    (('I'::('D'::('I'::('V'::[])))), (prim_16_64 (fun x -> IDIV x))))

(** val coq_Ox86_CQO_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_CQO_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_R x86_decl RAX) :: []); id_tout = (w_ty sz); id_out =
    ((coq_R x86_decl RDX) :: []); id_semi = (Obj.magic x86_CQO sz);
    id_args_kinds = ([] :: []); id_nargs = O; id_str_jas =
    (pp_sz ('C'::('Q'::('O'::[]))) sz); id_safe = []; id_pp_asm =
    (pp_cqo sz) }), (('C'::('Q'::('O'::[]))), (prim_16_64 (fun x -> CQO x))))

(** val coq_Ox86_ADC_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_ADC_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2b_ty sz sz);
    id_in =
    (cat ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])) (iCF :: []));
    id_tout = (b5w_ty sz); id_out =
    (cat implicit_flags ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_ADC sz); id_args_kinds = (check_add sz); id_nargs = (S (S
    O)); id_str_jas = (pp_sz ('A'::('D'::('C'::[]))) sz); id_safe = [];
    id_pp_asm = (pp_iname ('a'::('d'::('c'::[]))) sz) }),
    (('A'::('D'::('C'::[]))), (prim_8_64 (fun x -> ADC x))))

(** val coq_Ox86_SBB_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_SBB_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2b_ty sz sz);
    id_in =
    (cat ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])) (iCF :: []));
    id_tout = (b5w_ty sz); id_out =
    (cat implicit_flags ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_SBB sz); id_args_kinds = (check_add sz); id_nargs = (S (S
    O)); id_str_jas = (pp_sz ('S'::('B'::('B'::[]))) sz); id_safe = [];
    id_pp_asm = (pp_iname ('s'::('b'::('b'::[]))) sz) }),
    (('S'::('B'::('B'::[]))), (prim_8_64 (fun x -> SBB x))))

(** val check_adcx : wsize -> arg_kind list list list **)

let check_adcx _ =
  r_rm :: []

(** val coq_Ox86_ADCX_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_ADCX_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2b_ty sz sz);
    id_in =
    (cat ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: []))
      ((coq_F x86_decl CF) :: [])); id_tout = (bw_ty sz); id_out =
    ((coq_F x86_decl CF) :: ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_ADCX sz); id_args_kinds = (check_adcx sz); id_nargs = (S
    (S O)); id_str_jas = (pp_sz ('A'::('D'::('C'::('X'::[])))) sz); id_safe =
    []; id_pp_asm = (pp_iname ('a'::('d'::('c'::('x'::[])))) sz) }),
    (('A'::('D'::('C'::('X'::[])))), (prim_32_64 (fun x -> ADCX x))))

(** val coq_Ox86_ADOX_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_ADOX_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2b_ty sz sz);
    id_in =
    (cat ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: []))
      ((coq_F x86_decl OF) :: [])); id_tout = (bw_ty sz); id_out =
    ((coq_F x86_decl OF) :: ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_ADCX sz); id_args_kinds = (check_adcx sz); id_nargs = (S
    (S O)); id_str_jas = (pp_sz ('A'::('D'::('O'::('X'::[])))) sz); id_safe =
    []; id_pp_asm = (pp_iname ('a'::('d'::('o'::('x'::[])))) sz) }),
    (('A'::('D'::('O'::('X'::[])))), (prim_32_64 (fun x -> ADOX x))))

(** val check_mulx : arg_kind list list list **)

let check_mulx =
  (r :: (r :: ((rm true) :: []))) :: []

(** val coq_Ox86_MULX_lo_hi_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_MULX_lo_hi_instr =
  let name =
    'M'::('U'::('L'::('X'::('_'::('l'::('o'::('_'::('h'::('i'::[])))))))))
  in
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
  id_in = ((coq_R x86_decl RDX) :: ((coq_E x86_decl (S (S O))) :: []));
  id_tout = (w2_ty sz sz); id_out =
  ((coq_E x86_decl (S O)) :: ((coq_E x86_decl O) :: [])); id_semi =
  (Obj.magic x86_MULX_lo_hi sz); id_args_kinds = check_mulx; id_nargs = (S (S
  (S O))); id_str_jas = (pp_sz name sz); id_safe = []; id_pp_asm =
  (pp_iname ('m'::('u'::('l'::('x'::[])))) sz) }), (name,
  (prim_32_64 (fun x -> MULX_lo_hi x))))

(** val check_neg : wsize -> arg_kind list list list **)

let check_neg _ =
  ((rm false) :: []) :: []

(** val coq_Ox86_NEG_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_NEG_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl O) :: []); id_tout = (b5w_ty sz); id_out =
    (cat implicit_flags ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_NEG sz); id_args_kinds = (check_neg sz); id_nargs = (S O);
    id_str_jas = (pp_sz ('N'::('E'::('G'::[]))) sz); id_safe = [];
    id_pp_asm = (pp_iname ('n'::('e'::('g'::[]))) sz) }),
    (('N'::('E'::('G'::[]))), (prim_8_64 (fun x -> NEG x))))

(** val coq_Ox86_INC_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_INC_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl O) :: []); id_tout = (b4w_ty sz); id_out =
    (cat implicit_flags_noCF ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_INC sz); id_args_kinds = (check_neg sz); id_nargs = (S O);
    id_str_jas = (pp_sz ('I'::('N'::('C'::[]))) sz); id_safe = [];
    id_pp_asm = (pp_iname ('i'::('n'::('c'::[]))) sz) }),
    (('I'::('N'::('C'::[]))), (prim_8_64 (fun x -> INC x))))

(** val coq_Ox86_DEC_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_DEC_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl O) :: []); id_tout = (b4w_ty sz); id_out =
    (cat implicit_flags_noCF ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_DEC sz); id_args_kinds = (check_neg sz); id_nargs = (S O);
    id_str_jas = (pp_sz ('D'::('E'::('C'::[]))) sz); id_safe = [];
    id_pp_asm = (pp_iname ('d'::('e'::('c'::[]))) sz) }),
    (('D'::('E'::('C'::[]))), (prim_8_64 (fun x -> DEC x))))

(** val coq_Ox86_LZCNT_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_LZCNT_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = (b5w_ty sz); id_out =
    (cat implicit_flags ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_LZCNT sz); id_args_kinds = (r_rm :: []); id_nargs = (S (S
    O)); id_str_jas = (pp_sz ('L'::('Z'::('C'::('N'::('T'::[]))))) sz);
    id_safe = []; id_pp_asm =
    (pp_iname ('l'::('z'::('c'::('n'::('t'::[]))))) sz) }),
    (('L'::('Z'::('C'::('N'::('T'::[]))))), (prim_16_64 (fun x -> LZCNT x))))

(** val check_setcc : arg_kind list list list **)

let check_setcc =
  (c :: ((rm false) :: [])) :: []

(** val coq_Ox86_SETcc_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_SETcc_instr =
  ({ id_msb_flag = (reg_msb_flag U8); id_tin = b_ty; id_in =
    ((coq_E x86_decl O) :: []); id_tout = w8_ty; id_out =
    ((coq_E x86_decl (S O)) :: []); id_semi = (Obj.magic x86_SETcc);
    id_args_kinds = check_setcc; id_nargs = (S (S O)); id_str_jas =
    (pp_s ('S'::('E'::('T'::('c'::('c'::[])))))); id_safe = []; id_pp_asm =
    (pp_ct ('s'::('e'::('t'::[]))) U8) },
    (('S'::('E'::('T'::('c'::('c'::[]))))), (primM SETcc)))

(** val check_bt : wsize -> arg_kind list list list **)

let check_bt _ =
  ((rm true) :: ((ri U8) :: [])) :: []

(** val coq_Ox86_BT_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_BT_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])); id_tout =
    b_ty; id_out = ((coq_F x86_decl CF) :: []); id_semi =
    (Obj.magic x86_BT sz); id_args_kinds = (check_bt sz); id_nargs = (S (S
    O)); id_str_jas = (pp_sz ('B'::('T'::[])) sz); id_safe = []; id_pp_asm =
    (pp_iname ('b'::('t'::[])) sz) }), (('B'::('T'::[])),
    (prim_16_64 (fun x -> BT x))))

(** val coq_Ox86_CLC_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_CLC_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = []; id_in = []; id_tout = b_ty;
    id_out = ((coq_F x86_decl CF) :: []); id_semi = (Obj.magic x86_CLC);
    id_args_kinds = ([] :: []); id_nargs = O; id_str_jas =
    (pp_s ('C'::('L'::('C'::[])))); id_safe = []; id_pp_asm =
    (pp_name ('c'::('l'::('c'::[]))) U8) }, (('C'::('L'::('C'::[]))),
    (primM CLC)))

(** val coq_Ox86_STC_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_STC_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = []; id_in = []; id_tout = b_ty;
    id_out = ((coq_F x86_decl CF) :: []); id_semi = (Obj.magic x86_STC);
    id_args_kinds = ([] :: []); id_nargs = O; id_str_jas =
    (pp_s ('S'::('T'::('C'::[])))); id_safe = []; id_pp_asm =
    (pp_name ('s'::('t'::('c'::[]))) U8) }, (('S'::('T'::('C'::[]))),
    (primM STC)))

(** val check_lea : wsize -> arg_kind list list list **)

let check_lea _ =
  (r :: ((m true) :: [])) :: []

(** val coq_Ox86_LEA_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_LEA_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_Ec x86_decl (S O)) :: []); id_tout = (w_ty sz); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_LEA sz);
    id_args_kinds = (check_lea sz); id_nargs = (S (S O)); id_str_jas =
    (pp_sz ('L'::('E'::('A'::[]))) sz); id_safe = []; id_pp_asm =
    (pp_iname ('l'::('e'::('a'::[]))) sz) }), (('L'::('E'::('A'::[]))),
    (prim_16_64 (fun x -> LEA x))))

(** val check_test : wsize -> arg_kind list list list **)

let check_test sz =
  ((rm false) :: ((ri (max_32 sz)) :: [])) :: []

(** val coq_Ox86_TEST_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_TEST_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])); id_tout =
    b5_ty; id_out = implicit_flags; id_semi = (Obj.magic x86_TEST sz);
    id_args_kinds = (check_test sz); id_nargs = (S (S O)); id_str_jas =
    (pp_sz ('T'::('E'::('S'::('T'::[])))) sz); id_safe = []; id_pp_asm =
    (pp_iname ('t'::('e'::('s'::('t'::[])))) sz) }),
    (('T'::('E'::('S'::('T'::[])))), (prim_8_64 (fun x -> TEST x))))

(** val check_cmp : wsize -> arg_kind list list list **)

let check_cmp sz =
  ((rm false) :: ((ri (max_32 sz)) :: [])) :: (r_rm :: [])

(** val coq_Ox86_CMP_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_CMP_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])); id_tout =
    b5_ty; id_out = implicit_flags; id_semi = (Obj.magic x86_CMP sz);
    id_args_kinds = (check_cmp sz); id_nargs = (S (S O)); id_str_jas =
    (pp_sz ('C'::('M'::('P'::[]))) sz); id_safe = []; id_pp_asm =
    (pp_iname ('c'::('m'::('p'::[]))) sz) }), (('C'::('M'::('P'::[]))),
    (prim_8_64 (fun x -> CMP x))))

(** val coq_Ox86_AND_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_AND_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])); id_tout =
    (b5w_ty sz); id_out = (cat implicit_flags ((coq_E x86_decl O) :: []));
    id_semi = (Obj.magic x86_AND sz); id_args_kinds = (check_cmp sz);
    id_nargs = (S (S O)); id_str_jas = (pp_sz ('A'::('N'::('D'::[]))) sz);
    id_safe = []; id_pp_asm = (pp_iname ('a'::('n'::('d'::[]))) sz) }),
    (('A'::('N'::('D'::[]))), (prim_8_64 (fun x -> AND x))))

(** val coq_Ox86_OR_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_OR_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])); id_tout =
    (b5w_ty sz); id_out = (cat implicit_flags ((coq_E x86_decl O) :: []));
    id_semi = (Obj.magic x86_OR sz); id_args_kinds = (check_cmp sz);
    id_nargs = (S (S O)); id_str_jas = (pp_sz ('O'::('R'::[])) sz); id_safe =
    []; id_pp_asm = (pp_iname ('o'::('r'::[])) sz) }), (('O'::('R'::[])),
    (prim_8_64 (fun x -> OR x))))

(** val coq_Ox86_XOR_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_XOR_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])); id_tout =
    (b5w_ty sz); id_out = (cat implicit_flags ((coq_E x86_decl O) :: []));
    id_semi = (Obj.magic x86_XOR sz); id_args_kinds = (check_cmp sz);
    id_nargs = (S (S O)); id_str_jas = (pp_sz ('X'::('O'::('R'::[]))) sz);
    id_safe = []; id_pp_asm = (pp_iname ('x'::('o'::('r'::[]))) sz) }),
    (('X'::('O'::('R'::[]))), (prim_8_64 (fun x -> XOR x))))

(** val check_andn : wsize -> arg_kind list list list **)

let check_andn _ =
  (r :: (r :: ((rm true) :: []))) :: []

(** val coq_Ox86_ANDN_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_ANDN_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (b5w_ty sz); id_out =
    (cat implicit_flags ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_ANDN sz); id_args_kinds = (check_andn sz); id_nargs = (S
    (S (S O))); id_str_jas = (pp_sz ('A'::('N'::('D'::('N'::[])))) sz);
    id_safe = []; id_pp_asm =
    (pp_iname ('a'::('n'::('d'::('n'::[])))) sz) }),
    (('A'::('N'::('D'::('N'::[])))), (prim_32_64 (fun x -> ANDN x))))

(** val coq_Ox86_NOT_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_NOT_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl O) :: []); id_tout = (w_ty sz); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_NOT sz);
    id_args_kinds = (check_neg sz); id_nargs = (S O); id_str_jas =
    (pp_sz ('N'::('O'::('T'::[]))) sz); id_safe = []; id_pp_asm =
    (pp_iname ('n'::('o'::('t'::[]))) sz) }), (('N'::('O'::('T'::[]))),
    (prim_8_64 (fun x -> NOT x))))

(** val check_ror : wsize -> arg_kind list list list **)

let check_ror _ =
  ((rm false) :: ((ri U8) :: [])) :: []

(** val coq_Ox86_ROR_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_ROR_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8_ty sz);
    id_in = ((coq_E x86_decl O) :: ((coq_Ef x86_decl (S O) RCX) :: []));
    id_tout = (b2w_ty sz); id_out =
    ((coq_F x86_decl OF) :: ((coq_F x86_decl CF) :: ((coq_E x86_decl O) :: [])));
    id_semi = (Obj.magic x86_ROR sz); id_args_kinds = (check_ror sz);
    id_nargs = (S (S O)); id_str_jas = (pp_sz ('R'::('O'::('R'::[]))) sz);
    id_safe = []; id_pp_asm = (pp_iname_w_8 ('r'::('o'::('r'::[]))) sz) }),
    (('R'::('O'::('R'::[]))), (prim_8_64 (fun x -> ROR x))))

(** val coq_Ox86_ROL_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_ROL_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8_ty sz);
    id_in = ((coq_E x86_decl O) :: ((coq_Ef x86_decl (S O) RCX) :: []));
    id_tout = (b2w_ty sz); id_out =
    ((coq_F x86_decl OF) :: ((coq_F x86_decl CF) :: ((coq_E x86_decl O) :: [])));
    id_semi = (Obj.magic x86_ROL sz); id_args_kinds = (check_ror sz);
    id_nargs = (S (S O)); id_str_jas = (pp_sz ('R'::('O'::('L'::[]))) sz);
    id_safe = []; id_pp_asm = (pp_iname_w_8 ('r'::('o'::('l'::[]))) sz) }),
    (('R'::('O'::('L'::[]))), (prim_8_64 (fun x -> ROL x))))

(** val coq_Ox86_RCR_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_RCR_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8b_ty sz);
    id_in =
    ((coq_E x86_decl O) :: ((coq_Ef x86_decl (S O) RCX) :: ((coq_F x86_decl
                                                              CF) :: [])));
    id_tout = (b2w_ty sz); id_out =
    ((coq_F x86_decl OF) :: ((coq_F x86_decl CF) :: ((coq_E x86_decl O) :: [])));
    id_semi = (Obj.magic x86_RCR sz); id_args_kinds = (check_ror sz);
    id_nargs = (S (S O)); id_str_jas = (pp_sz ('R'::('C'::('R'::[]))) sz);
    id_safe = []; id_pp_asm = (pp_iname_w_8 ('r'::('c'::('r'::[]))) sz) }),
    (('R'::('C'::('R'::[]))), (prim_8_64 (fun x -> RCR x))))

(** val coq_Ox86_RCL_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_RCL_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8b_ty sz);
    id_in =
    ((coq_E x86_decl O) :: ((coq_Ef x86_decl (S O) RCX) :: ((coq_F x86_decl
                                                              CF) :: [])));
    id_tout = (b2w_ty sz); id_out =
    ((coq_F x86_decl OF) :: ((coq_F x86_decl CF) :: ((coq_E x86_decl O) :: [])));
    id_semi = (Obj.magic x86_RCL sz); id_args_kinds = (check_ror sz);
    id_nargs = (S (S O)); id_str_jas = (pp_sz ('R'::('C'::('L'::[]))) sz);
    id_safe = []; id_pp_asm = (pp_iname_w_8 ('r'::('c'::('l'::[]))) sz) }),
    (('R'::('C'::('L'::[]))), (prim_8_64 (fun x -> RCL x))))

(** val coq_Ox86_SHL_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_SHL_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8_ty sz);
    id_in = ((coq_E x86_decl O) :: ((coq_Ef x86_decl (S O) RCX) :: []));
    id_tout = (b5w_ty sz); id_out =
    (cat implicit_flags ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_SHL sz); id_args_kinds = (check_ror sz); id_nargs = (S (S
    O)); id_str_jas = (pp_sz ('S'::('H'::('L'::[]))) sz); id_safe = [];
    id_pp_asm = (pp_iname_w_8 ('s'::('h'::('l'::[]))) sz) }),
    (('S'::('H'::('L'::[]))), (prim_8_64 (fun x -> SHL x))))

(** val coq_Ox86_SHR_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_SHR_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8_ty sz);
    id_in = ((coq_E x86_decl O) :: ((coq_Ef x86_decl (S O) RCX) :: []));
    id_tout = (b5w_ty sz); id_out =
    (cat implicit_flags ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_SHR sz); id_args_kinds = (check_ror sz); id_nargs = (S (S
    O)); id_str_jas = (pp_sz ('S'::('H'::('R'::[]))) sz); id_safe = [];
    id_pp_asm = (pp_iname_w_8 ('s'::('h'::('r'::[]))) sz) }),
    (('S'::('H'::('R'::[]))), (prim_8_64 (fun x -> SHR x))))

(** val coq_Ox86_SAL_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_SAL_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8_ty sz);
    id_in = ((coq_E x86_decl O) :: ((coq_Ef x86_decl (S O) RCX) :: []));
    id_tout = (b5w_ty sz); id_out =
    (cat implicit_flags ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_SHL sz); id_args_kinds = (check_ror sz); id_nargs = (S (S
    O)); id_str_jas = (pp_sz ('S'::('A'::('L'::[]))) sz); id_safe = [];
    id_pp_asm = (pp_iname_w_8 ('s'::('a'::('l'::[]))) sz) }),
    (('S'::('A'::('L'::[]))), (prim_8_64 (fun x -> SAL x))))

(** val coq_Ox86_SAR_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_SAR_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8_ty sz);
    id_in = ((coq_E x86_decl O) :: ((coq_Ef x86_decl (S O) RCX) :: []));
    id_tout = (b5w_ty sz); id_out =
    (cat implicit_flags ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_SAR sz); id_args_kinds = (check_ror sz); id_nargs = (S (S
    O)); id_str_jas = (pp_sz ('S'::('A'::('R'::[]))) sz); id_safe = [];
    id_pp_asm = (pp_iname_w_8 ('s'::('a'::('r'::[]))) sz) }),
    (('S'::('A'::('R'::[]))), (prim_8_64 (fun x -> SAR x))))

(** val check_shld : wsize -> arg_kind list list list **)

let check_shld _ =
  ((rm false) :: (r :: ((ri U8) :: []))) :: []

(** val safe_shxd : wsize -> safe_cond list **)

let safe_shxd sz =
  if cmp_le wsize_cmp sz U16
  then (InRange (U8, Z0, (Zpos (Coq_xI (Coq_xI (Coq_xI Coq_xH)))), (S (S
         O)))) :: []
  else []

(** val coq_Ox86_SHLD_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_SHLD_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2w8_ty sz);
    id_in =
    ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: ((coq_Ef x86_decl (S (S
                                                         O)) RCX) :: [])));
    id_tout = (b5w_ty sz); id_out =
    (cat implicit_flags ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_SHLD sz); id_args_kinds = (check_shld sz); id_nargs = (S
    (S (S O))); id_str_jas = (pp_sz ('S'::('H'::('L'::('D'::[])))) sz);
    id_safe = (safe_shxd sz); id_pp_asm =
    (pp_iname_ww_8 ('s'::('h'::('l'::('d'::[])))) sz) }),
    (('S'::('H'::('L'::('D'::[])))), (prim_16_64 (fun x -> SHLD x))))

(** val coq_Ox86_SHRD_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_SHRD_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2w8_ty sz);
    id_in =
    ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: ((coq_Ef x86_decl (S (S
                                                         O)) RCX) :: [])));
    id_tout = (b5w_ty sz); id_out =
    (cat implicit_flags ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_SHRD sz); id_args_kinds = (check_shld sz); id_nargs = (S
    (S (S O))); id_str_jas = (pp_sz ('S'::('H'::('R'::('D'::[])))) sz);
    id_safe = (safe_shxd sz); id_pp_asm =
    (pp_iname_ww_8 ('s'::('h'::('r'::('d'::[])))) sz) }),
    (('S'::('H'::('R'::('D'::[])))), (prim_16_64 (fun x -> SHRD x))))

(** val coq_Ox86_BSWAP_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_BSWAP_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl O) :: []); id_tout = (w_ty sz); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_BSWAP sz);
    id_args_kinds = ((r :: []) :: []); id_nargs = (S O); id_str_jas =
    (pp_sz ('B'::('S'::('W'::('A'::('P'::[]))))) sz); id_safe = [];
    id_pp_asm = (pp_iname ('b'::('s'::('w'::('a'::('p'::[]))))) sz) }),
    (('B'::('S'::('W'::('A'::('P'::[]))))), (prim_32_64 (fun x -> BSWAP x))))

(** val coq_Ox86_POPCNT_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_POPCNT_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = (b5w_ty sz); id_out =
    (cat implicit_flags ((coq_E x86_decl O) :: [])); id_semi =
    (Obj.magic x86_POPCNT sz); id_args_kinds = (r_rm :: []); id_nargs = (S (S
    O)); id_str_jas =
    (pp_sz ('P'::('O'::('P'::('C'::('N'::('T'::[])))))) sz); id_safe = [];
    id_pp_asm = (pp_name ('p'::('o'::('p'::('c'::('n'::('t'::[])))))) sz) }),
    (('P'::('O'::('P'::('C'::('N'::('T'::[])))))),
    (prim_16_64 (fun x -> POPCNT x))))

(** val coq_Ox86_PEXT_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_PEXT_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_PEXT sz); id_args_kinds =
    ((r :: (r :: ((rm true) :: []))) :: []); id_nargs = (S (S (S O)));
    id_str_jas = (pp_sz ('P'::('E'::('X'::('T'::[])))) sz); id_safe = [];
    id_pp_asm = (pp_name ('p'::('e'::('x'::('t'::[])))) sz) }),
    (('P'::('E'::('X'::('T'::[])))), (prim_32_64 (fun x -> PEXT x))))

(** val coq_Ox86_PDEP_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_PDEP_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_PDEP sz); id_args_kinds =
    ((r :: (r :: ((rm true) :: []))) :: []); id_nargs = (S (S (S O)));
    id_str_jas = (pp_sz ('P'::('D'::('E'::('P'::[])))) sz); id_safe = [];
    id_pp_asm = (pp_name ('p'::('d'::('e'::('p'::[])))) sz) }),
    (('P'::('D'::('E'::('P'::[])))), (prim_32_64 (fun x -> PDEP x))))

(** val check_movd : wsize -> arg_kind list list list **)

let check_movd _ =
  (xmm :: ((rm true) :: [])) :: []

(** val coq_Ox86_MOVD_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_MOVD_instr =
  ((fun sz -> { id_msb_flag = MSB_MERGE; id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = w128_ty; id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_MOVD sz);
    id_args_kinds = (check_movd sz); id_nargs = (S (S O)); id_str_jas =
    (pp_sz ('M'::('O'::('V'::('D'::[])))) sz); id_safe = []; id_pp_asm =
    (pp_movd ('m'::('o'::('v'::[]))) (Obj.magic sz)) }),
    (('M'::('O'::('V'::('D'::[])))), (prim_32_64 (fun x -> MOVD x))))

(** val coq_Ox86_MOVV_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_MOVV_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = (w_ty sz); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_MOVX sz);
    id_args_kinds = (((rm false) :: (xmm :: [])) :: []); id_nargs = (S (S
    O)); id_str_jas = (pp_sz ('M'::('O'::('V'::('V'::[])))) sz); id_safe =
    []; id_pp_asm = (pp_movd ('m'::('o'::('v'::[]))) (Obj.magic sz)) }),
    (('M'::('O'::('V'::('V'::[])))), (prim_32_64 (fun x -> MOVV x))))

(** val coq_Ox86_VMOV_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VMOV_instr =
  ((fun sz -> { id_msb_flag = MSB_CLEAR; id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = w128_ty; id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_MOVD sz);
    id_args_kinds = (check_movd sz); id_nargs = (S (S O)); id_str_jas =
    (pp_sz ('V'::('M'::('O'::('V'::[])))) sz); id_safe = []; id_pp_asm =
    (pp_movd ('v'::('m'::('o'::('v'::[])))) (Obj.magic sz)) }),
    (('V'::('M'::('O'::('V'::[])))), (prim_32_64 (fun x -> VMOV x))))

(** val check_vmovdq : wsize -> arg_kind list list list **)

let check_vmovdq _ =
  xmm_xmmm :: (xmmm_xmm :: [])

(** val coq_Ox86_VMOVDQA_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VMOVDQA_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = (w_ty sz); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_VMOVDQ sz);
    id_args_kinds = (check_vmovdq sz); id_nargs = (S (S O)); id_str_jas =
    (pp_sz ('V'::('M'::('O'::('V'::('D'::('Q'::('A'::[]))))))) sz); id_safe =
    []; id_pp_asm =
    (pp_name ('v'::('m'::('o'::('v'::('d'::('q'::('a'::[]))))))) sz) }),
    (('V'::('M'::('O'::('V'::('D'::('Q'::('A'::[]))))))),
    (prim_128_256 (fun x -> VMOVDQA x))))

(** val coq_Ox86_VMOVDQU_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VMOVDQU_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = (w_ty sz); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_VMOVDQ sz);
    id_args_kinds = (check_vmovdq sz); id_nargs = (S (S O)); id_str_jas =
    (pp_sz ('V'::('M'::('O'::('V'::('D'::('Q'::('U'::[]))))))) sz); id_safe =
    []; id_pp_asm =
    (pp_name ('v'::('m'::('o'::('v'::('d'::('q'::('u'::[]))))))) sz) }),
    (('V'::('M'::('O'::('V'::('D'::('Q'::('U'::[]))))))),
    (prim_128_256 (fun x -> VMOVDQU x))))

(** val pp_vpmovx :
    char list -> velem -> wsize -> velem -> wsize -> (register, register_ext,
    xmm_register, rflag, condt) asm_arg list -> (register, register_ext,
    xmm_register, rflag, condt) pp_asm_op **)

let pp_vpmovx name ve sz ve' sz' args =
  { pp_aop_name = name; pp_aop_ext = (PP_viname2 (ve, ve')); pp_aop_args =
    (zip (sz' :: (sz :: [])) args) }

(** val coq_Ox86_VPMOVSX_instr :
    (velem -> wsize -> velem -> wsize -> (register, register_ext,
    xmm_register, rflag, condt) instr_desc_t) * (char list * x86_op
    prim_constructor) **)

let coq_Ox86_VPMOVSX_instr =
  let name = 'V'::('P'::('M'::('O'::('V'::('S'::('X'::[])))))) in
  ((fun ve sz ve' sz' -> { id_msb_flag = MSB_CLEAR; id_tin = ((Coq_sword
  sz) :: []); id_in = ((coq_E x86_decl (S O)) :: []); id_tout = ((Coq_sword
  sz') :: []); id_out = ((coq_E x86_decl O) :: []); id_semi =
  (Obj.magic x86_VPMOVSX ve sz ve' sz'); id_args_kinds =
  ((xmm :: ((xmmm true) :: [])) :: []); id_nargs = (S (S O)); id_str_jas =
  (pp_ve_sz_ve_sz name ve sz ve' sz'); id_safe = []; id_pp_asm =
  (pp_vpmovx ('v'::('p'::('m'::('o'::('v'::('s'::('x'::[]))))))) ve sz ve'
    sz') }), (name, (prim_vv (fun x x0 x1 x2 -> VPMOVSX (x, x0, x1, x2)))))

(** val coq_Ox86_VPMOVZX_instr :
    (velem -> wsize -> velem -> wsize -> (register, register_ext,
    xmm_register, rflag, condt) instr_desc_t) * (char list * x86_op
    prim_constructor) **)

let coq_Ox86_VPMOVZX_instr =
  let name = 'V'::('P'::('M'::('O'::('V'::('Z'::('X'::[])))))) in
  ((fun ve sz ve' sz' -> { id_msb_flag = MSB_CLEAR; id_tin = ((Coq_sword
  sz) :: []); id_in = ((coq_E x86_decl (S O)) :: []); id_tout = ((Coq_sword
  sz') :: []); id_out = ((coq_E x86_decl O) :: []); id_semi =
  (Obj.magic x86_VPMOVZX ve sz ve' sz'); id_args_kinds =
  ((xmm :: ((xmmm true) :: [])) :: []); id_nargs = (S (S O)); id_str_jas =
  (pp_ve_sz_ve_sz name ve sz ve' sz'); id_safe = []; id_pp_asm =
  (pp_vpmovx ('v'::('p'::('m'::('o'::('v'::('z'::('x'::[]))))))) ve sz ve'
    sz') }), (name, (prim_vv (fun x x0 x1 x2 -> VPMOVZX (x, x0, x1, x2)))))

(** val check_xmm_xmm_xmmm : wsize -> arg_kind list list list **)

let check_xmm_xmm_xmmm _ =
  xmm_xmm_xmmm :: []

(** val coq_Ox86_VPAND_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPAND_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPAND sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_sz ('V'::('P'::('A'::('N'::('D'::[]))))) sz); id_safe = [];
    id_pp_asm = (pp_name ('v'::('p'::('a'::('n'::('d'::[]))))) sz) }),
    (('V'::('P'::('A'::('N'::('D'::[]))))),
    (prim_128_256 (fun x -> VPAND x))))

(** val coq_Ox86_VPANDN_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPANDN_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPANDN sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_sz ('V'::('P'::('A'::('N'::('D'::('N'::[])))))) sz); id_safe = [];
    id_pp_asm = (pp_name ('v'::('p'::('a'::('n'::('d'::('n'::[])))))) sz) }),
    (('V'::('P'::('A'::('N'::('D'::('N'::[])))))),
    (prim_128_256 (fun x -> VPANDN x))))

(** val coq_Ox86_VPOR_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPOR_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPOR sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_sz ('V'::('P'::('O'::('R'::[])))) sz); id_safe = []; id_pp_asm =
    (pp_name ('v'::('p'::('o'::('r'::[])))) sz) }),
    (('V'::('P'::('O'::('R'::[])))), (prim_128_256 (fun x -> VPOR x))))

(** val coq_Ox86_VPXOR_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPXOR_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPXOR sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_sz ('V'::('P'::('X'::('O'::('R'::[]))))) sz); id_safe = [];
    id_pp_asm = (pp_name ('v'::('p'::('x'::('o'::('r'::[]))))) sz) }),
    (('V'::('P'::('X'::('O'::('R'::[]))))),
    (prim_128_256 (fun x -> VPXOR x))))

(** val coq_Ox86_VPADD_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPADD_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPADD ve sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('A'::('D'::('D'::[]))))) ve sz); id_safe = [];
    id_pp_asm = (pp_viname ('v'::('p'::('a'::('d'::('d'::[]))))) ve sz) }),
    (('V'::('P'::('A'::('D'::('D'::[]))))),
    (primV (fun x x0 -> VPADD (x, x0)))))

(** val coq_Ox86_VPSUB_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPSUB_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPSUB ve sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('S'::('U'::('B'::[]))))) ve sz); id_safe = [];
    id_pp_asm = (pp_viname ('v'::('p'::('s'::('u'::('b'::[]))))) ve sz) }),
    (('V'::('P'::('S'::('U'::('B'::[]))))),
    (primV (fun x x0 -> VPSUB (x, x0)))))

(** val coq_Ox86_VPAVG_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPAVG_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPAVG ve sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('A'::('V'::('G'::[]))))) ve sz); id_safe = [];
    id_pp_asm = (pp_viname ('v'::('p'::('a'::('v'::('g'::[]))))) ve sz) }),
    (('V'::('P'::('A'::('V'::('G'::[]))))),
    (primV_8_16 (fun x x0 -> VPAVG (x, x0)))))

(** val coq_Ox86_VPMULL_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPMULL_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPMULL ve sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('M'::('U'::('L'::('L'::[])))))) ve sz); id_safe =
    []; id_pp_asm =
    (pp_viname ('v'::('p'::('m'::('u'::('l'::('l'::[])))))) ve sz) }),
    (('V'::('P'::('M'::('U'::('L'::('L'::[])))))),
    (primV_16_32 (fun x x0 -> VPMULL (x, x0)))))

(** val coq_Ox86_VPMUL_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPMUL_instr =
  ((fun sz -> { id_msb_flag = MSB_CLEAR; id_tin = (w2_ty sz sz); id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: [])); id_tout =
    (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPMUL sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_sz ('V'::('P'::('M'::('U'::('L'::[]))))) sz); id_safe = [];
    id_pp_asm =
    (pp_name ('v'::('p'::('m'::('u'::('l'::('d'::('q'::[]))))))) sz) }),
    (('V'::('P'::('M'::('U'::('L'::[]))))),
    (prim_128_256 (fun x -> VPMUL x))))

(** val coq_Ox86_VPMULU_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPMULU_instr =
  ((fun sz -> { id_msb_flag = MSB_CLEAR; id_tin = (w2_ty sz sz); id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: [])); id_tout =
    (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPMULU sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_sz ('V'::('P'::('M'::('U'::('L'::('U'::[])))))) sz); id_safe = [];
    id_pp_asm =
    (pp_name ('v'::('p'::('m'::('u'::('l'::('u'::('d'::('q'::[])))))))) sz) }),
    (('V'::('P'::('M'::('U'::('L'::('U'::[])))))),
    (prim_128_256 (fun x -> VPMULU x))))

(** val coq_Ox86_VPMULH_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPMULH_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPMULH sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('M'::('U'::('L'::('H'::[])))))) VE16 sz);
    id_safe = []; id_pp_asm =
    (pp_viname ('v'::('p'::('m'::('u'::('l'::('h'::[])))))) VE16 sz) }),
    (('V'::('P'::('M'::('U'::('L'::('H'::[])))))),
    (primV_16 (fun _ x -> VPMULH x))))

(** val coq_Ox86_VPMULHU_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPMULHU_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPMULHU sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('M'::('U'::('L'::('H'::('U'::[]))))))) VE16 sz);
    id_safe = []; id_pp_asm =
    (pp_viname ('v'::('p'::('m'::('u'::('l'::('h'::('u'::[]))))))) VE16 sz) }),
    (('V'::('P'::('M'::('U'::('L'::('H'::('U'::[]))))))),
    (primV_16 (fun _ x -> VPMULHU x))))

(** val coq_Ox86_VPMULHRS_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPMULHRS_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPMULHRS sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('M'::('U'::('L'::('H'::('R'::('S'::[])))))))) VE16
      sz); id_safe = []; id_pp_asm =
    (pp_viname ('v'::('p'::('m'::('u'::('l'::('h'::('r'::('s'::[]))))))))
      VE16 sz) }),
    (('V'::('P'::('M'::('U'::('L'::('H'::('R'::('S'::[])))))))),
    (primV_16 (fun _ x -> VPMULHRS x))))

(** val check_vpextr : wsize -> arg_kind list list list **)

let check_vpextr _ =
  ((rm false) :: (xmm :: ((i U8) :: []))) :: []

(** val pp_viname_t :
    char list -> velem -> wsize list -> (register, register_ext,
    xmm_register, rflag, condt) asm_arg list -> (register, register_ext,
    xmm_register, rflag, condt) pp_asm_op **)

let pp_viname_t name ve ts args =
  { pp_aop_name = name; pp_aop_ext = (PP_viname (ve, false)); pp_aop_args =
    (zip ts args) }

(** val coq_Ox86_VPEXTR_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPEXTR_instr =
  ((fun sz ->
    let ve = match sz with
             | U8 -> VE8
             | U16 -> VE16
             | U32 -> VE32
             | _ -> VE64 in
    { id_msb_flag = MSB_CLEAR; id_tin = w128w8_ty; id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: [])); id_tout =
    (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPEXTR sz); id_args_kinds = (check_vpextr sz); id_nargs =
    (S (S (S O))); id_str_jas =
    (pp_sz ('V'::('P'::('E'::('X'::('T'::('R'::[])))))) sz); id_safe = [];
    id_pp_asm =
    (pp_viname_t ('v'::('p'::('e'::('x'::('t'::('r'::[])))))) ve
      ((if eq_op wsize_eqType (Obj.magic sz) (Obj.magic U32) then U32 else U64) :: (U128 :: (U8 :: [])))) }),
    (('V'::('P'::('E'::('X'::('T'::('R'::[])))))),
    (prim_8_64 (fun x -> VPEXTR x))))

(** val pp_vpinsr :
    velem -> (register, register_ext, xmm_register, rflag, condt) asm_arg
    list -> (register, register_ext, xmm_register, rflag, condt) pp_asm_op **)

let pp_vpinsr ve args =
  let rs = match ve with
           | VE64 -> U64
           | _ -> U32 in
  { pp_aop_name = ('v'::('p'::('i'::('n'::('s'::('r'::[])))))); pp_aop_ext =
  (PP_viname (ve, false)); pp_aop_args =
  (zip (U128 :: (U128 :: (rs :: (U8 :: [])))) args) }

(** val check_vpinsr : wsize -> arg_kind list list list **)

let check_vpinsr _ =
  (xmm :: (xmm :: ((rm true) :: ((i U8) :: [])))) :: []

(** val coq_Ox86_VPINSR_instr :
    (velem -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPINSR_instr =
  ((fun ve -> { id_msb_flag = MSB_CLEAR; id_tin =
    (w128ww8_ty (wsize_of_velem ve)); id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: ((coq_E
                                                                 x86_decl (S
                                                                 (S (S O)))) :: [])));
    id_tout = w128_ty; id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPINSR ve); id_args_kinds =
    (check_vpinsr (wsize_of_velem ve)); id_nargs = (S (S (S (S O))));
    id_str_jas =
    (pp_ve_sz ('V'::('P'::('I'::('N'::('S'::('R'::[])))))) ve U128);
    id_safe = []; id_pp_asm = (pp_vpinsr ve) }),
    (('V'::('P'::('I'::('N'::('S'::('R'::[])))))),
    (primV_128 (fun ve _ -> VPINSR ve))))

(** val check_xmm_xmm_imm8 : wsize -> arg_kind list list list **)

let check_xmm_xmm_imm8 _ =
  (xmm :: (xmm :: ((i U8) :: []))) :: []

(** val coq_Ox86_VPSLL_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPSLL_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8_ty sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPSLL ve sz); id_args_kinds = (check_xmm_xmm_imm8 sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('S'::('L'::('L'::[]))))) ve sz); id_safe = [];
    id_pp_asm = (pp_viname ('v'::('p'::('s'::('l'::('l'::[]))))) ve sz) }),
    (('V'::('P'::('S'::('L'::('L'::[]))))),
    (primV_16_64 (fun x x0 -> VPSLL (x, x0)))))

(** val coq_Ox86_VPSRL_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPSRL_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8_ty sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPSRL ve sz); id_args_kinds = (check_xmm_xmm_imm8 sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('S'::('R'::('L'::[]))))) ve sz); id_safe = [];
    id_pp_asm = (pp_viname ('v'::('p'::('s'::('r'::('l'::[]))))) ve sz) }),
    (('V'::('P'::('S'::('R'::('L'::[]))))),
    (primV_16_64 (fun x x0 -> VPSRL (x, x0)))))

(** val coq_Ox86_VPSRA_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPSRA_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8_ty sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPSRA ve sz); id_args_kinds = (check_xmm_xmm_imm8 sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('S'::('R'::('A'::[]))))) ve sz); id_safe = [];
    id_pp_asm = (pp_viname ('v'::('p'::('s'::('r'::('a'::[]))))) ve sz) }),
    (('V'::('P'::('S'::('R'::('A'::[]))))),
    (primV_16_64 (fun x x0 -> VPSRA (x, x0)))))

(** val coq_Ox86_VPSLLV_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPSLLV_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPSLLV (wsize_of_velem ve) sz); id_args_kinds =
    (check_xmm_xmm_xmmm sz); id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('S'::('L'::('L'::('V'::[])))))) ve sz); id_safe =
    []; id_pp_asm =
    (pp_viname ('v'::('p'::('s'::('l'::('l'::('v'::[])))))) ve sz) }),
    (('V'::('P'::('S'::('L'::('L'::('V'::[])))))),
    (primV_16_64 (fun x x0 -> VPSLLV (x, x0)))))

(** val coq_Ox86_VPSRLV_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPSRLV_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPSRLV (wsize_of_velem ve) sz); id_args_kinds =
    (check_xmm_xmm_xmmm sz); id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('S'::('R'::('L'::('V'::[])))))) ve sz); id_safe =
    []; id_pp_asm =
    (pp_viname ('v'::('p'::('s'::('r'::('l'::('v'::[])))))) ve sz) }),
    (('V'::('P'::('S'::('R'::('L'::('V'::[])))))),
    (primV_16_64 (fun x x0 -> VPSRLV (x, x0)))))

(** val coq_Ox86_VPSLLDQ_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPSLLDQ_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8_ty sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPSLLDQ sz); id_args_kinds = (check_xmm_xmm_imm8 sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_sz ('V'::('P'::('S'::('L'::('L'::('D'::('Q'::[]))))))) sz); id_safe =
    []; id_pp_asm =
    (pp_name ('v'::('p'::('s'::('l'::('l'::('d'::('q'::[]))))))) sz) }),
    (('V'::('P'::('S'::('L'::('L'::('D'::('Q'::[]))))))),
    (prim_128_256 (fun x -> VPSLLDQ x))))

(** val coq_Ox86_VPSRLDQ_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPSRLDQ_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8_ty sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPSRLDQ sz); id_args_kinds = (check_xmm_xmm_imm8 sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_sz ('V'::('P'::('S'::('R'::('L'::('D'::('Q'::[]))))))) sz); id_safe =
    []; id_pp_asm =
    (pp_name ('v'::('p'::('s'::('r'::('l'::('d'::('q'::[]))))))) sz) }),
    (('V'::('P'::('S'::('R'::('L'::('D'::('Q'::[]))))))),
    (prim_128_256 (fun x -> VPSRLDQ x))))

(** val coq_Ox86_VPSHUFB_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPSHUFB_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPSHUFB sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_sz ('V'::('P'::('S'::('H'::('U'::('F'::('B'::[]))))))) sz); id_safe =
    []; id_pp_asm =
    (pp_name ('v'::('p'::('s'::('h'::('u'::('f'::('b'::[]))))))) sz) }),
    (('V'::('P'::('S'::('H'::('U'::('F'::('B'::[]))))))),
    (prim_128_256 (fun x -> VPSHUFB x))))

(** val check_xmm_xmmm_imm8 : wsize -> arg_kind list list list **)

let check_xmm_xmmm_imm8 _ =
  (xmm :: ((xmmm true) :: ((i U8) :: []))) :: []

(** val coq_Ox86_VPSHUFHW_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPSHUFHW_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8_ty sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPSHUFHW sz); id_args_kinds = (check_xmm_xmmm_imm8 sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_sz ('V'::('P'::('S'::('H'::('U'::('F'::('H'::('W'::[])))))))) sz);
    id_safe = []; id_pp_asm =
    (pp_name ('v'::('p'::('s'::('h'::('u'::('f'::('h'::('w'::[])))))))) sz) }),
    (('V'::('P'::('S'::('H'::('U'::('F'::('H'::('W'::[])))))))),
    (prim_128_256 (fun x -> VPSHUFHW x))))

(** val coq_Ox86_VPSHUFLW_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPSHUFLW_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8_ty sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPSHUFLW sz); id_args_kinds = (check_xmm_xmmm_imm8 sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_sz ('V'::('P'::('S'::('H'::('U'::('F'::('L'::('W'::[])))))))) sz);
    id_safe = []; id_pp_asm =
    (pp_name ('v'::('p'::('s'::('h'::('u'::('f'::('l'::('w'::[])))))))) sz) }),
    (('V'::('P'::('S'::('H'::('U'::('F'::('L'::('W'::[])))))))),
    (prim_128_256 (fun x -> VPSHUFLW x))))

(** val coq_Ox86_VPSHUFD_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPSHUFD_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (ww8_ty sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPSHUFD sz); id_args_kinds = (check_xmm_xmmm_imm8 sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_sz ('V'::('P'::('S'::('H'::('U'::('F'::('D'::[]))))))) sz); id_safe =
    []; id_pp_asm =
    (pp_name ('v'::('p'::('s'::('h'::('u'::('f'::('d'::[]))))))) sz) }),
    (('V'::('P'::('S'::('H'::('U'::('F'::('D'::[]))))))),
    (prim_128_256 (fun x -> VPSHUFD x))))

(** val coq_Ox86_VPUNPCKH_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPUNPCKH_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPUNPCKH ve sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('U'::('N'::('P'::('C'::('K'::('H'::[])))))))) ve
      sz); id_safe = []; id_pp_asm =
    (pp_viname_long
      ('v'::('p'::('u'::('n'::('p'::('c'::('k'::('h'::[])))))))) ve sz) }),
    (('V'::('P'::('U'::('N'::('P'::('C'::('K'::('H'::[])))))))),
    (primV (fun x x0 -> VPUNPCKH (x, x0)))))

(** val coq_Ox86_VPUNPCKL_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPUNPCKL_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPUNPCKL ve sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('U'::('N'::('P'::('C'::('K'::('L'::[])))))))) ve
      sz); id_safe = []; id_pp_asm =
    (pp_viname_long
      ('v'::('p'::('u'::('n'::('p'::('c'::('k'::('l'::[])))))))) ve sz) }),
    (('V'::('P'::('U'::('N'::('P'::('C'::('K'::('L'::[])))))))),
    (primV (fun x x0 -> VPUNPCKL (x, x0)))))

(** val check_xmm_xmm_xmmm_imm8 : wsize -> arg_kind list list list **)

let check_xmm_xmm_xmmm_imm8 _ =
  (xmm :: (xmm :: ((xmmm true) :: ((i U8) :: [])))) :: []

(** val coq_Ox86_VPBLEND_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPBLEND_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2w8_ty sz);
    id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: ((coq_E
                                                                 x86_decl (S
                                                                 (S (S O)))) :: [])));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPBLEND (wsize_of_velem ve) sz); id_args_kinds =
    (check_xmm_xmm_xmmm_imm8 sz); id_nargs = (S (S (S (S O)))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('B'::('L'::('E'::('N'::('D'::[]))))))) ve sz);
    id_safe = []; id_pp_asm =
    (pp_viname ('v'::('p'::('b'::('l'::('e'::('n'::('d'::[]))))))) ve sz) }),
    (('V'::('P'::('B'::('L'::('E'::('N'::('D'::[]))))))),
    (primV_16_32 (fun x x0 -> VPBLEND (x, x0)))))

(** val check_xmm_xmm_xmmm_xmm : wsize -> arg_kind list list list **)

let check_xmm_xmm_xmmm_xmm _ =
  (xmm :: (xmm :: ((xmmm true) :: (xmm :: [])))) :: []

(** val coq_Ox86_VPBLENDVB_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPBLENDVB_instr =
  ((fun sz -> { id_msb_flag = MSB_CLEAR; id_tin = (w3_ty sz); id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: ((coq_E
                                                                 x86_decl (S
                                                                 (S (S O)))) :: [])));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPBLENDVB sz); id_args_kinds =
    (check_xmm_xmm_xmmm_xmm sz); id_nargs = (S (S (S (S O)))); id_str_jas =
    (pp_sz ('V'::('P'::('B'::('L'::('E'::('N'::('D'::('V'::('B'::[])))))))))
      sz); id_safe = []; id_pp_asm =
    (pp_name
      ('v'::('p'::('b'::('l'::('e'::('n'::('d'::('v'::('b'::[]))))))))) sz) }),
    (('V'::('P'::('B'::('L'::('E'::('N'::('D'::('V'::('B'::[]))))))))),
    (prim_128_256 (fun x -> VPBLENDVB x))))

(** val coq_Ox86_VPACKUS_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPACKUS_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPACKUS (wsize_of_velem ve) sz); id_args_kinds =
    (check_xmm_xmm_xmmm sz); id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('A'::('C'::('K'::('U'::('S'::[]))))))) ve sz);
    id_safe = []; id_pp_asm =
    (pp_name
      (if eq_op wsize_eqType (Obj.magic U16) (Obj.magic wsize_of_velem ve)
       then 'v'::('p'::('a'::('c'::('k'::('u'::('s'::('w'::('b'::[]))))))))
       else 'v'::('p'::('a'::('c'::('k'::('u'::('s'::('d'::('w'::[])))))))))
      sz) }), (('V'::('P'::('A'::('C'::('K'::('U'::('S'::[]))))))),
    (primV_16_32 (fun x x0 -> VPACKUS (x, x0)))))

(** val coq_Ox86_VPACKSS_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPACKSS_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPACKSS (wsize_of_velem ve) sz); id_args_kinds =
    (check_xmm_xmm_xmmm sz); id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('A'::('C'::('K'::('S'::('S'::[]))))))) ve sz);
    id_safe = []; id_pp_asm =
    (pp_name
      (if eq_op wsize_eqType (Obj.magic U16) (Obj.magic wsize_of_velem ve)
       then 'v'::('p'::('a'::('c'::('k'::('s'::('s'::('w'::('b'::[]))))))))
       else 'v'::('p'::('a'::('c'::('k'::('s'::('s'::('d'::('w'::[])))))))))
      sz) }), (('V'::('P'::('A'::('C'::('K'::('S'::('S'::[]))))))),
    (primV_16_32 (fun x x0 -> VPACKSS (x, x0)))))

(** val coq_Ox86_VSHUFPS_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VSHUFPS_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2w8_ty sz);
    id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: ((coq_E
                                                                 x86_decl (S
                                                                 (S (S O)))) :: [])));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VSHUFPS sz); id_args_kinds = (check_xmm_xmm_xmmm_imm8 sz);
    id_nargs = (S (S (S (S O)))); id_str_jas =
    (pp_sz ('V'::('S'::('H'::('U'::('F'::('P'::('S'::[]))))))) sz); id_safe =
    []; id_pp_asm =
    (pp_name ('v'::('s'::('h'::('u'::('f'::('p'::('s'::[]))))))) sz) }),
    (('V'::('S'::('H'::('U'::('F'::('P'::('S'::[]))))))),
    (prim_128_256 (fun x -> VSHUFPS x))))

(** val pp_vpbroadcast :
    velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    asm_arg list -> (register, register_ext, xmm_register, rflag, condt)
    pp_asm_op **)

let pp_vpbroadcast ve sz args =
  { pp_aop_name =
    ('v'::('p'::('b'::('r'::('o'::('a'::('d'::('c'::('a'::('s'::('t'::[])))))))))));
    pp_aop_ext = (PP_viname (ve, false)); pp_aop_args =
    (zip (sz :: ((wsize_of_velem ve) :: [])) args) }

(** val check_xmm_xmmm : wsize -> arg_kind list list list **)

let check_xmm_xmmm _ =
  (xmm :: ((xmmm true) :: [])) :: []

(** val coq_Ox86_VPBROADCAST_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPBROADCAST_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin =
    (w_ty (wsize_of_velem ve)); id_in = ((coq_E x86_decl (S O)) :: []);
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPBROADCAST (wsize_of_velem ve) sz); id_args_kinds =
    (check_xmm_xmmm sz); id_nargs = (S (S O)); id_str_jas =
    (pp_ve_sz
      ('V'::('P'::('B'::('R'::('O'::('A'::('D'::('C'::('A'::('S'::('T'::[])))))))))))
      ve sz); id_safe = []; id_pp_asm = (pp_vpbroadcast ve sz) }),
    (('V'::('P'::('B'::('R'::('O'::('A'::('D'::('C'::('A'::('S'::('T'::[]))))))))))),
    (primV (fun x x0 -> VPBROADCAST (x, x0)))))

(** val coq_Ox86_VMOVSHDUP_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VMOVSHDUP_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = (w_ty sz); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_VMOVSHDUP sz);
    id_args_kinds = (check_xmm_xmmm sz); id_nargs = (S (S O)); id_str_jas =
    (pp_sz ('V'::('M'::('O'::('V'::('S'::('H'::('D'::('U'::('P'::[])))))))))
      sz); id_safe = []; id_pp_asm =
    (pp_name
      ('v'::('m'::('o'::('v'::('s'::('h'::('d'::('u'::('p'::[]))))))))) sz) }),
    (('V'::('M'::('O'::('V'::('S'::('H'::('D'::('U'::('P'::[]))))))))),
    (prim_128_256 (fun x -> VMOVSHDUP x))))

(** val coq_Ox86_VMOVSLDUP_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VMOVSLDUP_instr =
  ((fun sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w_ty sz); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = (w_ty sz); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_VMOVSLDUP sz);
    id_args_kinds = (check_xmm_xmmm sz); id_nargs = (S (S O)); id_str_jas =
    (pp_sz ('V'::('M'::('O'::('V'::('S'::('L'::('D'::('U'::('P'::[])))))))))
      sz); id_safe = []; id_pp_asm =
    (pp_name
      ('v'::('m'::('o'::('v'::('s'::('l'::('d'::('u'::('p'::[]))))))))) sz) }),
    (('V'::('M'::('O'::('V'::('S'::('L'::('D'::('U'::('P'::[]))))))))),
    (prim_128_256 (fun x -> VMOVSLDUP x))))

(** val coq_Ox86_VPALIGNR_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPALIGNR_instr =
  ((fun sz -> { id_msb_flag = MSB_CLEAR; id_tin = (w2w8_ty sz); id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: ((coq_E
                                                                 x86_decl (S
                                                                 (S (S O)))) :: [])));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPALIGNR sz); id_args_kinds =
    (check_xmm_xmm_xmmm_imm8 sz); id_nargs = (S (S (S (S O)))); id_str_jas =
    (pp_sz ('V'::('P'::('A'::('L'::('I'::('G'::('N'::('R'::[])))))))) sz);
    id_safe = []; id_pp_asm =
    (pp_name ('v'::('p'::('a'::('l'::('i'::('g'::('n'::('r'::[])))))))) sz) }),
    (('V'::('P'::('A'::('L'::('I'::('G'::('N'::('R'::[])))))))),
    (prim_128_256 (fun x -> VPALIGNR x))))

(** val coq_Ox86_VBROADCASTI128_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_VBROADCASTI128_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = w128_ty; id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = w256_ty; id_out =
    ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPBROADCAST U128 U256); id_args_kinds =
    ((xmm :: ((m true) :: [])) :: []); id_nargs = (S (S O)); id_str_jas =
    (pp_s
      ('V'::('P'::('B'::('R'::('O'::('A'::('D'::('C'::('A'::('S'::('T'::('_'::('2'::('u'::('1'::('2'::('8'::[]))))))))))))))))));
    id_safe = []; id_pp_asm =
    (pp_name_ty
      ('v'::('b'::('r'::('o'::('a'::('d'::('c'::('a'::('s'::('t'::('i'::('1'::('2'::('8'::[]))))))))))))))
      (U256 :: (U128 :: []))) },
    (('V'::('P'::('B'::('R'::('O'::('A'::('D'::('C'::('A'::('S'::('T'::('_'::('2'::('u'::('1'::('2'::('8'::[]))))))))))))))))),
    (primM VBROADCASTI128)))

(** val check_xmmm_xmm_imm8 : wsize -> arg_kind list list list **)

let check_xmmm_xmm_imm8 _ =
  ((xmmm false) :: (xmm :: ((i U8) :: []))) :: []

(** val coq_Ox86_VEXTRACTI128_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_VEXTRACTI128_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = w256w8_ty; id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: [])); id_tout =
    w128_ty; id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VEXTRACTI128); id_args_kinds = (check_xmmm_xmm_imm8 U256);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_s
      ('V'::('E'::('X'::('T'::('R'::('A'::('C'::('T'::('I'::('1'::('2'::('8'::[])))))))))))));
    id_safe = []; id_pp_asm =
    (pp_name_ty
      ('v'::('e'::('x'::('t'::('r'::('a'::('c'::('t'::('i'::('1'::('2'::('8'::[]))))))))))))
      (U128 :: (U256 :: (U8 :: [])))) },
    (('V'::('E'::('X'::('T'::('R'::('A'::('C'::('T'::('I'::('1'::('2'::('8'::[])))))))))))),
    (primM VEXTRACTI128)))

(** val coq_Ox86_VINSERTI128_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_VINSERTI128_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = w256w128w8_ty; id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: ((coq_E
                                                                 x86_decl (S
                                                                 (S (S O)))) :: [])));
    id_tout = w256_ty; id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VINSERTI128); id_args_kinds =
    (check_xmm_xmm_xmmm_imm8 U256); id_nargs = (S (S (S (S O))));
    id_str_jas =
    (pp_s
      ('V'::('I'::('N'::('S'::('E'::('R'::('T'::('I'::('1'::('2'::('8'::[]))))))))))));
    id_safe = []; id_pp_asm =
    (pp_name_ty
      ('v'::('i'::('n'::('s'::('e'::('r'::('t'::('i'::('1'::('2'::('8'::[])))))))))))
      (U256 :: (U256 :: (U128 :: (U8 :: []))))) },
    (('V'::('I'::('N'::('S'::('E'::('R'::('T'::('I'::('1'::('2'::('8'::[]))))))))))),
    (primM VINSERTI128)))

(** val coq_Ox86_VPERM2I128_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPERM2I128_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = w256x2w8_ty; id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: ((coq_E
                                                                 x86_decl (S
                                                                 (S (S O)))) :: [])));
    id_tout = w256_ty; id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPERM2I128); id_args_kinds =
    (check_xmm_xmm_xmmm_imm8 U256); id_nargs = (S (S (S (S O))));
    id_str_jas =
    (pp_s
      ('V'::('P'::('E'::('R'::('M'::('2'::('I'::('1'::('2'::('8'::[])))))))))));
    id_safe = []; id_pp_asm =
    (pp_name_ty
      ('v'::('p'::('e'::('r'::('m'::('2'::('i'::('1'::('2'::('8'::[]))))))))))
      (U256 :: (U256 :: (U256 :: (U8 :: []))))) },
    (('V'::('P'::('E'::('R'::('M'::('2'::('I'::('1'::('2'::('8'::[])))))))))),
    (primM VPERM2I128)))

(** val coq_Ox86_VPERMD_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPERMD_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = (w2_ty U256 U256); id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: [])); id_tout =
    w256_ty; id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPERMD); id_args_kinds = (check_xmm_xmm_xmmm U256);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_s ('V'::('P'::('E'::('R'::('M'::('D'::[]))))))); id_safe = [];
    id_pp_asm =
    (pp_name ('v'::('p'::('e'::('r'::('m'::('d'::[])))))) U256) },
    (('V'::('P'::('E'::('R'::('M'::('D'::[])))))), (primM VPERMD)))

(** val coq_Ox86_VPERMQ_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPERMQ_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = w256w8_ty; id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: [])); id_tout =
    w256_ty; id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPERMQ); id_args_kinds = (check_xmm_xmmm_imm8 U256);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_s ('V'::('P'::('E'::('R'::('M'::('Q'::[]))))))); id_safe = [];
    id_pp_asm =
    (pp_name_ty ('v'::('p'::('e'::('r'::('m'::('q'::[]))))))
      (U256 :: (U256 :: (U8 :: [])))) },
    (('V'::('P'::('E'::('R'::('M'::('Q'::[])))))), (primM VPERMQ)))

(** val coq_Ox86_PMOVMSKB_instr :
    (wsize -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_PMOVMSKB_instr =
  ((fun ssz dsz -> { id_msb_flag = MSB_CLEAR; id_tin = (w_ty ssz); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = (w_ty dsz); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_VPMOVMSKB ssz dsz);
    id_args_kinds = ((r :: (xmm :: [])) :: []); id_nargs = (S (S O));
    id_str_jas =
    (pp_sz_sz
      ('V'::('P'::('M'::('O'::('V'::('M'::('S'::('K'::('B'::[]))))))))) false
      ssz dsz); id_safe = []; id_pp_asm =
    (pp_name_ty
      ('v'::('p'::('m'::('o'::('v'::('m'::('s'::('k'::('b'::[])))))))))
      (dsz :: (ssz :: []))) }),
    (('V'::('P'::('M'::('O'::('V'::('M'::('S'::('K'::('B'::[]))))))))),
    (primX (fun x x0 -> VPMOVMSKB (x, x0)))))

(** val coq_Ox86_VPCMPEQ_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPCMPEQ_instr =
  ((fun ve sz -> { id_msb_flag = MSB_CLEAR; id_tin = (w2_ty sz sz); id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: [])); id_tout =
    (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPCMPEQ ve sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('C'::('M'::('P'::('E'::('Q'::[]))))))) ve sz);
    id_safe = []; id_pp_asm =
    (pp_viname ('v'::('p'::('c'::('m'::('p'::('e'::('q'::[]))))))) ve sz) }),
    (('V'::('P'::('C'::('M'::('P'::('E'::('Q'::[]))))))),
    (primV (fun x x0 -> VPCMPEQ (x, x0)))))

(** val coq_Ox86_VPCMPGT_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPCMPGT_instr =
  ((fun ve sz -> { id_msb_flag = MSB_CLEAR; id_tin = (w2_ty sz sz); id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: [])); id_tout =
    (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPCMPGT ve sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('C'::('M'::('P'::('G'::('T'::[]))))))) ve sz);
    id_safe = []; id_pp_asm =
    (pp_viname ('v'::('p'::('c'::('m'::('p'::('g'::('t'::[]))))))) ve sz) }),
    (('V'::('P'::('C'::('M'::('P'::('G'::('T'::[]))))))),
    (primV (fun x x0 -> VPCMPGT (x, x0)))))

(** val coq_Ox86_VPMADDUBSW_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPMADDUBSW_instr =
  ((fun sz -> { id_msb_flag = MSB_CLEAR; id_tin = (w2_ty sz sz); id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: [])); id_tout =
    (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPMADDUBSW sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_sz
      ('V'::('P'::('M'::('A'::('D'::('D'::('U'::('B'::('S'::('W'::[]))))))))))
      sz); id_safe = []; id_pp_asm =
    (pp_name_ty
      ('v'::('p'::('m'::('a'::('d'::('d'::('u'::('b'::('s'::('w'::[]))))))))))
      (sz :: (sz :: (sz :: [])))) }),
    (('V'::('P'::('M'::('A'::('D'::('D'::('U'::('B'::('S'::('W'::[])))))))))),
    (prim_128_256 (fun x -> VPMADDUBSW x))))

(** val coq_Ox86_VPMADDWD_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPMADDWD_instr =
  ((fun sz -> { id_msb_flag = MSB_CLEAR; id_tin = (w2_ty sz sz); id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: [])); id_tout =
    (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPMADDWD sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_sz ('V'::('P'::('M'::('A'::('D'::('D'::('W'::('D'::[])))))))) sz);
    id_safe = []; id_pp_asm =
    (pp_name_ty ('v'::('p'::('m'::('a'::('d'::('d'::('w'::('d'::[]))))))))
      (sz :: (sz :: (sz :: [])))) }),
    (('V'::('P'::('M'::('A'::('D'::('D'::('W'::('D'::[])))))))),
    (prim_128_256 (fun x -> VPMADDWD x))))

(** val check_movpd : arg_kind list list list **)

let check_movpd =
  ((m false) :: (xmm :: [])) :: []

(** val coq_Ox86_VMOVLPD_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_VMOVLPD_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = (w_ty U128); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = (w_ty U64); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_VMOVLPD);
    id_args_kinds = check_movpd; id_nargs = (S (S O)); id_str_jas =
    (pp_s ('V'::('M'::('O'::('V'::('L'::('P'::('D'::[])))))))); id_safe = [];
    id_pp_asm =
    (pp_name_ty ('v'::('m'::('o'::('v'::('l'::('p'::('d'::[])))))))
      (U64 :: (U128 :: []))) },
    (('V'::('M'::('O'::('V'::('L'::('P'::('D'::[]))))))), (primM VMOVLPD)))

(** val coq_Ox86_VMOVHPD_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_VMOVHPD_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = (w_ty U128); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = (w_ty U64); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_VMOVHPD);
    id_args_kinds = check_movpd; id_nargs = (S (S O)); id_str_jas =
    (pp_s ('V'::('M'::('O'::('V'::('H'::('P'::('D'::[])))))))); id_safe = [];
    id_pp_asm =
    (pp_name_ty ('v'::('m'::('o'::('v'::('h'::('p'::('d'::[])))))))
      (U64 :: (U128 :: []))) },
    (('V'::('M'::('O'::('V'::('H'::('P'::('D'::[]))))))), (primM VMOVHPD)))

(** val coq_Ox86_VPMINS_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPMINS_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPMINS ve sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('M'::('I'::('N'::('S'::[])))))) ve sz); id_safe =
    []; id_pp_asm =
    (pp_viname ('v'::('p'::('m'::('i'::('n'::('s'::[])))))) ve sz) }),
    (('V'::('P'::('M'::('I'::('N'::('S'::[])))))),
    (primV_8_32 (fun x x0 -> VPMINS (x, x0)))))

(** val coq_Ox86_VPMINU_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPMINU_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPMINU ve sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('M'::('I'::('N'::('U'::[])))))) ve sz); id_safe =
    []; id_pp_asm =
    (pp_viname ('v'::('p'::('m'::('i'::('n'::('u'::[])))))) ve sz) }),
    (('V'::('P'::('M'::('I'::('N'::('U'::[])))))),
    (primV_8_32 (fun x x0 -> VPMINU (x, x0)))))

(** val coq_Ox86_VPMAXS_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPMAXS_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPMAXS ve sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('M'::('A'::('X'::('S'::[])))))) ve sz); id_safe =
    []; id_pp_asm =
    (pp_viname ('v'::('p'::('m'::('a'::('x'::('s'::[])))))) ve sz) }),
    (('V'::('P'::('M'::('A'::('X'::('S'::[])))))),
    (primV_8_32 (fun x x0 -> VPMAXS (x, x0)))))

(** val coq_Ox86_VPMAXU_instr :
    (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPMAXU_instr =
  ((fun ve sz -> { id_msb_flag = (reg_msb_flag sz); id_tin = (w2_ty sz sz);
    id_in = ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: []));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPMAXU ve sz); id_args_kinds = (check_xmm_xmm_xmmm sz);
    id_nargs = (S (S (S O))); id_str_jas =
    (pp_ve_sz ('V'::('P'::('M'::('A'::('X'::('U'::[])))))) ve sz); id_safe =
    []; id_pp_asm =
    (pp_viname ('v'::('p'::('m'::('a'::('x'::('u'::[])))))) ve sz) }),
    (('V'::('P'::('M'::('A'::('X'::('U'::[])))))),
    (primV_8_32 (fun x x0 -> VPMAXU (x, x0)))))

(** val check_vptest : wsize -> arg_kind list list list **)

let check_vptest _ =
  xmm_xmmm :: []

(** val coq_Ox86_VPTEST_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPTEST_instr =
  ((fun sz -> { id_msb_flag = MSB_MERGE; id_tin = (w2_ty sz sz); id_in =
    ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])); id_tout = b5_ty;
    id_out = implicit_flags; id_semi = (Obj.magic x86_VPTEST sz);
    id_args_kinds = (check_vptest sz); id_nargs = (S (S O)); id_str_jas =
    (pp_sz ('V'::('P'::('T'::('E'::('S'::('T'::[])))))) sz); id_safe = [];
    id_pp_asm = (pp_name ('v'::('p'::('t'::('e'::('s'::('t'::[])))))) sz) }),
    (('V'::('P'::('T'::('E'::('S'::('T'::[])))))),
    (prim_128_256 (fun x -> VPTEST x))))

(** val coq_Ox86_RDTSC_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_RDTSC_instr =
  ((fun sz -> { id_msb_flag = MSB_CLEAR; id_tin = []; id_in = []; id_tout =
    (w2_ty sz sz); id_out =
    ((coq_R x86_decl RDX) :: ((coq_R x86_decl RAX) :: [])); id_semi =
    (Obj.magic (Error ErrType)); id_args_kinds = ([] :: []); id_nargs = O;
    id_str_jas = (pp_sz ('R'::('D'::('T'::('S'::('C'::[]))))) sz); id_safe =
    []; id_pp_asm =
    (pp_name_ty ('r'::('d'::('t'::('s'::('c'::[]))))) (sz :: (sz :: []))) }),
    (('R'::('D'::('T'::('S'::('C'::[]))))), (prim_32_64 (fun x -> RDTSC x))))

(** val coq_Ox86_RDTSCP_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_RDTSCP_instr =
  ((fun sz -> { id_msb_flag = MSB_CLEAR; id_tin = []; id_in = []; id_tout =
    (w3_ty sz); id_out =
    ((coq_R x86_decl RDX) :: ((coq_R x86_decl RAX) :: ((coq_R x86_decl RCX) :: [])));
    id_semi = (Obj.magic (Error ErrType)); id_args_kinds = ([] :: []);
    id_nargs = O; id_str_jas =
    (pp_sz ('R'::('D'::('T'::('S'::('C'::('P'::[])))))) sz); id_safe = [];
    id_pp_asm =
    (pp_name_ty ('r'::('d'::('t'::('s'::('c'::('p'::[]))))))
      (sz :: (sz :: (sz :: [])))) }),
    (('R'::('D'::('T'::('S'::('C'::('P'::[])))))),
    (prim_32_64 (fun x -> RDTSCP x))))

(** val coq_Ox86_CLFLUSH_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_CLFLUSH_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = ((Coq_sword
    (coq_Uptr (arch_pd x86_decl))) :: []); id_in =
    ((coq_Ec x86_decl O) :: []); id_tout = []; id_out = []; id_semi =
    (Obj.magic (fun _ -> Ok ())); id_args_kinds = (((m true) :: []) :: []);
    id_nargs = (S O); id_str_jas =
    (pp_s ('C'::('L'::('F'::('L'::('U'::('S'::('H'::[])))))))); id_safe = [];
    id_pp_asm =
    (pp_name ('c'::('l'::('f'::('l'::('u'::('s'::('h'::[])))))))
      (coq_Uptr (arch_pd x86_decl))) },
    (('C'::('L'::('F'::('L'::('U'::('S'::('H'::[]))))))), (primM CLFLUSH)))

(** val coq_Ox86_LFENCE_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_LFENCE_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = []; id_in = []; id_tout = []; id_out =
    []; id_semi = (Obj.magic (Ok ())); id_args_kinds = ([] :: []); id_nargs =
    O; id_str_jas = (pp_s ('L'::('F'::('E'::('N'::('C'::('E'::[])))))));
    id_safe = []; id_pp_asm =
    (pp_name ('l'::('f'::('e'::('n'::('c'::('e'::[])))))) U8) },
    (('L'::('F'::('E'::('N'::('C'::('E'::[])))))), (primM LFENCE)))

(** val coq_Ox86_MFENCE_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_MFENCE_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = []; id_in = []; id_tout = []; id_out =
    []; id_semi = (Obj.magic (Ok ())); id_args_kinds = ([] :: []); id_nargs =
    O; id_str_jas = (pp_s ('M'::('F'::('E'::('N'::('C'::('E'::[])))))));
    id_safe = []; id_pp_asm =
    (pp_name ('m'::('f'::('e'::('n'::('c'::('e'::[])))))) U8) },
    (('M'::('F'::('E'::('N'::('C'::('E'::[])))))), (primM MFENCE)))

(** val coq_Ox86_SFENCE_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_SFENCE_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = []; id_in = []; id_tout = []; id_out =
    []; id_semi = (Obj.magic (Ok ())); id_args_kinds = ([] :: []); id_nargs =
    O; id_str_jas = (pp_s ('S'::('F'::('E'::('N'::('C'::('E'::[])))))));
    id_safe = []; id_pp_asm =
    (pp_name ('s'::('f'::('e'::('n'::('c'::('e'::[])))))) U8) },
    (('S'::('F'::('E'::('N'::('C'::('E'::[])))))), (primM SFENCE)))

(** val mk_instr_aes2 :
    char list -> char list -> x86_op -> sem_tuple exec sem_prod -> msb_flag
    -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let mk_instr_aes2 jname aname constr x86_sem msb_flag0 =
  ({ id_msb_flag = msb_flag0; id_tin = (w2_ty U128 U128); id_in =
    ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: [])); id_tout =
    (w_ty U128); id_out = ((coq_E x86_decl O) :: []); id_semi = x86_sem;
    id_args_kinds = (check_xmm_xmmm U128); id_nargs = (S (S O)); id_str_jas =
    (pp_s jname); id_safe = []; id_pp_asm =
    (pp_name_ty aname (U128 :: (U128 :: []))) }, (jname, (primM constr)))

(** val mk_instr_aes3 :
    char list -> char list -> x86_op -> sem_tuple exec sem_prod -> msb_flag
    -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let mk_instr_aes3 jname aname constr x86_sem msb_flag0 =
  ({ id_msb_flag = msb_flag0; id_tin = (w2_ty U128 U128); id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: [])); id_tout =
    (w_ty U128); id_out = ((coq_E x86_decl O) :: []); id_semi = x86_sem;
    id_args_kinds = (check_xmm_xmm_xmmm U128); id_nargs = (S (S (S O)));
    id_str_jas = (pp_s jname); id_safe = []; id_pp_asm =
    (pp_name_ty aname (U128 :: (U128 :: (U128 :: [])))) }, (jname,
    (primM constr)))

(** val coq_Ox86_AESDEC_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_AESDEC_instr =
  mk_instr_aes2 ('A'::('E'::('S'::('D'::('E'::('C'::[]))))))
    ('a'::('e'::('s'::('d'::('e'::('c'::[])))))) AESDEC
    (Obj.magic x86_AESDEC) MSB_MERGE

(** val coq_Ox86_VAESDEC_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_VAESDEC_instr =
  mk_instr_aes3 ('V'::('A'::('E'::('S'::('D'::('E'::('C'::[])))))))
    ('v'::('a'::('e'::('s'::('d'::('e'::('c'::[]))))))) VAESDEC
    (Obj.magic x86_AESDEC) MSB_CLEAR

(** val coq_Ox86_AESDECLAST_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_AESDECLAST_instr =
  mk_instr_aes2
    ('A'::('E'::('S'::('D'::('E'::('C'::('L'::('A'::('S'::('T'::[]))))))))))
    ('a'::('e'::('s'::('d'::('e'::('c'::('l'::('a'::('s'::('t'::[]))))))))))
    AESDECLAST (Obj.magic x86_AESDECLAST) MSB_MERGE

(** val coq_Ox86_VAESDECLAST_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_VAESDECLAST_instr =
  mk_instr_aes3
    ('V'::('A'::('E'::('S'::('D'::('E'::('C'::('L'::('A'::('S'::('T'::[])))))))))))
    ('v'::('a'::('e'::('s'::('d'::('e'::('c'::('l'::('a'::('s'::('t'::[])))))))))))
    VAESDECLAST (Obj.magic x86_AESDECLAST) MSB_CLEAR

(** val coq_Ox86_AESENC_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_AESENC_instr =
  mk_instr_aes2 ('A'::('E'::('S'::('E'::('N'::('C'::[]))))))
    ('a'::('e'::('s'::('e'::('n'::('c'::[])))))) AESENC
    (Obj.magic x86_AESENC) MSB_MERGE

(** val coq_Ox86_VAESENC_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_VAESENC_instr =
  mk_instr_aes3 ('V'::('A'::('E'::('S'::('E'::('N'::('C'::[])))))))
    ('v'::('a'::('e'::('s'::('e'::('n'::('c'::[]))))))) VAESENC
    (Obj.magic x86_AESENC) MSB_CLEAR

(** val coq_Ox86_AESENCLAST_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_AESENCLAST_instr =
  mk_instr_aes2
    ('A'::('E'::('S'::('E'::('N'::('C'::('L'::('A'::('S'::('T'::[]))))))))))
    ('a'::('e'::('s'::('e'::('n'::('c'::('l'::('a'::('s'::('t'::[]))))))))))
    AESENCLAST (Obj.magic x86_AESENCLAST) MSB_MERGE

(** val coq_Ox86_VAESENCLAST_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_VAESENCLAST_instr =
  mk_instr_aes3
    ('V'::('A'::('E'::('S'::('E'::('N'::('C'::('L'::('A'::('S'::('T'::[])))))))))))
    ('v'::('a'::('e'::('s'::('e'::('n'::('c'::('l'::('a'::('s'::('t'::[])))))))))))
    VAESENCLAST (Obj.magic x86_AESENCLAST) MSB_CLEAR

(** val coq_Ox86_AESIMC_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_AESIMC_instr =
  ({ id_msb_flag = MSB_MERGE; id_tin = (w_ty U128); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = (w_ty U128); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_AESIMC);
    id_args_kinds = (check_xmm_xmmm U128); id_nargs = (S (S O)); id_str_jas =
    (pp_s ('A'::('E'::('S'::('I'::('M'::('C'::[]))))))); id_safe = [];
    id_pp_asm =
    (pp_name_ty ('a'::('e'::('s'::('i'::('m'::('c'::[]))))))
      (U128 :: (U128 :: []))) },
    (('A'::('E'::('S'::('I'::('M'::('C'::[])))))), (primM AESIMC)))

(** val coq_Ox86_VAESIMC_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_VAESIMC_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = (w_ty U128); id_in =
    ((coq_E x86_decl (S O)) :: []); id_tout = (w_ty U128); id_out =
    ((coq_E x86_decl O) :: []); id_semi = (Obj.magic x86_AESIMC);
    id_args_kinds = (check_xmm_xmmm U128); id_nargs = (S (S O)); id_str_jas =
    (pp_s ('V'::('A'::('E'::('S'::('I'::('M'::('C'::[])))))))); id_safe = [];
    id_pp_asm =
    (pp_name_ty ('v'::('a'::('e'::('s'::('i'::('m'::('c'::[])))))))
      (U128 :: (U128 :: []))) },
    (('V'::('A'::('E'::('S'::('I'::('M'::('C'::[]))))))), (primM VAESIMC)))

(** val coq_Ox86_AESKEYGENASSIST_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_AESKEYGENASSIST_instr =
  ({ id_msb_flag = MSB_MERGE; id_tin = (w2_ty U128 U8); id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: [])); id_tout =
    (w_ty U128); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_AESKEYGENASSIST); id_args_kinds =
    (check_xmm_xmmm_imm8 U128); id_nargs = (S (S (S O))); id_str_jas =
    (pp_s
      ('A'::('E'::('S'::('K'::('E'::('Y'::('G'::('E'::('N'::('A'::('S'::('S'::('I'::('S'::('T'::[]))))))))))))))));
    id_safe = []; id_pp_asm =
    (pp_name_ty
      ('a'::('e'::('s'::('k'::('e'::('y'::('g'::('e'::('n'::('a'::('s'::('s'::('i'::('s'::('t'::[])))))))))))))))
      (U128 :: (U128 :: (U8 :: [])))) },
    (('A'::('E'::('S'::('K'::('E'::('Y'::('G'::('E'::('N'::('A'::('S'::('S'::('I'::('S'::('T'::[]))))))))))))))),
    (primM AESKEYGENASSIST)))

(** val coq_Ox86_VAESKEYGENASSIST_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_VAESKEYGENASSIST_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = (w2_ty U128 U8); id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: [])); id_tout =
    (w_ty U128); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_AESKEYGENASSIST); id_args_kinds =
    (check_xmm_xmmm_imm8 U128); id_nargs = (S (S (S O))); id_str_jas =
    (pp_s
      ('V'::('A'::('E'::('S'::('K'::('E'::('Y'::('G'::('E'::('N'::('A'::('S'::('S'::('I'::('S'::('T'::[])))))))))))))))));
    id_safe = []; id_pp_asm =
    (pp_name_ty
      ('v'::('a'::('e'::('s'::('k'::('e'::('y'::('g'::('e'::('n'::('a'::('s'::('s'::('i'::('s'::('t'::[]))))))))))))))))
      (U128 :: (U128 :: (U8 :: [])))) },
    (('V'::('A'::('E'::('S'::('K'::('E'::('Y'::('G'::('E'::('N'::('A'::('S'::('S'::('I'::('S'::('T'::[])))))))))))))))),
    (primM VAESKEYGENASSIST)))

(** val coq_Ox86_PCLMULQDQ_instr :
    (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t * (char list * x86_op prim_constructor) **)

let coq_Ox86_PCLMULQDQ_instr =
  ({ id_msb_flag = MSB_CLEAR; id_tin = ((Coq_sword U128) :: ((Coq_sword
    U128) :: ((Coq_sword U8) :: []))); id_in =
    ((coq_E x86_decl O) :: ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S
                                                         O))) :: [])));
    id_tout = (w_ty U128); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPCLMULQDQ U128); id_args_kinds =
    (check_xmm_xmmm_imm8 U128); id_nargs = (S (S (S O))); id_str_jas =
    (pp_s ('P'::('C'::('L'::('M'::('U'::('L'::('Q'::('D'::('Q'::[]))))))))));
    id_safe = []; id_pp_asm =
    (pp_name_ty
      ('p'::('c'::('l'::('m'::('u'::('l'::('q'::('d'::('q'::[])))))))))
      (U128 :: (U128 :: (U8 :: [])))) },
    (('P'::('C'::('L'::('M'::('U'::('L'::('Q'::('D'::('Q'::[]))))))))),
    (primM PCLMULQDQ)))

(** val coq_Ox86_VPCLMULQDQ_instr :
    (wsize -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t) * (char list * x86_op prim_constructor) **)

let coq_Ox86_VPCLMULQDQ_instr =
  ((fun sz -> { id_msb_flag = MSB_CLEAR; id_tin = ((Coq_sword
    sz) :: ((Coq_sword sz) :: ((Coq_sword U8) :: []))); id_in =
    ((coq_E x86_decl (S O)) :: ((coq_E x86_decl (S (S O))) :: ((coq_E
                                                                 x86_decl (S
                                                                 (S (S O)))) :: [])));
    id_tout = (w_ty sz); id_out = ((coq_E x86_decl O) :: []); id_semi =
    (Obj.magic x86_VPCLMULQDQ sz); id_args_kinds =
    (check_xmm_xmm_xmmm_imm8 sz); id_nargs = (S (S (S (S O)))); id_str_jas =
    (pp_sz
      ('V'::('P'::('C'::('L'::('M'::('U'::('L'::('Q'::('D'::('Q'::[]))))))))))
      sz); id_safe = []; id_pp_asm =
    (pp_name
      ('v'::('p'::('c'::('l'::('m'::('u'::('l'::('q'::('d'::('q'::[]))))))))))
      sz) }),
    (('V'::('P'::('C'::('L'::('M'::('U'::('L'::('Q'::('D'::('Q'::[])))))))))),
    (prim_128_256 (fun x -> VPCLMULQDQ x))))

(** val x86_instr_desc :
    x86_op -> (register, register_ext, xmm_register, rflag, condt)
    instr_desc_t **)

let x86_instr_desc = function
| MOV sz -> fst coq_Ox86_MOV_instr sz
| MOVSX (sz, sz') -> fst coq_Ox86_MOVSX_instr sz sz'
| MOVZX (sz, sz') -> fst coq_Ox86_MOVZX_instr sz sz'
| CMOVcc sz -> fst coq_Ox86_CMOVcc_instr sz
| XCHG sz -> fst coq_Ox86_XCHG_instr sz
| ADD sz -> fst coq_Ox86_ADD_instr sz
| SUB sz -> fst coq_Ox86_SUB_instr sz
| MUL sz -> fst coq_Ox86_MUL_instr sz
| IMUL sz -> fst coq_Ox86_IMUL_instr sz
| IMULr sz -> fst coq_Ox86_IMULr_instr sz
| IMULri sz -> fst coq_Ox86_IMULri_instr sz
| DIV sz -> fst coq_Ox86_DIV_instr sz
| IDIV sz -> fst coq_Ox86_IDIV_instr sz
| CQO sz -> fst coq_Ox86_CQO_instr sz
| ADC sz -> fst coq_Ox86_ADC_instr sz
| SBB sz -> fst coq_Ox86_SBB_instr sz
| NEG sz -> fst coq_Ox86_NEG_instr sz
| INC sz -> fst coq_Ox86_INC_instr sz
| DEC sz -> fst coq_Ox86_DEC_instr sz
| LZCNT sz -> fst coq_Ox86_LZCNT_instr sz
| SETcc -> fst coq_Ox86_SETcc_instr
| BT sz -> fst coq_Ox86_BT_instr sz
| CLC -> fst coq_Ox86_CLC_instr
| STC -> fst coq_Ox86_STC_instr
| LEA sz -> fst coq_Ox86_LEA_instr sz
| TEST sz -> fst coq_Ox86_TEST_instr sz
| CMP sz -> fst coq_Ox86_CMP_instr sz
| AND sz -> fst coq_Ox86_AND_instr sz
| ANDN sz -> fst coq_Ox86_ANDN_instr sz
| OR sz -> fst coq_Ox86_OR_instr sz
| XOR sz -> fst coq_Ox86_XOR_instr sz
| NOT sz -> fst coq_Ox86_NOT_instr sz
| ROR sz -> fst coq_Ox86_ROR_instr sz
| ROL sz -> fst coq_Ox86_ROL_instr sz
| RCR sz -> fst coq_Ox86_RCR_instr sz
| RCL sz -> fst coq_Ox86_RCL_instr sz
| SHL sz -> fst coq_Ox86_SHL_instr sz
| SHR sz -> fst coq_Ox86_SHR_instr sz
| SAL sz -> fst coq_Ox86_SAL_instr sz
| SAR sz -> fst coq_Ox86_SAR_instr sz
| SHLD sz -> fst coq_Ox86_SHLD_instr sz
| SHRD sz -> fst coq_Ox86_SHRD_instr sz
| MULX_lo_hi sz -> fst coq_Ox86_MULX_lo_hi_instr sz
| ADCX sz -> fst coq_Ox86_ADCX_instr sz
| ADOX sz -> fst coq_Ox86_ADOX_instr sz
| BSWAP sz -> fst coq_Ox86_BSWAP_instr sz
| POPCNT sz -> fst coq_Ox86_POPCNT_instr sz
| PEXT sz -> fst coq_Ox86_PEXT_instr sz
| PDEP sz -> fst coq_Ox86_PDEP_instr sz
| MOVX sz -> fst coq_Ox86_MOVX_instr sz
| MOVD sz -> fst coq_Ox86_MOVD_instr sz
| MOVV sz -> fst coq_Ox86_MOVV_instr sz
| VMOV sz -> fst coq_Ox86_VMOV_instr sz
| VMOVDQA sz -> fst coq_Ox86_VMOVDQA_instr sz
| VMOVDQU sz -> fst coq_Ox86_VMOVDQU_instr sz
| VPMOVSX (ve, sz, ve', sz') -> fst coq_Ox86_VPMOVSX_instr ve sz ve' sz'
| VPMOVZX (ve, sz, ve', sz') -> fst coq_Ox86_VPMOVZX_instr ve sz ve' sz'
| VPAND sz -> fst coq_Ox86_VPAND_instr sz
| VPANDN sz -> fst coq_Ox86_VPANDN_instr sz
| VPOR sz -> fst coq_Ox86_VPOR_instr sz
| VPXOR sz -> fst coq_Ox86_VPXOR_instr sz
| VPADD (sz, sz') -> fst coq_Ox86_VPADD_instr sz sz'
| VPSUB (sz, sz') -> fst coq_Ox86_VPSUB_instr sz sz'
| VPAVG (sz, sz') -> fst coq_Ox86_VPAVG_instr sz sz'
| VPMULL (sz, sz') -> fst coq_Ox86_VPMULL_instr sz sz'
| VPMULH sz -> fst coq_Ox86_VPMULH_instr sz
| VPMULHU sz -> fst coq_Ox86_VPMULHU_instr sz
| VPMULHRS sz -> fst coq_Ox86_VPMULHRS_instr sz
| VPMUL sz -> fst coq_Ox86_VPMUL_instr sz
| VPMULU sz -> fst coq_Ox86_VPMULU_instr sz
| VPEXTR ve -> fst coq_Ox86_VPEXTR_instr ve
| VPINSR sz -> fst coq_Ox86_VPINSR_instr sz
| VPSLL (sz, sz') -> fst coq_Ox86_VPSLL_instr sz sz'
| VPSRL (sz, sz') -> fst coq_Ox86_VPSRL_instr sz sz'
| VPSRA (sz, sz') -> fst coq_Ox86_VPSRA_instr sz sz'
| VPSLLV (sz, sz') -> fst coq_Ox86_VPSLLV_instr sz sz'
| VPSRLV (sz, sz') -> fst coq_Ox86_VPSRLV_instr sz sz'
| VPSLLDQ sz -> fst coq_Ox86_VPSLLDQ_instr sz
| VPSRLDQ sz -> fst coq_Ox86_VPSRLDQ_instr sz
| VPSHUFB sz -> fst coq_Ox86_VPSHUFB_instr sz
| VPSHUFD sz -> fst coq_Ox86_VPSHUFD_instr sz
| VPSHUFHW sz -> fst coq_Ox86_VPSHUFHW_instr sz
| VPSHUFLW sz -> fst coq_Ox86_VPSHUFLW_instr sz
| VPBLEND (ve, sz) -> fst coq_Ox86_VPBLEND_instr ve sz
| VPBLENDVB sz -> fst coq_Ox86_VPBLENDVB_instr sz
| VPACKUS (ve, sz) -> fst coq_Ox86_VPACKUS_instr ve sz
| VPACKSS (ve, sz) -> fst coq_Ox86_VPACKSS_instr ve sz
| VSHUFPS sz -> fst coq_Ox86_VSHUFPS_instr sz
| VPBROADCAST (sz, sz') -> fst coq_Ox86_VPBROADCAST_instr sz sz'
| VMOVSHDUP sz -> fst coq_Ox86_VMOVSHDUP_instr sz
| VMOVSLDUP sz -> fst coq_Ox86_VMOVSLDUP_instr sz
| VPALIGNR sz -> fst coq_Ox86_VPALIGNR_instr sz
| VBROADCASTI128 -> fst coq_Ox86_VBROADCASTI128_instr
| VPUNPCKH (sz, sz') -> fst coq_Ox86_VPUNPCKH_instr sz sz'
| VPUNPCKL (sz, sz') -> fst coq_Ox86_VPUNPCKL_instr sz sz'
| VEXTRACTI128 -> fst coq_Ox86_VEXTRACTI128_instr
| VINSERTI128 -> fst coq_Ox86_VINSERTI128_instr
| VPERM2I128 -> fst coq_Ox86_VPERM2I128_instr
| VPERMD -> fst coq_Ox86_VPERMD_instr
| VPERMQ -> fst coq_Ox86_VPERMQ_instr
| VPMOVMSKB (sz, sz') -> fst coq_Ox86_PMOVMSKB_instr sz sz'
| VPCMPEQ (ve, sz) -> fst coq_Ox86_VPCMPEQ_instr ve sz
| VPCMPGT (ve, sz) -> fst coq_Ox86_VPCMPGT_instr ve sz
| VPMADDUBSW sz -> fst coq_Ox86_VPMADDUBSW_instr sz
| VPMADDWD sz -> fst coq_Ox86_VPMADDWD_instr sz
| VMOVLPD -> fst coq_Ox86_VMOVLPD_instr
| VMOVHPD -> fst coq_Ox86_VMOVHPD_instr
| VPMINU (ve, sz) -> fst coq_Ox86_VPMINU_instr ve sz
| VPMINS (ve, sz) -> fst coq_Ox86_VPMINS_instr ve sz
| VPMAXU (ve, sz) -> fst coq_Ox86_VPMAXU_instr ve sz
| VPMAXS (ve, sz) -> fst coq_Ox86_VPMAXS_instr ve sz
| VPTEST sz -> fst coq_Ox86_VPTEST_instr sz
| CLFLUSH -> fst coq_Ox86_CLFLUSH_instr
| LFENCE -> fst coq_Ox86_LFENCE_instr
| MFENCE -> fst coq_Ox86_MFENCE_instr
| SFENCE -> fst coq_Ox86_SFENCE_instr
| RDTSC sz -> fst coq_Ox86_RDTSC_instr sz
| RDTSCP sz -> fst coq_Ox86_RDTSCP_instr sz
| AESDEC -> fst coq_Ox86_AESDEC_instr
| VAESDEC -> fst coq_Ox86_VAESDEC_instr
| AESDECLAST -> fst coq_Ox86_AESDECLAST_instr
| VAESDECLAST -> fst coq_Ox86_VAESDECLAST_instr
| AESENC -> fst coq_Ox86_AESENC_instr
| VAESENC -> fst coq_Ox86_VAESENC_instr
| AESENCLAST -> fst coq_Ox86_AESENCLAST_instr
| VAESENCLAST -> fst coq_Ox86_VAESENCLAST_instr
| AESIMC -> fst coq_Ox86_AESIMC_instr
| VAESIMC -> fst coq_Ox86_VAESIMC_instr
| AESKEYGENASSIST -> fst coq_Ox86_AESKEYGENASSIST_instr
| VAESKEYGENASSIST -> fst coq_Ox86_VAESKEYGENASSIST_instr
| PCLMULQDQ -> fst coq_Ox86_PCLMULQDQ_instr
| VPCLMULQDQ sz -> fst coq_Ox86_VPCLMULQDQ_instr sz

(** val x86_prim_string : (char list * x86_op prim_constructor) list **)

let x86_prim_string =
  (snd coq_Ox86_MOV_instr) :: ((snd coq_Ox86_MOVSX_instr) :: ((snd
                                                                coq_Ox86_MOVZX_instr) :: (
    (snd coq_Ox86_CMOVcc_instr) :: ((snd coq_Ox86_XCHG_instr) :: ((snd
                                                                    coq_Ox86_BSWAP_instr) :: (
    (snd coq_Ox86_POPCNT_instr) :: ((snd coq_Ox86_PEXT_instr) :: ((snd
                                                                    coq_Ox86_PDEP_instr) :: (
    (snd coq_Ox86_CQO_instr) :: ((snd coq_Ox86_ADD_instr) :: ((snd
                                                                coq_Ox86_SUB_instr) :: (
    (snd coq_Ox86_MUL_instr) :: ((snd coq_Ox86_IMUL_instr) :: ((snd
                                                                 coq_Ox86_IMULr_instr) :: (
    (snd coq_Ox86_IMULri_instr) :: ((snd coq_Ox86_DIV_instr) :: ((snd
                                                                   coq_Ox86_IDIV_instr) :: (
    (snd coq_Ox86_ADC_instr) :: ((snd coq_Ox86_ADCX_instr) :: ((snd
                                                                 coq_Ox86_ADOX_instr) :: (
    (snd coq_Ox86_MULX_lo_hi_instr) :: ((snd coq_Ox86_SBB_instr) :: (
    (snd coq_Ox86_NEG_instr) :: ((snd coq_Ox86_INC_instr) :: ((snd
                                                                coq_Ox86_DEC_instr) :: (
    (snd coq_Ox86_LZCNT_instr) :: ((snd coq_Ox86_SETcc_instr) :: ((snd
                                                                    coq_Ox86_BT_instr) :: (
    (snd coq_Ox86_CLC_instr) :: ((snd coq_Ox86_STC_instr) :: ((snd
                                                                coq_Ox86_LEA_instr) :: (
    (snd coq_Ox86_TEST_instr) :: ((snd coq_Ox86_CMP_instr) :: ((snd
                                                                 coq_Ox86_AND_instr) :: (
    (snd coq_Ox86_ANDN_instr) :: ((snd coq_Ox86_OR_instr) :: ((snd
                                                                coq_Ox86_XOR_instr) :: (
    (snd coq_Ox86_NOT_instr) :: ((snd coq_Ox86_ROL_instr) :: ((snd
                                                                coq_Ox86_ROR_instr) :: (
    (snd coq_Ox86_RCL_instr) :: ((snd coq_Ox86_RCR_instr) :: ((snd
                                                                coq_Ox86_SHL_instr) :: (
    (snd coq_Ox86_SHR_instr) :: ((snd coq_Ox86_SAR_instr) :: ((snd
                                                                coq_Ox86_SAL_instr) :: (
    (snd coq_Ox86_SHLD_instr) :: ((snd coq_Ox86_SHRD_instr) :: ((snd
                                                                  coq_Ox86_MOVX_instr) :: (
    (snd coq_Ox86_MOVD_instr) :: ((snd coq_Ox86_MOVV_instr) :: ((snd
                                                                  coq_Ox86_VMOV_instr) :: (
    (snd coq_Ox86_VPMOVSX_instr) :: ((snd coq_Ox86_VPMOVZX_instr) :: (
    (snd coq_Ox86_VPINSR_instr) :: ((snd coq_Ox86_VEXTRACTI128_instr) :: (
    (snd coq_Ox86_VMOVDQA_instr) :: ((snd coq_Ox86_VMOVDQU_instr) :: (
    (snd coq_Ox86_VPAND_instr) :: ((snd coq_Ox86_VPANDN_instr) :: ((snd
                                                                    coq_Ox86_VPOR_instr) :: (
    (snd coq_Ox86_VPXOR_instr) :: ((snd coq_Ox86_VPADD_instr) :: ((snd
                                                                    coq_Ox86_VPSUB_instr) :: (
    (snd coq_Ox86_VPAVG_instr) :: ((snd coq_Ox86_VPMULL_instr) :: ((snd
                                                                    coq_Ox86_VPMUL_instr) :: (
    (snd coq_Ox86_VPMULU_instr) :: ((snd coq_Ox86_VPMULH_instr) :: ((snd
                                                                    coq_Ox86_VPMULHU_instr) :: (
    (snd coq_Ox86_VPMULHRS_instr) :: ((snd coq_Ox86_VPSLL_instr) :: (
    (snd coq_Ox86_VPSRL_instr) :: ((snd coq_Ox86_VPSRA_instr) :: ((snd
                                                                    coq_Ox86_VPSLLV_instr) :: (
    (snd coq_Ox86_VPSRLV_instr) :: ((snd coq_Ox86_VPSLLDQ_instr) :: (
    (snd coq_Ox86_VPSRLDQ_instr) :: ((snd coq_Ox86_VPSHUFB_instr) :: (
    (snd coq_Ox86_VPSHUFHW_instr) :: ((snd coq_Ox86_VPSHUFLW_instr) :: (
    (snd coq_Ox86_VPSHUFD_instr) :: ((snd coq_Ox86_VSHUFPS_instr) :: (
    (snd coq_Ox86_VPUNPCKH_instr) :: ((snd coq_Ox86_VPUNPCKL_instr) :: (
    (snd coq_Ox86_VPBLEND_instr) :: ((snd coq_Ox86_VPBLENDVB_instr) :: (
    (snd coq_Ox86_VPACKUS_instr) :: ((snd coq_Ox86_VPACKSS_instr) :: (
    (snd coq_Ox86_VPBROADCAST_instr) :: ((snd coq_Ox86_VMOVSHDUP_instr) :: (
    (snd coq_Ox86_VMOVSLDUP_instr) :: ((snd coq_Ox86_VPALIGNR_instr) :: (
    (snd coq_Ox86_VBROADCASTI128_instr) :: ((snd coq_Ox86_VPERM2I128_instr) :: (
    (snd coq_Ox86_VPERMD_instr) :: ((snd coq_Ox86_VPERMQ_instr) :: ((snd
                                                                    coq_Ox86_VINSERTI128_instr) :: (
    (snd coq_Ox86_VPEXTR_instr) :: ((snd coq_Ox86_PMOVMSKB_instr) :: (
    (snd coq_Ox86_VPCMPEQ_instr) :: ((snd coq_Ox86_VPCMPGT_instr) :: (
    (snd coq_Ox86_VPMADDUBSW_instr) :: ((snd coq_Ox86_VPMADDWD_instr) :: (
    (snd coq_Ox86_VMOVLPD_instr) :: ((snd coq_Ox86_VMOVHPD_instr) :: (
    (snd coq_Ox86_VPMINU_instr) :: ((snd coq_Ox86_VPMINS_instr) :: ((snd
                                                                    coq_Ox86_VPMAXU_instr) :: (
    (snd coq_Ox86_VPMAXS_instr) :: ((snd coq_Ox86_VPTEST_instr) :: ((snd
                                                                    coq_Ox86_CLFLUSH_instr) :: (
    (snd coq_Ox86_LFENCE_instr) :: ((snd coq_Ox86_MFENCE_instr) :: ((snd
                                                                    coq_Ox86_SFENCE_instr) :: (
    (snd coq_Ox86_RDTSC_instr) :: ((snd coq_Ox86_RDTSCP_instr) :: ((snd
                                                                    coq_Ox86_AESDEC_instr) :: (
    (snd coq_Ox86_VAESDEC_instr) :: ((snd coq_Ox86_AESDECLAST_instr) :: (
    (snd coq_Ox86_VAESDECLAST_instr) :: ((snd coq_Ox86_AESENC_instr) :: (
    (snd coq_Ox86_VAESENC_instr) :: ((snd coq_Ox86_AESENCLAST_instr) :: (
    (snd coq_Ox86_VAESENCLAST_instr) :: ((snd coq_Ox86_AESIMC_instr) :: (
    (snd coq_Ox86_VAESIMC_instr) :: ((snd coq_Ox86_AESKEYGENASSIST_instr) :: (
    (snd coq_Ox86_VAESKEYGENASSIST_instr) :: ((snd coq_Ox86_PCLMULQDQ_instr) :: (
    (snd coq_Ox86_VPCLMULQDQ_instr) :: ((('V'::('P'::('M'::('A'::('X'::[]))))),
    (primSV_8_32 (fun signedness0 ve sz ->
      match signedness0 with
      | Signed -> VPMAXS (ve, sz)
      | Unsigned -> VPMAXU (ve, sz)))) :: ((('V'::('P'::('M'::('I'::('N'::[]))))),
    (primSV_8_32 (fun signedness0 ve sz ->
      match signedness0 with
      | Signed -> VPMINS (ve, sz)
      | Unsigned -> VPMINU (ve, sz)))) :: [])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eqC_x86_op : x86_op eqTypeC **)

let eqC_x86_op =
  { beq = x86_op_beq; ceqP = x86_op_eq_axiom }

(** val x86_op_decl :
    (register, register_ext, xmm_register, rflag, condt, x86_op) asm_op_decl **)

let x86_op_decl =
  { Arch_decl._eqT = eqC_x86_op; instr_desc_op = x86_instr_desc;
    Arch_decl.prim_string = x86_prim_string }

type x86_prog =
  (register, register_ext, xmm_register, rflag, condt, x86_op) asm_prog
