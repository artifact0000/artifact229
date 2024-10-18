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

val x86_op_beq : x86_op -> x86_op -> bool

val x86_op_eq_dec : x86_op -> x86_op -> bool

val x86_op_eq_axiom : x86_op Equality.axiom

val x86_op_eqMixin : x86_op Equality.mixin_of

val x86_op_eqType : Equality.coq_type

val b_ty : stype list

val b4_ty : stype list

val b5_ty : stype list

val bw_ty : wsize -> stype list

val bw2_ty : wsize -> stype list

val b2w_ty : wsize -> stype list

val b4w_ty : wsize -> stype list

val b5w_ty : wsize -> stype list

val b5w2_ty : wsize -> stype list

val w_ty : wsize -> stype list

val w2_ty : wsize -> wsize -> stype list

val w3_ty : wsize -> stype list

val w8_ty : stype list

val w128_ty : stype list

val w256_ty : stype list

val w2b_ty : wsize -> wsize -> stype list

val ww8_ty : wsize -> stype list

val ww8b_ty : wsize -> stype list

val w2w8_ty : wsize -> stype list

val w128w8_ty : stype list

val w128ww8_ty : wsize -> stype list

val w256w8_ty : stype list

val w256w128w8_ty : stype list

val w256x2w8_ty : stype list

val coq_SF_of_word : wsize -> GRing.ComRing.sort -> bool

val coq_PF_of_word : wsize -> GRing.ComRing.sort -> bool

val coq_ZF_of_word : wsize -> GRing.ComRing.sort -> bool

val rflags_of_bwop : wsize -> GRing.ComRing.sort -> sem_tuple

val rflags_of_aluop :
  wsize -> GRing.ComRing.sort -> coq_Z -> coq_Z -> sem_tuple

val rflags_of_mul : bool -> sem_tuple

val rflags_of_div : sem_tuple

val rflags_of_andn : wsize -> GRing.ComRing.sort -> sem_tuple

val rflags_None_w : wsize -> sem_ot -> sem_tuple

val rflags_of_aluop_nocf : wsize -> GRing.ComRing.sort -> coq_Z -> sem_tuple

val flags_w : __ list -> ltuple -> wsize -> GRing.ComRing.sort -> ltuple

val flags_w2 : __ list -> ltuple -> wsize -> sem_tuple -> ltuple

val rflags_of_aluop_w :
  wsize -> GRing.ComRing.sort -> coq_Z -> coq_Z -> ltuple

val rflags_of_aluop_nocf_w : wsize -> GRing.ComRing.sort -> coq_Z -> ltuple

val rflags_of_bwop_w : wsize -> GRing.ComRing.sort -> ltuple

val prim_8_64 : (wsize -> 'a1) -> 'a1 prim_constructor

val prim_16_64 : (wsize -> 'a1) -> 'a1 prim_constructor

val prim_32_64 : (wsize -> 'a1) -> 'a1 prim_constructor

val prim_128_256 : (wsize -> 'a1) -> 'a1 prim_constructor

val prim_movsx : (wsize -> wsize -> x86_op) -> x86_op prim_constructor

val prim_movzx : (wsize -> wsize -> x86_op) -> x86_op prim_constructor

val prim_vv :
  (velem -> wsize -> velem -> wsize -> x86_op) -> x86_op prim_constructor

val primV_range :
  prim_x86_suffix list -> (velem -> wsize -> x86_op) -> x86_op
  prim_constructor

val primV : (velem -> wsize -> x86_op) -> x86_op prim_constructor

val primV_8_16 : (velem -> wsize -> x86_op) -> x86_op prim_constructor

val primV_8_32 : (velem -> wsize -> x86_op) -> x86_op prim_constructor

val primV_16 : (velem -> wsize -> x86_op) -> x86_op prim_constructor

val primV_16_32 : (velem -> wsize -> x86_op) -> x86_op prim_constructor

val primV_16_64 : (velem -> wsize -> x86_op) -> x86_op prim_constructor

val primV_128 : (velem -> wsize -> x86_op) -> x86_op prim_constructor

val primSV_8_32 :
  (signedness -> velem -> wsize -> x86_op) -> x86_op prim_constructor

val primX : (wsize -> wsize -> x86_op) -> x86_op prim_constructor

val x86_MOV : wsize -> GRing.ComRing.sort -> GRing.ComRing.sort exec

val x86_MOVSX : wsize -> wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_MOVZX : wsize -> wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_XCHG :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_ADD :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_SUB :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_CMOVcc :
  wsize -> bool -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_MUL :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_IMUL_overflow :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool

val x86_IMUL :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_IMULt :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_DIV :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  sem_tuple exec

val x86_IDIV :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  sem_tuple exec

val x86_CQO : wsize -> GRing.ComRing.sort -> GRing.ComRing.sort exec

val add_carry : wsize -> coq_Z -> coq_Z -> coq_Z -> GRing.ComRing.sort

val x86_ADC :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool -> sem_tuple exec

val x86_ADCX :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool -> sem_tuple exec

val x86_MULX_lo_hi :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val sub_borrow : wsize -> coq_Z -> coq_Z -> coq_Z -> GRing.ComRing.sort

val x86_SBB :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool -> sem_tuple exec

val x86_NEG : wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_INC : wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_DEC : wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_LZCNT : wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_SETcc : bool -> sem_tuple exec

val x86_BT :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_CLC : sem_tuple exec

val x86_STC : sem_tuple exec

val x86_LEA : wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_TEST :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_CMP :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_AND :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_ANDN :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_OR :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_XOR :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_NOT : wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_shift_mask : wsize -> GRing.ComRing.sort

val x86_ROR :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_ROL :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_rotate_with_carry :
  wsize -> (word -> nat -> word) -> (GRing.ComRing.sort -> bool -> bool) ->
  GRing.ComRing.sort -> GRing.ComRing.sort -> bool -> sem_tuple exec

val x86_RCL :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool -> sem_tuple exec

val x86_RCR :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool -> sem_tuple exec

val rflags_OF :
  wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> bool -> bool
  -> sem_tuple exec

val x86_SHL :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_SHLD :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  sem_tuple exec

val x86_SHR :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_SHRD :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  sem_tuple exec

val x86_SAR :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_BSWAP : wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_POPCNT : wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_PEXT :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_PDEP :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_MOVX : wsize -> GRing.ComRing.sort -> GRing.ComRing.sort exec

val x86_MOVD : wsize -> GRing.ComRing.sort -> sem_tuple exec

val vector_size : velem -> wsize -> coq_Z option

val same_vector_length :
  velem -> wsize -> velem -> wsize -> (error, unit) result

val x86_VPMOVSX :
  velem -> wsize -> velem -> wsize -> GRing.ComRing.sort ->
  GRing.ComRing.sort exec

val x86_VPMOVZX :
  velem -> wsize -> velem -> wsize -> GRing.ComRing.sort ->
  GRing.ComRing.sort exec

val x86_VMOVDQ : wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_u128_binop :
  wsize -> (GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort)
  -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPAND :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPANDN :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPOR :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPXOR :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPADD :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPSUB :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPMULL :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> (error,
  sem_tuple) result

val x86_VPMUL :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPMULU :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPAVG :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> (error,
  sem_tuple) result

val x86_VPMULH :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPMULHU :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPMULHRS :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_nelem_mask : wsize -> wsize -> GRing.ComRing.sort

val x86_VPEXTR :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPINSR :
  velem -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  sem_tuple exec

val x86_u128_shift :
  wsize -> wsize -> (GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort) ->
  GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPSLL :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPSRL :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPSRA :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_u128_shift_variable :
  wsize -> wsize -> (GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort) ->
  GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPSLLV :
  wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPSRLV :
  wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_vpsxldq :
  wsize -> (GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple) ->
  GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPSLLDQ :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPSRLDQ :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPSHUFB :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_vpshuf :
  wsize -> (GRing.ComRing.sort -> coq_Z -> GRing.ComRing.sort) ->
  GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPSHUFHW :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPSHUFLW :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPSHUFD :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val wshufps_128 :
  GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  GRing.ComRing.sort

val x86_VSHUFPS :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  (error, GRing.ComRing.sort) result

val x86_VPUNPCKH :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPUNPCKL :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val wpblendw :
  GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  GRing.ComRing.sort

val x86_VPBLEND :
  Equality.sort -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  GRing.ComRing.sort -> sem_tuple exec

val x86_VPBLENDVB :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  sem_tuple exec

val coq_SaturatedSignedToUnsigned :
  wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort

val coq_SaturatedSignedToSigned :
  wsize -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort

val vpack2 :
  wsize -> wsize -> wsize -> (GRing.ComRing.sort -> GRing.ComRing.sort) ->
  GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort

val x86_VPACKUS :
  Equality.sort -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  sem_tuple exec

val x86_VPACKSS :
  Equality.sort -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  sem_tuple exec

val x86_VPBROADCAST : wsize -> wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_VMOVSHDUP : wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_VMOVSLDUP : wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_VEXTRACTI128 :
  GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VINSERTI128 :
  GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
  exec

val x86_VPERM2I128 :
  GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple
  exec

val x86_VPERMD : GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPERMQ : GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPALIGNR128 :
  GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  GRing.ComRing.sort

val x86_VPALIGNR :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  sem_tuple exec

val x86_VPMOVMSKB : wsize -> wsize -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPCMPEQ :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPCMPGT :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPMADDUBSW :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPMADDWD :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VMOVLPD : GRing.ComRing.sort -> sem_tuple exec

val x86_VMOVHPD : GRing.ComRing.sort -> sem_tuple exec

val x86_VPMINU :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPMINS :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPMAXU :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPMAXS :
  velem -> wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_VPTEST :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_AESDEC : GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_AESDECLAST :
  GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_AESENC : GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_AESENCLAST :
  GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val x86_AESIMC : GRing.ComRing.sort -> sem_tuple exec

val x86_AESKEYGENASSIST :
  GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val wclmulq : GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort

val wVPCLMULDQD :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  GRing.ComRing.sort

val x86_VPCLMULQDQ :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  sem_tuple exec

val implicit_flags :
  (register, register_ext, xmm_register, rflag, condt) Arch_decl.arg_desc list

val implicit_flags_noCF :
  (register, register_ext, xmm_register, rflag, condt) Arch_decl.arg_desc list

val iCF :
  (register, register_ext, xmm_register, rflag, condt) Arch_decl.arg_desc

val reg_msb_flag : wsize -> msb_flag

val max_32 : wsize -> wsize

val map_sz :
  wsize -> (register, register_ext, xmm_register, rflag, condt) asm_args ->
  (wsize * (register, register_ext, xmm_register, rflag, condt) asm_arg) list

val pp_name :
  char list -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  asm_args -> (register, register_ext, xmm_register, rflag, condt) pp_asm_op

val pp_name_ty :
  char list -> wsize list -> (register, register_ext, xmm_register, rflag,
  condt) asm_arg list -> (register, register_ext, xmm_register, rflag, condt)
  pp_asm_op

val pp_iname :
  char list -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  asm_args -> (register, register_ext, xmm_register, rflag, condt) pp_asm_op

val pp_viname_long :
  char list -> velem -> wsize -> (register, register_ext, xmm_register,
  rflag, condt) asm_args -> (register, register_ext, xmm_register, rflag,
  condt) pp_asm_op

val pp_viname :
  char list -> velem -> wsize -> (register, register_ext, xmm_register,
  rflag, condt) asm_args -> (register, register_ext, xmm_register, rflag,
  condt) pp_asm_op

val pp_iname_w_8 :
  char list -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  asm_arg list -> (register, register_ext, xmm_register, rflag, condt)
  pp_asm_op

val pp_iname_ww_8 :
  char list -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  asm_arg list -> (register, register_ext, xmm_register, rflag, condt)
  pp_asm_op

val get_ct :
  (register, register_ext, xmm_register, rflag, condt) asm_arg list ->
  (register, register_ext, xmm_register, rflag, condt)
  pp_asm_op_ext * (register, register_ext, xmm_register, rflag, condt)
  asm_arg list

val pp_ct :
  char list -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  asm_arg list -> (register, register_ext, xmm_register, rflag, condt)
  pp_asm_op

val pp_cqo :
  wsize -> (register, register_ext, xmm_register, rflag, condt) asm_args ->
  (register, register_ext, xmm_register, rflag, condt) pp_asm_op

val c : arg_kind list

val r : arg_kind list

val rx : arg_kind list

val m : bool -> arg_kind list

val i : wsize -> arg_kind list

val rm : bool -> arg_kind list

val rmi : wsize -> arg_kind list

val ri : wsize -> arg_kind list

val m_r : arg_kind list list

val r_rm_false : arg_kind list list

val r_rm : arg_kind list list

val r_rmi : wsize -> arg_kind list list

val m_ri : wsize -> arg_kind list list

val xmm : arg_kind list

val xmmm : bool -> arg_kind list

val xmm_xmmm : arg_kind list list

val xmmm_xmm : arg_kind list list

val xmm_xmm_xmmm : arg_kind list list

val check_mov : wsize -> arg_kind list list list

val coq_Ox86_MOV_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_movx : wsize -> arg_kind list list list

val pp_movd :
  char list -> Equality.sort -> (register, register_ext, xmm_register, rflag,
  condt) asm_arg list -> (register, register_ext, xmm_register, rflag, condt)
  pp_asm_op

val coq_Ox86_MOVX_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_movsx : wsize -> wsize -> arg_kind list list list

val pp_movsx :
  Equality.sort -> Equality.sort -> (register, register_ext, xmm_register,
  rflag, condt) asm_arg list -> (register, register_ext, xmm_register, rflag,
  condt) pp_asm_op

val coq_Ox86_MOVSX_instr :
  (wsize -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val pp_movzx :
  wsize -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  asm_arg list -> (register, register_ext, xmm_register, rflag, condt)
  pp_asm_op

val coq_Ox86_MOVZX_instr :
  (wsize -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_xchg : arg_kind list list list

val coq_Ox86_XCHG_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val c_r_rm : arg_kind list list

val coq_Ox86_CMOVcc_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_add : wsize -> arg_kind list list list

val coq_Ox86_ADD_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_SUB_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_mul : wsize -> arg_kind list list list

val coq_Ox86_MUL_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_IMUL_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_IMULr_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_IMULri_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_DIV_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_IDIV_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_CQO_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_ADC_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_SBB_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_adcx : wsize -> arg_kind list list list

val coq_Ox86_ADCX_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_ADOX_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_mulx : arg_kind list list list

val coq_Ox86_MULX_lo_hi_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_neg : wsize -> arg_kind list list list

val coq_Ox86_NEG_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_INC_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_DEC_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_LZCNT_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_setcc : arg_kind list list list

val coq_Ox86_SETcc_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val check_bt : wsize -> arg_kind list list list

val coq_Ox86_BT_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_CLC_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_STC_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val check_lea : wsize -> arg_kind list list list

val coq_Ox86_LEA_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_test : wsize -> arg_kind list list list

val coq_Ox86_TEST_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_cmp : wsize -> arg_kind list list list

val coq_Ox86_CMP_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_AND_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_OR_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_XOR_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_andn : wsize -> arg_kind list list list

val coq_Ox86_ANDN_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_NOT_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_ror : wsize -> arg_kind list list list

val coq_Ox86_ROR_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_ROL_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_RCR_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_RCL_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_SHL_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_SHR_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_SAL_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_SAR_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_shld : wsize -> arg_kind list list list

val safe_shxd : wsize -> safe_cond list

val coq_Ox86_SHLD_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_SHRD_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_BSWAP_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_POPCNT_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_PEXT_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_PDEP_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_movd : wsize -> arg_kind list list list

val coq_Ox86_MOVD_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_MOVV_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VMOV_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_vmovdq : wsize -> arg_kind list list list

val coq_Ox86_VMOVDQA_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VMOVDQU_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val pp_vpmovx :
  char list -> velem -> wsize -> velem -> wsize -> (register, register_ext,
  xmm_register, rflag, condt) asm_arg list -> (register, register_ext,
  xmm_register, rflag, condt) pp_asm_op

val coq_Ox86_VPMOVSX_instr :
  (velem -> wsize -> velem -> wsize -> (register, register_ext, xmm_register,
  rflag, condt) instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPMOVZX_instr :
  (velem -> wsize -> velem -> wsize -> (register, register_ext, xmm_register,
  rflag, condt) instr_desc_t) * (char list * x86_op prim_constructor)

val check_xmm_xmm_xmmm : wsize -> arg_kind list list list

val coq_Ox86_VPAND_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPANDN_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPOR_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPXOR_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPADD_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPSUB_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPAVG_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPMULL_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPMUL_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPMULU_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPMULH_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPMULHU_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPMULHRS_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_vpextr : wsize -> arg_kind list list list

val pp_viname_t :
  char list -> velem -> wsize list -> (register, register_ext, xmm_register,
  rflag, condt) asm_arg list -> (register, register_ext, xmm_register, rflag,
  condt) pp_asm_op

val coq_Ox86_VPEXTR_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val pp_vpinsr :
  velem -> (register, register_ext, xmm_register, rflag, condt) asm_arg list
  -> (register, register_ext, xmm_register, rflag, condt) pp_asm_op

val check_vpinsr : wsize -> arg_kind list list list

val coq_Ox86_VPINSR_instr :
  (velem -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_xmm_xmm_imm8 : wsize -> arg_kind list list list

val coq_Ox86_VPSLL_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPSRL_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPSRA_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPSLLV_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPSRLV_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPSLLDQ_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPSRLDQ_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPSHUFB_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_xmm_xmmm_imm8 : wsize -> arg_kind list list list

val coq_Ox86_VPSHUFHW_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPSHUFLW_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPSHUFD_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPUNPCKH_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPUNPCKL_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_xmm_xmm_xmmm_imm8 : wsize -> arg_kind list list list

val coq_Ox86_VPBLEND_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_xmm_xmm_xmmm_xmm : wsize -> arg_kind list list list

val coq_Ox86_VPBLENDVB_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPACKUS_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPACKSS_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VSHUFPS_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val pp_vpbroadcast :
  velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  asm_arg list -> (register, register_ext, xmm_register, rflag, condt)
  pp_asm_op

val check_xmm_xmmm : wsize -> arg_kind list list list

val coq_Ox86_VPBROADCAST_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VMOVSHDUP_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VMOVSLDUP_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPALIGNR_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VBROADCASTI128_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val check_xmmm_xmm_imm8 : wsize -> arg_kind list list list

val coq_Ox86_VEXTRACTI128_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_VINSERTI128_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_VPERM2I128_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_VPERMD_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_VPERMQ_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_PMOVMSKB_instr :
  (wsize -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPCMPEQ_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPCMPGT_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPMADDUBSW_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPMADDWD_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_movpd : arg_kind list list list

val coq_Ox86_VMOVLPD_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_VMOVHPD_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_VPMINS_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPMINU_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPMAXS_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_VPMAXU_instr :
  (velem -> wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val check_vptest : wsize -> arg_kind list list list

val coq_Ox86_VPTEST_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_RDTSC_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_RDTSCP_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val coq_Ox86_CLFLUSH_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_LFENCE_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_MFENCE_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_SFENCE_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val mk_instr_aes2 :
  char list -> char list -> x86_op -> sem_tuple exec sem_prod -> msb_flag ->
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val mk_instr_aes3 :
  char list -> char list -> x86_op -> sem_tuple exec sem_prod -> msb_flag ->
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_AESDEC_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_VAESDEC_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_AESDECLAST_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_VAESDECLAST_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_AESENC_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_VAESENC_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_AESENCLAST_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_VAESENCLAST_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_AESIMC_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_VAESIMC_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_AESKEYGENASSIST_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_VAESKEYGENASSIST_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_PCLMULQDQ_instr :
  (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t * (char list * x86_op prim_constructor)

val coq_Ox86_VPCLMULQDQ_instr :
  (wsize -> (register, register_ext, xmm_register, rflag, condt)
  instr_desc_t) * (char list * x86_op prim_constructor)

val x86_instr_desc :
  x86_op -> (register, register_ext, xmm_register, rflag, condt) instr_desc_t

val x86_prim_string : (char list * x86_op prim_constructor) list

val eqC_x86_op : x86_op eqTypeC

val x86_op_decl :
  (register, register_ext, xmm_register, rflag, condt, x86_op) asm_op_decl

type x86_prog =
  (register, register_ext, xmm_register, rflag, condt, x86_op) asm_prog
