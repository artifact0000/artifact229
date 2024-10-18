open Memory_example
open Memory_model
open Wsize

module Memory :
 sig
  type mem = MemoryI.mem

  val coq_CM : coq_PointerData -> mem coreMem

  val coq_M : coq_PointerData -> mem memory
 end
