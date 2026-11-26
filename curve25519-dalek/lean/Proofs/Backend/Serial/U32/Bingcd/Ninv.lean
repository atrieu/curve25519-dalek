module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- The constant `NINV` is `-1 / p` modulo `2 ^ 32`. -/
theorem NINV_bv : UScalar.bv NINV = Limbs.Curve25519.U32.ninv := by
  have h : Limbs.Curve25519.U32.ninv = 678152731#32 := by decide +kernel
  rw [h]
  unfold NINV
  rfl

end Curve25519Dalek.backend.serial.u32.bingcd
