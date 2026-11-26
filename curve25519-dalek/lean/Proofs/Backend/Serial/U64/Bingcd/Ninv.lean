module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- The constant `NINV` is `-1 / p` modulo `2 ^ 64`. -/
theorem NINV_bv : UScalar.bv NINV = Limbs.Curve25519.ninv := by
  have h : Limbs.Curve25519.ninv = 9708812670373448219#64 := by decide +kernel
  rw [h]
  unfold NINV
  rfl

end Curve25519Dalek.backend.serial.u64.bingcd
