module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- The constant `P` is the modulus `2 ^ 255 - 19` on eight limbs. -/
theorem L8_P : L8 P = Limbs.Curve25519.U32.P := by
  unfold P
  rfl

end Curve25519Dalek.backend.serial.u32.bingcd
