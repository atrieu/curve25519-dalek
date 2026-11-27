module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- The constant `P` is the modulus `2 ^ 255 - 19` on four limbs. -/
theorem L4_P : L4 P = Limbs.Curve25519.P := by
  have h : Limbs.Curve25519.P =
      #v[18446744073709551597#64, 18446744073709551615#64, 18446744073709551615#64,
        9223372036854775807#64] := by decide
  rw [h]
  unfold P
  rfl

end Curve25519Dalek.backend.serial.u64.bingcd
