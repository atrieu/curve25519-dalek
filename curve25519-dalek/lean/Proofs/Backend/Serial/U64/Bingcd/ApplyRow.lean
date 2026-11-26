module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.LinComb
import Proofs.Backend.Serial.U64.Bingcd.ShrAbs
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

@[step]
theorem apply_row_spec (a b : Array U64 4#usize) (f g : U64) :
    apply_row a b f g ⦃ (x : Array U64 4#usize) (neg : Bool) =>
      L4 x = (Pornin.applyRow (L4 a) (L4 b) f.bv g.bv 31).1 ∧
        neg = (Pornin.applyRow (L4 a) (L4 b) f.bv g.bv 31).2 ⦄ := by
  unfold apply_row
  step*
  simp [Pornin.applyRow, *]

end Curve25519Dalek.backend.serial.u64.bingcd
