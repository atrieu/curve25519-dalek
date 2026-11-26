module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.LinComb
import Proofs.Backend.Serial.U32.Bingcd.ShrAbs
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

@[step]
theorem apply_row_spec (a b : Array U32 8#usize) (f g : U32) :
    apply_row a b f g ⦃ (x : Array U32 8#usize) (neg : Bool) =>
      L8 x = (Pornin.applyRow (L8 a) (L8 b) f.bv g.bv 15).1 ∧
        neg = (Pornin.applyRow (L8 a) (L8 b) f.bv g.bv 15).2 ⦄ := by
  unfold apply_row
  step*
  simp [Pornin.applyRow, *]

end Curve25519Dalek.backend.serial.u32.bingcd
