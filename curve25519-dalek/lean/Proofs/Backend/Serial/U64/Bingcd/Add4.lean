module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Addc
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- `Limbs.addc` on four limbs, unfolded. -/
private theorem addc_four (a0 a1 a2 a3 b0 b1 b2 b3 : Word 64) (c : Bool) :
    Limbs.addc #v[a0, a1, a2, a3] #v[b0, b1, b2, b3] c =
      (#v[(Word.addc a0 b0 c).1,
          (Word.addc a1 b1 (Word.addc a0 b0 c).2).1,
          (Word.addc a2 b2 (Word.addc a1 b1 (Word.addc a0 b0 c).2).2).1,
          (Word.addc a3 b3 (Word.addc a2 b2 (Word.addc a1 b1 (Word.addc a0 b0 c).2).2).2).1],
        (Word.addc a3 b3 (Word.addc a2 b2 (Word.addc a1 b1 (Word.addc a0 b0 c).2).2).2).2) :=
  rfl

@[step]
theorem add4_spec (a b : Array U64 4#usize) :
    add4 a b ⦃ r => L4 r = Limbs.add (L4 a) (L4 b) ⦄ := by
  unfold add4
  step*
  simp only [L4_make]
  simp [L4, Limbs.add, addc_four, *]

end Curve25519Dalek.backend.serial.u64.bingcd
