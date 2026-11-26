module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.Addc
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- `Limbs.addc` on eight limbs, unfolded. -/
private theorem addc_eight (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Word 32) (c : Bool) :
    Limbs.addc #v[a0, a1, a2, a3, a4, a5, a6, a7] #v[b0, b1, b2, b3, b4, b5, b6, b7] c =
      (#v[(Word.addc a0 b0 c).1,
          (Word.addc a1 b1 (Word.addc a0 b0 c).2).1,
          (Word.addc a2 b2 (Word.addc a1 b1 (Word.addc a0 b0 c).2).2).1,
          (Word.addc a3 b3 (Word.addc a2 b2 (Word.addc a1 b1 (Word.addc a0 b0 c).2).2).2).1,
          (Word.addc a4 b4 (Word.addc a3 b3 (Word.addc a2 b2 (Word.addc a1 b1 (Word.addc a0 b0
            c).2).2).2).2).1,
          (Word.addc a5 b5 (Word.addc a4 b4 (Word.addc a3 b3 (Word.addc a2 b2 (Word.addc a1 b1
            (Word.addc a0 b0 c).2).2).2).2).2).1,
          (Word.addc a6 b6 (Word.addc a5 b5 (Word.addc a4 b4 (Word.addc a3 b3 (Word.addc a2 b2
            (Word.addc a1 b1 (Word.addc a0 b0 c).2).2).2).2).2).2).1,
          (Word.addc a7 b7 (Word.addc a6 b6 (Word.addc a5 b5 (Word.addc a4 b4 (Word.addc a3 b3
            (Word.addc a2 b2 (Word.addc a1 b1 (Word.addc a0 b0 c).2).2).2).2).2).2).2).1],
        (Word.addc a7 b7 (Word.addc a6 b6 (Word.addc a5 b5 (Word.addc a4 b4 (Word.addc a3 b3
          (Word.addc a2 b2 (Word.addc a1 b1 (Word.addc a0 b0 c).2).2).2).2).2).2).2).2) :=
  rfl

@[step]
theorem add8_spec (a b : Array U32 8#usize) :
    add8 a b ⦃ r => L8 r = Limbs.add (L8 a) (L8 b) ⦄ := by
  unfold add8
  step*
  simp only [L8_make]
  simp [L8, Limbs.add, addc_eight, *]

end Curve25519Dalek.backend.serial.u32.bingcd
