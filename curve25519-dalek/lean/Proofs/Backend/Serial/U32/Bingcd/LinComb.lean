module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.SmulAdd2
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- `Limbs.linComb` on eight limbs, unfolded. -/
private theorem linComb_eight (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 f g : Word 32) :
    Limbs.linComb #v[a0, a1, a2, a3, a4, a5, a6, a7] #v[b0, b1, b2, b3, b4, b5, b6, b7] f g =
      (#v[(Word.smulAdd2 a0 b0 f g 0).1,
          (Word.smulAdd2 a1 b1 f g (Word.smulAdd2 a0 b0 f g 0).2).1,
          (Word.smulAdd2 a2 b2 f g (Word.smulAdd2 a1 b1 f g (Word.smulAdd2 a0 b0 f g 0).2).2).1,
          (Word.smulAdd2 a3 b3 f g (Word.smulAdd2 a2 b2 f g (Word.smulAdd2 a1 b1 f g
            (Word.smulAdd2 a0 b0 f g 0).2).2).2).1,
          (Word.smulAdd2 a4 b4 f g (Word.smulAdd2 a3 b3 f g (Word.smulAdd2 a2 b2 f g
            (Word.smulAdd2 a1 b1 f g (Word.smulAdd2 a0 b0 f g 0).2).2).2).2).1,
          (Word.smulAdd2 a5 b5 f g (Word.smulAdd2 a4 b4 f g (Word.smulAdd2 a3 b3 f g
            (Word.smulAdd2 a2 b2 f g (Word.smulAdd2 a1 b1 f g (Word.smulAdd2 a0 b0 f g
            0).2).2).2).2).2).1,
          (Word.smulAdd2 a6 b6 f g (Word.smulAdd2 a5 b5 f g (Word.smulAdd2 a4 b4 f g
            (Word.smulAdd2 a3 b3 f g (Word.smulAdd2 a2 b2 f g (Word.smulAdd2 a1 b1 f g
            (Word.smulAdd2 a0 b0 f g 0).2).2).2).2).2).2).1,
          (Word.smulAdd2 a7 b7 f g (Word.smulAdd2 a6 b6 f g (Word.smulAdd2 a5 b5 f g
            (Word.smulAdd2 a4 b4 f g (Word.smulAdd2 a3 b3 f g (Word.smulAdd2 a2 b2 f g
            (Word.smulAdd2 a1 b1 f g (Word.smulAdd2 a0 b0 f g 0).2).2).2).2).2).2).2).1],
        (Word.smulAdd2 a7 b7 f g (Word.smulAdd2 a6 b6 f g (Word.smulAdd2 a5 b5 f g (Word.smulAdd2
          a4 b4 f g (Word.smulAdd2 a3 b3 f g (Word.smulAdd2 a2 b2 f g (Word.smulAdd2 a1 b1 f g
          (Word.smulAdd2 a0 b0 f g 0).2).2).2).2).2).2).2).2) :=
  rfl

@[step]
theorem lin_comb_spec (a b : Array U32 8#usize) (f g : U32) :
    lin_comb a b f g ⦃ (r : Array U32 8#usize) (c : U32) =>
      L8 r = (Limbs.linComb (L8 a) (L8 b) f.bv g.bv).1 ∧
        c.bv = (Limbs.linComb (L8 a) (L8 b) f.bv g.bv).2 ⦄ := by
  unfold lin_comb
  step*
  simp only [L8_make]
  simp [L8, linComb_eight, *]

end Curve25519Dalek.backend.serial.u32.bingcd
