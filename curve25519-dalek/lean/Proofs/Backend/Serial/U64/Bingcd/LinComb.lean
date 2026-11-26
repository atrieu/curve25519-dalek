module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.SmulAdd2
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- `Limbs.linComb` on four limbs, unfolded. -/
private theorem linComb_four (a0 a1 a2 a3 b0 b1 b2 b3 f g : Word 64) :
    Limbs.linComb #v[a0, a1, a2, a3] #v[b0, b1, b2, b3] f g =
      (#v[(Word.smulAdd2 a0 b0 f g 0).1,
          (Word.smulAdd2 a1 b1 f g (Word.smulAdd2 a0 b0 f g 0).2).1,
          (Word.smulAdd2 a2 b2 f g
            (Word.smulAdd2 a1 b1 f g (Word.smulAdd2 a0 b0 f g 0).2).2).1,
          (Word.smulAdd2 a3 b3 f g
            (Word.smulAdd2 a2 b2 f g
              (Word.smulAdd2 a1 b1 f g (Word.smulAdd2 a0 b0 f g 0).2).2).2).1],
        (Word.smulAdd2 a3 b3 f g
          (Word.smulAdd2 a2 b2 f g
            (Word.smulAdd2 a1 b1 f g (Word.smulAdd2 a0 b0 f g 0).2).2).2).2) := rfl

@[step]
theorem lin_comb_spec (a b : Array U64 4#usize) (f g : U64) :
    lin_comb a b f g ⦃ (r : Array U64 4#usize) (c : U64) =>
      L4 r = (Limbs.linComb (L4 a) (L4 b) f.bv g.bv).1 ∧
        c.bv = (Limbs.linComb (L4 a) (L4 b) f.bv g.bv).2 ⦄ := by
  unfold lin_comb
  step*
  simp only [L4_make]
  simp [L4, linComb_four, *]

end Curve25519Dalek.backend.serial.u64.bingcd
