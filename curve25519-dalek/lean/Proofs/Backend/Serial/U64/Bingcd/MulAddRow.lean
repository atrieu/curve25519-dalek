module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.MulAdd2
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- `Limbs.mulAddRow` on four limbs, unfolded. -/
private theorem mulAddRow_four (c0 c1 c2 c3 a0 a1 a2 a3 b c : Word 64) :
    Limbs.mulAddRow #v[c0, c1, c2, c3] #v[a0, a1, a2, a3] b c =
      (#v[(Word.mulAdd2 a0 b c0 c).1,
          (Word.mulAdd2 a1 b c1 (Word.mulAdd2 a0 b c0 c).2).1,
          (Word.mulAdd2 a2 b c2 (Word.mulAdd2 a1 b c1 (Word.mulAdd2 a0 b c0 c).2).2).1,
          (Word.mulAdd2 a3 b c3
            (Word.mulAdd2 a2 b c2 (Word.mulAdd2 a1 b c1 (Word.mulAdd2 a0 b c0 c).2).2).2).1],
        (Word.mulAdd2 a3 b c3
          (Word.mulAdd2 a2 b c2 (Word.mulAdd2 a1 b c1 (Word.mulAdd2 a0 b c0 c).2).2).2).2) :=
  rfl

@[step]
theorem mul_add_row_spec (acc a : Array U64 4#usize) (b c : U64) :
    mul_add_row acc a b c ⦃ (r : Array U64 4#usize) (hi : U64) =>
      L4 r = (Limbs.mulAddRow (L4 acc) (L4 a) b.bv c.bv).1 ∧
        hi.bv = (Limbs.mulAddRow (L4 acc) (L4 a) b.bv c.bv).2 ⦄ := by
  unfold mul_add_row
  step*
  simp only [L4_make]
  simp [L4, mulAddRow_four, *]

end Curve25519Dalek.backend.serial.u64.bingcd
