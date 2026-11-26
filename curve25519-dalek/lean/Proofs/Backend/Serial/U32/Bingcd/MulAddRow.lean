module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.MulAdd2
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- `Limbs.mulAddRow` on eight limbs, unfolded. -/
private theorem mulAddRow_eight (c0 c1 c2 c3 c4 c5 c6 c7 a0 a1 a2 a3 a4 a5 a6 a7 b c : Word 32) :
    Limbs.mulAddRow #v[c0, c1, c2, c3, c4, c5, c6, c7] #v[a0, a1, a2, a3, a4, a5, a6, a7] b c =
      (#v[(Word.mulAdd2 a0 b c0 c).1,
          (Word.mulAdd2 a1 b c1 (Word.mulAdd2 a0 b c0 c).2).1,
          (Word.mulAdd2 a2 b c2 (Word.mulAdd2 a1 b c1 (Word.mulAdd2 a0 b c0 c).2).2).1,
          (Word.mulAdd2 a3 b c3 (Word.mulAdd2 a2 b c2 (Word.mulAdd2 a1 b c1 (Word.mulAdd2 a0 b c0
            c).2).2).2).1,
          (Word.mulAdd2 a4 b c4 (Word.mulAdd2 a3 b c3 (Word.mulAdd2 a2 b c2 (Word.mulAdd2 a1 b c1
            (Word.mulAdd2 a0 b c0 c).2).2).2).2).1,
          (Word.mulAdd2 a5 b c5 (Word.mulAdd2 a4 b c4 (Word.mulAdd2 a3 b c3 (Word.mulAdd2 a2 b c2
            (Word.mulAdd2 a1 b c1 (Word.mulAdd2 a0 b c0 c).2).2).2).2).2).1,
          (Word.mulAdd2 a6 b c6 (Word.mulAdd2 a5 b c5 (Word.mulAdd2 a4 b c4 (Word.mulAdd2 a3 b c3
            (Word.mulAdd2 a2 b c2 (Word.mulAdd2 a1 b c1 (Word.mulAdd2 a0 b c0
            c).2).2).2).2).2).2).1,
          (Word.mulAdd2 a7 b c7 (Word.mulAdd2 a6 b c6 (Word.mulAdd2 a5 b c5 (Word.mulAdd2 a4 b c4
            (Word.mulAdd2 a3 b c3 (Word.mulAdd2 a2 b c2 (Word.mulAdd2 a1 b c1 (Word.mulAdd2 a0 b
            c0 c).2).2).2).2).2).2).2).1],
        (Word.mulAdd2 a7 b c7 (Word.mulAdd2 a6 b c6 (Word.mulAdd2 a5 b c5 (Word.mulAdd2 a4 b c4
          (Word.mulAdd2 a3 b c3 (Word.mulAdd2 a2 b c2 (Word.mulAdd2 a1 b c1 (Word.mulAdd2 a0 b c0
          c).2).2).2).2).2).2).2).2) :=
  rfl

@[step]
theorem mul_add_row_spec (acc a : Array U32 8#usize) (b c : U32) :
    mul_add_row acc a b c ⦃ (r : Array U32 8#usize) (hi : U32) =>
      L8 r = (Limbs.mulAddRow (L8 acc) (L8 a) b.bv c.bv).1 ∧
        hi.bv = (Limbs.mulAddRow (L8 acc) (L8 a) b.bv c.bv).2 ⦄ := by
  unfold mul_add_row
  step*
  simp only [L8_make]
  simp [L8, mulAddRow_eight, *]

end Curve25519Dalek.backend.serial.u32.bingcd
