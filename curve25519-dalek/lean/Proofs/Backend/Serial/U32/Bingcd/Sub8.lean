module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.Subb
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- `Limbs.subb` on eight limbs, unfolded. -/
private theorem subb_eight (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Word 32) (c : Bool) :
    Limbs.subb #v[a0, a1, a2, a3, a4, a5, a6, a7] #v[b0, b1, b2, b3, b4, b5, b6, b7] c =
      (#v[(Word.subb a0 b0 c).1,
          (Word.subb a1 b1 (Word.subb a0 b0 c).2).1,
          (Word.subb a2 b2 (Word.subb a1 b1 (Word.subb a0 b0 c).2).2).1,
          (Word.subb a3 b3 (Word.subb a2 b2 (Word.subb a1 b1 (Word.subb a0 b0 c).2).2).2).1,
          (Word.subb a4 b4 (Word.subb a3 b3 (Word.subb a2 b2 (Word.subb a1 b1 (Word.subb a0 b0
            c).2).2).2).2).1,
          (Word.subb a5 b5 (Word.subb a4 b4 (Word.subb a3 b3 (Word.subb a2 b2 (Word.subb a1 b1
            (Word.subb a0 b0 c).2).2).2).2).2).1,
          (Word.subb a6 b6 (Word.subb a5 b5 (Word.subb a4 b4 (Word.subb a3 b3 (Word.subb a2 b2
            (Word.subb a1 b1 (Word.subb a0 b0 c).2).2).2).2).2).2).1,
          (Word.subb a7 b7 (Word.subb a6 b6 (Word.subb a5 b5 (Word.subb a4 b4 (Word.subb a3 b3
            (Word.subb a2 b2 (Word.subb a1 b1 (Word.subb a0 b0 c).2).2).2).2).2).2).2).1],
        (Word.subb a7 b7 (Word.subb a6 b6 (Word.subb a5 b5 (Word.subb a4 b4 (Word.subb a3 b3
          (Word.subb a2 b2 (Word.subb a1 b1 (Word.subb a0 b0 c).2).2).2).2).2).2).2).2) :=
  rfl

@[step]
theorem sub8_spec (a b : Array U32 8#usize) :
    sub8 a b ⦃ (r : Array U32 8#usize) (k : Bool) =>
      L8 r = (Limbs.subb (L8 a) (L8 b) false).1 ∧ k = (Limbs.subb (L8 a) (L8 b) false).2 ⦄ := by
  unfold sub8
  step*
  simp only [L8_make]
  subst c0_post c1_post c2_post c3_post c4_post c5_post c6_post c7_post i_post i1_post i2_post
    i3_post i4_post i5_post i6_post i7_post i8_post i9_post i10_post i11_post i12_post i13_post
    i14_post i15_post
  rw [r0_post, r1_post, r2_post, r3_post, r4_post, r5_post, r6_post, r7_post, L8, L8, subb_eight]
  exact ⟨rfl, rfl⟩

end Curve25519Dalek.backend.serial.u32.bingcd
