module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Subb
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- `Limbs.subb` on four limbs, unfolded. -/
private theorem subb_four (a0 a1 a2 a3 b0 b1 b2 b3 : Word 64) (c : Bool) :
    Limbs.subb #v[a0, a1, a2, a3] #v[b0, b1, b2, b3] c =
      (#v[(Word.subb a0 b0 c).1,
          (Word.subb a1 b1 (Word.subb a0 b0 c).2).1,
          (Word.subb a2 b2 (Word.subb a1 b1 (Word.subb a0 b0 c).2).2).1,
          (Word.subb a3 b3 (Word.subb a2 b2 (Word.subb a1 b1 (Word.subb a0 b0 c).2).2).2).1],
        (Word.subb a3 b3 (Word.subb a2 b2 (Word.subb a1 b1 (Word.subb a0 b0 c).2).2).2).2) :=
  rfl

@[step]
theorem sub4_spec (a b : Array U64 4#usize) :
    sub4 a b ⦃ (r : Array U64 4#usize) (k : Bool) =>
      L4 r = (Limbs.subb (L4 a) (L4 b) false).1 ∧ k = (Limbs.subb (L4 a) (L4 b) false).2 ⦄ := by
  unfold sub4
  step*
  simp only [L4_make]
  subst c0_post c1_post c2_post c3_post i_post i1_post i2_post i3_post i4_post i5_post i6_post
    i7_post
  rw [r0_post, r1_post, r2_post, r3_post, L4, L4, subb_four]
  exact ⟨rfl, rfl⟩

end Curve25519Dalek.backend.serial.u64.bingcd
