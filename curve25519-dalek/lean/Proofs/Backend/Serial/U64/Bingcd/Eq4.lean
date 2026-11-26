module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- `Limbs.eq` on four limbs, unfolded: the or of the xors is zero. -/
private theorem eq_four (a0 a1 a2 a3 b0 b1 b2 b3 : Word 64) :
    Limbs.eq #v[a0, a1, a2, a3] #v[b0, b1, b2, b3] =
      ((a0 ^^^ b0) ||| (a1 ^^^ b1) ||| (a2 ^^^ b2) ||| (a3 ^^^ b3) == 0#64) := by
  have h : Limbs.xorOrAll #v[a0, a1, a2, a3] #v[b0, b1, b2, b3] =
      0#64 ||| (a0 ^^^ b0) ||| (a1 ^^^ b1) ||| (a2 ^^^ b2) ||| (a3 ^^^ b3) := rfl
  rw [Limbs.eq, h, BitVec.zero_or]

@[step]
theorem eq4_spec (a b : Array U64 4#usize) :
    eq4 a b ⦃ r => r = Limbs.eq (L4 a) (L4 b) ⦄ := by
  unfold eq4
  step*
  have hx : decide (x = 0#u64) = (x.bv == 0#64) := by
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, beq_iff_eq, U64.eq_iff_bv]
    rfl
  subst i_post i1_post i3_post i4_post i7_post i8_post i11_post i12_post
  rw [hx, L4, L4, eq_four]
  simp only [U64.bv, x_post1, i10_post1, i6_post1, i2_post1, i5_post1, i9_post1, i13_post1]

end Curve25519Dalek.backend.serial.u64.bingcd
