module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- `Limbs.eq` on eight limbs, unfolded: the or of the xors is zero. -/
private theorem eq_eight (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Word 32) :
    Limbs.eq #v[a0, a1, a2, a3, a4, a5, a6, a7] #v[b0, b1, b2, b3, b4, b5, b6, b7] =
      ((a0 ^^^ b0) ||| (a1 ^^^ b1) ||| (a2 ^^^ b2) ||| (a3 ^^^ b3) ||| (a4 ^^^ b4) |||
        (a5 ^^^ b5) ||| (a6 ^^^ b6) ||| (a7 ^^^ b7) == 0#32) := by
  have h : Limbs.xorOrAll #v[a0, a1, a2, a3, a4, a5, a6, a7] #v[b0, b1, b2, b3, b4, b5, b6, b7] =
      0#32 ||| (a0 ^^^ b0) ||| (a1 ^^^ b1) ||| (a2 ^^^ b2) ||| (a3 ^^^ b3) ||| (a4 ^^^ b4) |||
        (a5 ^^^ b5) ||| (a6 ^^^ b6) ||| (a7 ^^^ b7) := rfl
  rw [Limbs.eq, h, BitVec.zero_or]

@[step]
theorem eq8_spec (a b : Array U32 8#usize) :
    eq8 a b ⦃ r => r = Limbs.eq (L8 a) (L8 b) ⦄ := by
  unfold eq8
  step*
  have hx : decide (x = 0#u32) = (x.bv == 0#32) := by
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, beq_iff_eq, U32.eq_iff_bv]
    rfl
  subst i_post i1_post i3_post i4_post i7_post i8_post i11_post i12_post i15_post i16_post
    i19_post i20_post i23_post i24_post i27_post i28_post
  rw [hx, L8, L8, eq_eight]
  simp only [U32.bv, x_post1, i2_post1, i5_post1, i6_post1, i9_post1, i10_post1, i13_post1,
    i14_post1, i17_post1, i18_post1, i21_post1, i22_post1, i25_post1, i26_post1, i29_post1]

end Curve25519Dalek.backend.serial.u32.bingcd
