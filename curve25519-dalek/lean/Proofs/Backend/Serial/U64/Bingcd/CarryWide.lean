module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Mask51
import Proofs.Helpers.Array
import Proofs.Helpers.Limbs
public section

open Aeneas Aeneas.Std Result
open Bingcd curve25519

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- The value after the carry chain: each carry moves to the next limb, and the last one comes
back multiplied by `19 = 2^255 - p`, so `p` is subtracted once per unit of that carry. -/
private theorem carry_asNat {c0 c1 c2 c3 c4 C1 C2 C3 C4 R0 : ℕ} (h1 : C1 = c1 + c0 / 2 ^ 51)
    (h2 : C2 = c2 + C1 / 2 ^ 51) (h3 : C3 = c3 + C2 / 2 ^ 51) (h4 : C4 = c4 + C3 / 2 ^ 51)
    (hr : R0 = c0 % 2 ^ 51 + 19 * (C4 / 2 ^ 51)) :
    R0 % 2 ^ 51 + 2 ^ 51 * (C1 % 2 ^ 51 + R0 / 2 ^ 51) + 2 ^ 102 * (C2 % 2 ^ 51) +
        2 ^ 153 * (C3 % 2 ^ 51) + 2 ^ 204 * (C4 % 2 ^ 51) + p * (C4 / 2 ^ 51) =
      c0 + 2 ^ 51 * c1 + 2 ^ 102 * c2 + 2 ^ 153 * c3 + 2 ^ 204 * c4 := by
  have eR := Nat.div_add_mod R0 (2 ^ 51)
  have e0 := Nat.div_add_mod c0 (2 ^ 51)
  have e1 := Nat.div_add_mod C1 (2 ^ 51)
  have e2 := Nat.div_add_mod C2 (2 ^ 51)
  have e3 := Nat.div_add_mod C3 (2 ^ 51)
  have e4 := Nat.div_add_mod C4 (2 ^ 51)
  have hp := p_add_nineteen
  zify at *
  linear_combination eR + hr + (C4 / 2 ^ 51 : ℤ) * hp + 2 ^ 204 * e4 + 2 ^ 204 * h4 +
    2 ^ 153 * e3 + 2 ^ 153 * h3 + 2 ^ 102 * e2 + 2 ^ 102 * h2 + 2 ^ 51 * e1 + 2 ^ 51 * h1 + e0

/-- The carry chain on five limbs below `2^98`: the result represents the same value modulo
`p`, with limbs below `2^52`. -/
@[step]
theorem carry_wide_spec (c0 c1 c2 c3 c4 : U128) (h0 : c0.val < 2 ^ 98) (h1 : c1.val < 2 ^ 98)
    (h2 : c2.val < 2 ^ 98) (h3 : c3.val < 2 ^ 98) (h4 : c4.val < 2 ^ 98) :
    carry_wide c0 c1 c2 c3 c4 ⦃ (r : field.FieldElement51) =>
      r.asNat % p = (c0.val + 2 ^ 51 * c1.val + 2 ^ 102 * c2.val + 2 ^ 153 * c3.val +
        2 ^ 204 * c4.val) % p ∧ r.LimbsLt 52 ⦄ := by
  unfold carry_wide
  step*
  all_goals
    have hcast : ∀ x : U128, x.val < 2 ^ 64 →
        (UScalar.cast UScalarTy.U128 (UScalar.cast UScalarTy.U64 x)).val = x.val := by
      intro x hx
      rw [UScalar.cast_val_eq, UScalar.cast_val_eq]
      change x.val % 2 ^ 64 % 2 ^ 128 = x.val
      omega
    have hmask : ∀ x y : U64, y.bv = x.bv &&& i14.bv → y.val = x.val % 2 ^ 51 := by
      intro x y h
      have h' := congrArg BitVec.toNat h
      simp only [U64.bv, i14_post, Limbs.Curve25519.toNat_and_mask51, UScalar.bv_toNat] at h'
      exact h'
    have hlow : ∀ (x : U128) (z y : U64), z = UScalar.cast UScalarTy.U64 x →
        y.bv = z.bv &&& i14.bv → y.val = x.val % 2 ^ 51 := by
      intro x z y hz h
      have h' := hmask z y h
      have hn : UScalarTy.U64.numBits = 64 := rfl
      rw [hz, UScalar.cast_val_eq, hn] at h'
      omega
    have hi : i.val = c0.val / 2 ^ 51 := by rw [i_post, Nat.shiftRight_eq_div_pow]
    have hC1 : c11.val = c1.val + c0.val / 2 ^ 51 := by
      rw [c11_post, i2_post, i1_post, hcast i (by omega), hi]
    have hi3 : i3.val = c11.val / 2 ^ 51 := by rw [i3_post, Nat.shiftRight_eq_div_pow]
    have hC2 : c21.val = c2.val + c11.val / 2 ^ 51 := by
      rw [c21_post, i5_post, i4_post, hcast i3 (by omega), hi3]
    have hi6 : i6.val = c21.val / 2 ^ 51 := by rw [i6_post, Nat.shiftRight_eq_div_pow]
    have hC3 : c31.val = c3.val + c21.val / 2 ^ 51 := by
      rw [c31_post, i8_post, i7_post, hcast i6 (by omega), hi6]
    have hi9 : i9.val = c31.val / 2 ^ 51 := by rw [i9_post, Nat.shiftRight_eq_div_pow]
    have hC4 : c41.val = c4.val + c31.val / 2 ^ 51 := by
      rw [c41_post, i11_post, i10_post, hcast i9 (by omega), hi9]
    have hcarry : carry.val = c41.val / 2 ^ 51 := by
      rw [carry_post, UScalar.cast_val_eq, i12_post, Nat.shiftRight_eq_div_pow]
      change c41.val / 2 ^ 51 % 2 ^ 64 = c41.val / 2 ^ 51
      omega
    have h15 : i15.val = c0.val % 2 ^ 51 := hlow c0 i13 i15 i13_post i15_post1
  · -- the limb `0` with the carry times `19` fits in a word
    scalar_tac
  all_goals
    have hr0 : r0.val = c0.val % 2 ^ 51 + 19 * (c41.val / 2 ^ 51) := by
      rw [r0_post, i16_post, h15, hcarry, Nat.mul_comm]
    have h19 : i19.val = c11.val % 2 ^ 51 := hlow c11 i18 i19 i18_post i19_post1
    have h20 : i20.val = r0.val / 2 ^ 51 := by rw [i20_post, Nat.shiftRight_eq_div_pow]
  · scalar_tac
  · have h17 : i17.val = r0.val % 2 ^ 51 := hmask r0 i17 i17_post1
    have h21 : i21.val = c11.val % 2 ^ 51 + r0.val / 2 ^ 51 := by rw [i21_post, h19, h20]
    have h23 : i23.val = c21.val % 2 ^ 51 := hlow c21 i22 i23 i22_post i23_post1
    have h25 : i25.val = c31.val % 2 ^ 51 := hlow c31 i24 i25 i24_post i25_post1
    have h27 : i27.val = c41.val % 2 ^ 51 := hlow c41 i26 i27 i26_post i27_post1
    have hsum := carry_asNat hC1 hC2 hC3 hC4 hr0
    refine ⟨?_, ?_⟩
    · rw [← hsum, Nat.add_mul_mod_self_left, field.FieldElement51.asNat_eq]
      simp only [Array.getElem!_make, List.getElem!_cons_zero, List.getElem!_cons_succ, h17, h21,
        h23, h25, h27]
    · intro j hj
      interval_cases j <;>
        simp only [Array.getElem!_make, List.getElem!_cons_zero, List.getElem!_cons_succ, h17,
          h21, h23, h25, h27] <;> omega

end Curve25519Dalek.backend.serial.u64.bingcd
