module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

@[step]
theorem subb_spec (a b : U64) (c : Bool) :
    subb a b c ⦃ (s : U64) (k : Bool) =>
      s.bv = (Word.subb a.bv b.bv c).1 ∧ k = (Word.subb a.bv b.bv c).2 ⦄ := by
  unfold subb
  step*
  have ha : a.val < 2 ^ 64 := by scalar_tac
  have hb : b.val < 2 ^ 64 := by scalar_tac
  have hc : c.toNat ≤ 1 := by cases c <;> simp
  have hi : i.val = a.val := by simp [i_post]
  have h1 : i1.val = b.val := by simp [i1_post]
  have hsize : UScalar.size .U128 = 2 ^ 128 := by simp [U128.size, U128.numBits]
  -- the difference on 128 bits: `a - b - c` if there is no borrow, `2 ^ 128 + a - b - c` otherwise
  have h2 : i2.val = (a.val + (2 ^ 128 - b.val)) % 2 ^ 128 := by
    rw [i2_post, core.num.U128.wrapping_sub_val_eq, hi, h1, hsize]
  have hz : z.val = (a.val + 2 ^ 128 - (b.val + c.toNat)) % 2 ^ 128 := by
    rw [z_post, core.num.U128.wrapping_sub_val_eq, h2, i3_post, hsize]
    omega
  have h4v : i4.val = z.val % 2 ^ 64 := by simp [i4_post]
  have h4 : i4.bv = BitVec.ofNat 64 (a.val + 2 ^ 64 - (b.val + c.toNat)) := by
    apply BitVec.eq_of_toNat_eq
    rw [U64.bv_toNat, h4v, hz, BitVec.toNat_ofNat]
    omega
  have h5 : (i5 != 0#u128) = decide (a.val < b.val + c.toNat) := by
    rw [bne, Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq,
      U128.eq_zero_iff_val, i5_post, Nat.shiftRight_eq_div_pow, hz]
    omega
  simp only [Word.subb, U64.bv_toNat, h4, h5, and_self]

end Curve25519Dalek.backend.serial.u64.bingcd
