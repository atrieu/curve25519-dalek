module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

@[step]
theorem addc_spec (a b : U64) (c : Bool) :
    addc a b c ⦃ (s : U64) (k : Bool) =>
      s.bv = (Word.addc a.bv b.bv c).1 ∧ k = (Word.addc a.bv b.bv c).2 ⦄ := by
  unfold addc
  step*
  · have hi : i.val = a.val := by simp [i_post]
    have h1 : i1.val = b.val := by simp [i1_post]
    have hc : c.toNat ≤ 1 := by cases c <;> decide
    scalar_tac
  · have hs : s.val = a.val + b.val + c.toNat := by simp [*]
    have h4 : i4.bv = BitVec.ofNat 64 (a.val + b.val + c.toNat) := by
      apply BitVec.eq_of_toNat_eq
      simp [i4_post, hs]
    have h5 : (i5 != 0#u128) = decide (2 ^ 64 ≤ a.val + b.val + c.toNat) := by
      rw [← hs, bne, Bool.eq_iff_iff]
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq,
        U128.eq_zero_iff_val, i5_post, Nat.shiftRight_eq_div_pow]
      omega
    simp only [Word.addc, U64.bv_toNat, h4, h5, and_self]

end Curve25519Dalek.backend.serial.u64.bingcd
