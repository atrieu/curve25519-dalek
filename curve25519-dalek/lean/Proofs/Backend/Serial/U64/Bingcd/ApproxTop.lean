module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.K
import Proofs.Backend.Serial.U64.Bingcd.Select
import Proofs.Backend.Serial.U64.Bingcd.TopTwo
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

private theorem leading_zeros_val (x : U64) :
    (core.num.U64.leading_zeros x).val = 64 - x.val.size := by
  have hx : x.val < 2 ^ 64 := by scalar_tac
  have hs : x.val.size ≤ 64 := Nat.size_le.mpr hx
  simp only [core.num.U64.leading_zeros, Aeneas.Std.BitVec.leadingZeros]
  by_cases hz : x.bv = 0
  · simp [hz, UScalar.val]
  · have hx0 : x.val ≠ 0 := by
      intro h
      exact hz (BitVec.eq_of_toNat_eq (by simpa using h))
    have hsz : x.val.size = Nat.log 2 x.val + 1 := by
      rw [size_eq_bitLen, bitLen, ite_eq_right hx0, Nat.log2_eq_log_two]
    have hlog : Nat.log 2 x.val < 64 := by omega
    simp only [hz, ↓reduceIte]
    change (BitVec.ofNat 32 (64 - Nat.log 2 x.bv.toNat - 1)).toNat = _
    rw [BitVec.toNat_ofNat, U64.bv_toNat, hsz]
    omega

/-- The value selected by `select`. -/
private theorem select_val {c : Bool} {a b r : U64} (h : r.bv = Word.select c a.bv b.bv) :
    r.val = if c then a.val else b.val := by
  rw [Word.select_eq] at h
  cases c
  · simpa using congrArg BitVec.toNat h
  · simpa using congrArg BitVec.toNat h

/-- The shift count of `approx_top`: the number of leading zeros of the top limb, and zero when
there is none. -/
private theorem shift_count {tm i2 : U64}
    (h : i2.bv = Word.select (decide (tm = 0#u64)) (U64.bv 0#u64)
      (UScalar.cast UScalarTy.U64 (core.num.U64.leading_zeros tm)).bv) :
    (UScalar.cast UScalarTy.U32 i2).val = if tm.val = 0 then 0 else 64 - tm.val.size := by
  have hlz := leading_zeros_val tm
  have h2 := select_val h
  have hcast : (UScalar.cast UScalarTy.U64 (core.num.U64.leading_zeros tm)).val =
      (core.num.U64.leading_zeros tm).val := by
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  have e0 : (0#u64).val = 0 := rfl
  rw [UScalar.cast_val_eq, h2]
  simp only [decide_eq_true_eq, U64.eq_zero_iff_val, hcast, hlz, e0]
  split_ifs
  · rfl
  · exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (by decide))

/-- **The approximation read from the top limb is `Pornin.approxTop`.** -/
@[step]
theorem approx_top_spec (m a : Array U64 4#usize) :
    approx_top m a ⦃ r => r.bv = Pornin.approxTop 31 (L4 m) (L4 a) ⦄ := by
  unfold approx_top
  step*
  · -- the left shift: the count is at most 63
    have hc := shift_count (tm := tm) (i2 := i2) (by rw [i2_post, i1_post, i_post])
    rw [c_post, hc]
    split_ifs with h0
    · norm_num
    · have := Nat.size_pos.mpr (Nat.pos_of_ne_zero h0)
      omega
  · have hc := shift_count (tm := tm) (i2 := i2) (by rw [i2_post, i1_post, i_post])
    have e : (63#u32).val = 63 := rfl
    rw [c_post, hc, e]
    split_ifs with h0
    · norm_num
    · have := Nat.size_pos.mpr (Nat.pos_of_ne_zero h0)
      omega
  · have hc := shift_count (tm := tm) (i2 := i2) (by rw [i2_post, i1_post, i_post])
    rw [← c_post] at hc
    have hz : UScalar.bv tm = 0 ↔ tm.val = 0 := by
      have h := U64.bv_beq_zero tm
      rwa [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq] at h
    have hcbv : (if UScalar.bv tm = 0 then 0 else 64 - (UScalar.bv tm).toNat.size) = c.val := by
      rw [hc, U64.bv_toNat]
      simp only [hz]
    have h10 : i10.val = 31 := by rw [i10_post, i9_post, K_val]
    have h13 : i13.val = 2 ^ 31 := by simp [i13_post, U64.size, U64.numBits]
    have h14 : UScalar.bv i14 = BitVec.ofNat 64 (2 ^ 31 - 1) := by
      apply BitVec.eq_of_toNat_eq
      simp [i14_post, h13]
    -- the right shift by `64 - c`, written as two shifts
    have h7 : UScalar.bv i7 = UScalar.bv lo >>> (64 - c.val) := by
      simp only [i7_post1, i5_post1, i6_post, U64.bv]
      rw [← BitVec.shiftRight_add]
      congr 1
      omega
    have h3 : UScalar.bv i3 = (L4 a)[0] := by
      rw [i3_post]
      rfl
    simp only [Pornin.approxTop, ← tm_post, ← hi_post, ← hi_post1, hcbv,
      core.num.U64.wrapping_add_bv_eq, i12_post1, i11_post1, i15_post1, win_post, i8_post1,
      i4_post1, h7, h10, h14, h3, K_val, U64.decide_eq_zero, U64.bv, Nat.reduceSub]

end Curve25519Dalek.backend.serial.u64.bingcd
