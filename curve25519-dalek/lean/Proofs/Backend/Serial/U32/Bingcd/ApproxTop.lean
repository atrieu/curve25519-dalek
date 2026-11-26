module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.K
import Proofs.Backend.Serial.U32.Bingcd.Select
import Proofs.Backend.Serial.U32.Bingcd.TopTwo
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

private theorem leading_zeros_val (x : U32) :
    (core.num.U32.leading_zeros x).val = 32 - x.val.size := by
  have hx : x.val < 2 ^ 32 := by scalar_tac
  have hs : x.val.size ≤ 32 := Nat.size_le.mpr hx
  simp only [core.num.U32.leading_zeros, Aeneas.Std.BitVec.leadingZeros]
  by_cases hz : x.bv = 0
  · simp [hz, UScalar.val]
  · have hx0 : x.val ≠ 0 := by
      intro h
      exact hz (BitVec.eq_of_toNat_eq (by simpa using h))
    have hsz : x.val.size = Nat.log 2 x.val + 1 := by
      rw [size_eq_bitLen, bitLen, ite_eq_right hx0, Nat.log2_eq_log_two]
    have hlog : Nat.log 2 x.val < 32 := by omega
    simp only [hz, ↓reduceIte]
    change (BitVec.ofNat 32 (32 - Nat.log 2 x.bv.toNat - 1)).toNat = _
    rw [BitVec.toNat_ofNat, U32.bv_toNat, hsz]
    omega

/-- The value selected by `select`. -/
private theorem select_val {c : Bool} {a b r : U32} (h : r.bv = Word.select c a.bv b.bv) :
    r.val = if c then a.val else b.val := by
  rw [Word.select_eq] at h
  cases c
  · simpa using congrArg BitVec.toNat h
  · simpa using congrArg BitVec.toNat h

/-- The shift count of `approx_top`: the number of leading zeros of the top limb, and zero when
there is none. -/
private theorem shift_count {tm c : U32}
    (h : c.bv = Word.select (decide (tm = 0#u32)) (U32.bv 0#u32)
      (core.num.U32.leading_zeros tm).bv) :
    c.val = if tm.val = 0 then 0 else 32 - tm.val.size := by
  have hlz := leading_zeros_val tm
  have h2 := select_val h
  have e0 : (0#u32).val = 0 := rfl
  rw [h2]
  simp only [decide_eq_true_eq, U32.eq_zero_iff_val, hlz, e0]

/-- **The approximation read from the top limb is `Pornin.approxTop`.** -/
@[step]
theorem approx_top_spec (m a : Array U32 8#usize) :
    approx_top m a ⦃ r => r.bv = Pornin.approxTop 15 (L8 m) (L8 a) ⦄ := by
  unfold approx_top
  step*
  · -- the left shift: the count is at most 31
    have hc := shift_count (tm := tm) (c := c) (by rw [c_post, i_post])
    rw [hc]
    split_ifs with h0
    · norm_num
    · have := Nat.size_pos.mpr (Nat.pos_of_ne_zero h0)
      omega
  · have hc := shift_count (tm := tm) (c := c) (by rw [c_post, i_post])
    have e : (31#u32).val = 31 := rfl
    rw [hc, e]
    split_ifs with h0
    · norm_num
    · have := Nat.size_pos.mpr (Nat.pos_of_ne_zero h0)
      omega
  · have hc := shift_count (tm := tm) (c := c) (by rw [c_post, i_post])
    have hz : UScalar.bv tm = 0 ↔ tm.val = 0 := by
      have h := U32.bv_beq_zero tm
      rwa [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq] at h
    have hcbv : (if UScalar.bv tm = 0 then 0 else 32 - (UScalar.bv tm).toNat.size) = c.val := by
      rw [hc, U32.bv_toNat]
      simp only [hz]
    have h8 : i8.val = 15 := by rw [i8_post, i7_post, K_val]
    have h11 : i11.val = 2 ^ 15 := by simp [i11_post, U32.size, U32.numBits]
    have h12 : UScalar.bv i12 = BitVec.ofNat 32 (2 ^ 15 - 1) := by
      apply BitVec.eq_of_toNat_eq
      simp [i12_post, h11]
    -- the right shift by `32 - c`, written as two shifts
    have h5 : UScalar.bv i5 = UScalar.bv lo >>> (32 - c.val) := by
      simp only [i5_post1, i3_post1, i4_post, U32.bv]
      rw [← BitVec.shiftRight_add]
      congr 1
      omega
    have h1 : UScalar.bv i1 = (L8 a)[0] := by
      rw [i1_post]
      rfl
    simp only [Pornin.approxTop, ← tm_post, ← hi_post, ← hi_post1, hcbv,
      core.num.U32.wrapping_add_bv_eq, i10_post1, i9_post1, i13_post1, win_post, i6_post1,
      i2_post1, h5, h8, h12, h1, K_val, U32.decide_eq_zero, U32.bv, Nat.reduceSub]

end Curve25519Dalek.backend.serial.u32.bingcd
