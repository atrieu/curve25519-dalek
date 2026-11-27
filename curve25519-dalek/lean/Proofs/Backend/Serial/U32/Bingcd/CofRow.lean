module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.CofLimb
import Proofs.Backend.Serial.U32.Bingcd.Select
import Proofs.Backend.Serial.U32.Field.Reduce
import Proofs.Helpers.FieldElement2625
public section

open Aeneas Aeneas.Std Result
open Bingcd curve25519
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 (getElem!_make_le)

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- A limb of a field element with limbs below `2^26`, as `index_usize` returns it. -/
private theorem limb_lt {u : field.FieldElement2625} (hu : u.LimbsLt 26) (j : ℕ) (hj : j < 10) :
    (u.val[j]'(by scalar_tac)).val < 2 ^ 26 := by
  have h := hu j hj
  rwa [Array.getElem!_Nat_eq, getElem!_pos u.val j (by scalar_tac)] at h

private theorem limb_eq (u : field.FieldElement2625) (j : ℕ) (hj : j < 10) :
    ((u.val[j]'(by scalar_tac)).val : ℤ) = u[j]!.val := by
  rw [Array.getElem!_Nat_eq, getElem!_pos u.val j (by scalar_tac)]

/-- **A row of the transition matrix applied to the cofactors**, without division: the result
represents `u * f + v * g` in the field, negated when `neg` is set, with limbs below `2^26`. -/
@[step]
theorem cof_row_spec (u v : field.FieldElement2625) (f g : U32) (neg : Bool)
    (hu : u.LimbsLt 26) (hv : v.LimbsLt 26) (hf : |f.bv.toInt| ≤ 2 ^ 28)
    (hg : |g.bv.toInt| ≤ 2 ^ 28) :
    cof_row u v f g neg ⦃ (r : field.FieldElement2625) =>
      r.toField = Pornin.cofR u.toField v.toField f.bv g.bv neg ∧ r.LimbsLt 26 ⦄ := by
  unfold cof_row
  have hu0 := limb_lt hu 0 (by norm_num)
  have hu1 := limb_lt hu 1 (by norm_num)
  have hu2 := limb_lt hu 2 (by norm_num)
  have hu3 := limb_lt hu 3 (by norm_num)
  have hu4 := limb_lt hu 4 (by norm_num)
  have hu5 := limb_lt hu 5 (by norm_num)
  have hu6 := limb_lt hu 6 (by norm_num)
  have hu7 := limb_lt hu 7 (by norm_num)
  have hu8 := limb_lt hu 8 (by norm_num)
  have hu9 := limb_lt hu 9 (by norm_num)
  have hv0 := limb_lt hv 0 (by norm_num)
  have hv1 := limb_lt hv 1 (by norm_num)
  have hv2 := limb_lt hv 2 (by norm_num)
  have hv3 := limb_lt hv 3 (by norm_num)
  have hv4 := limb_lt hv 4 (by norm_num)
  have hv5 := limb_lt hv 5 (by norm_num)
  have hv6 := limb_lt hv 6 (by norm_num)
  have hv7 := limb_lt hv 7 (by norm_num)
  have hv8 := limb_lt hv 8 (by norm_num)
  have hv9 := limb_lt hv 9 (by norm_num)
  have hP0 : P31_0.val = 144115147273666560 := by
    unfold P31_0
    rfl
  have hPO : P31_ODD.val = 72057591890444288 := by
    unfold P31_ODD
    rfl
  have hPE : P31_EVEN.val = 144115185928372224 := by
    unfold P31_EVEN
    rfl
  have hP0a : 2 ^ 55 ≤ P31_0.val := by rw [hP0]; norm_num
  have hP0b : P31_0.val < 2 ^ 57 := by rw [hP0]; norm_num
  have hPOa : 2 ^ 55 ≤ P31_ODD.val := by rw [hPO]; norm_num
  have hPOb : P31_ODD.val < 2 ^ 57 := by rw [hPO]; norm_num
  have hPEa : 2 ^ 55 ≤ P31_EVEN.val := by rw [hPE]; norm_num
  have hPEb : P31_EVEN.val < 2 ^ 57 := by rw [hPE]; norm_num
  step as ⟨i, hi⟩
  step as ⟨f1, hf1⟩
  step as ⟨i1, hi1⟩
  step as ⟨g1, hg1⟩
  have h0 : UScalar.bv 0#u32 = 0#32 := rfl
  have hF : f1.bv.toInt = bif neg then -f.bv.toInt else f.bv.toInt := by
    have h : f1.bv = Word.select neg (-f.bv) f.bv := by
      simp only [hf1, hi, core.num.U32.wrapping_sub_bv_eq, h0, U32.bv, BitVec.zero_sub]
    rw [h]
    exact Pornin.toInt_select_neg (K := 28) (by norm_num) hf neg
  have hG : g1.bv.toInt = bif neg then -g.bv.toInt else g.bv.toInt := by
    have h : g1.bv = Word.select neg (-g.bv) g.bv := by
      simp only [hg1, hi1, core.num.U32.wrapping_sub_bv_eq, h0, U32.bv, BitVec.zero_sub]
    rw [h]
    exact Pornin.toInt_select_neg (K := 28) (by norm_num) hg neg
  have hF' : |f1.bv.toInt| ≤ 2 ^ 28 := by
    rw [hF]
    cases neg <;> simpa using hf
  have hG' : |g1.bv.toInt| ≤ 2 ^ 28 := by
    rw [hG]
    cases neg <;> simpa using hg
  step*
  · -- the limbs are within the range of `reduce`
    exact getElem!_make_le _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨?_, r_post1⟩
  rw [Array.asNat2625_make] at r_post
  -- the limbs sum to `2^31 * p + u * f + v * g`
  have hsum : ((i4.val + 2 ^ 26 * i7.val + 2 ^ 51 * i10.val + 2 ^ 77 * i13.val +
      2 ^ 102 * i16.val + 2 ^ 128 * i19.val + 2 ^ 153 * i22.val + 2 ^ 179 * i25.val +
      2 ^ 204 * i28.val + 2 ^ 230 * i31.val : ℕ) : ℤ) =
      2 ^ 31 * p + u.asNat * f1.bv.toInt + v.asNat * g1.bv.toInt := by
    push_cast
    rw [i4_post, i7_post, i10_post, i13_post, i16_post, i19_post, i22_post, i25_post, i28_post,
      i31_post, i2_post, i5_post, i8_post, i11_post, i14_post, i17_post, i20_post, i23_post,
      i26_post, i29_post, i3_post, i6_post, i9_post, i12_post, i15_post, i18_post, i21_post,
      i24_post, i27_post, i30_post, limb_eq u 0 (by norm_num), limb_eq u 1 (by norm_num),
      limb_eq u 2 (by norm_num), limb_eq u 3 (by norm_num), limb_eq u 4 (by norm_num),
      limb_eq u 5 (by norm_num), limb_eq u 6 (by norm_num), limb_eq u 7 (by norm_num),
      limb_eq u 8 (by norm_num), limb_eq u 9 (by norm_num), limb_eq v 0 (by norm_num),
      limb_eq v 1 (by norm_num), limb_eq v 2 (by norm_num), limb_eq v 3 (by norm_num),
      limb_eq v 4 (by norm_num), limb_eq v 5 (by norm_num), limb_eq v 6 (by norm_num),
      limb_eq v 7 (by norm_num), limb_eq v 8 (by norm_num), limb_eq v 9 (by norm_num),
      field.FieldElement2625.asNat_expand u, field.FieldElement2625.asNat_expand v, hP0, hPO, hPE,
      p_eq_numeral]
    push_cast
    ring
  have hr : (r.asNat : ZMod p) = u.toField * (f1.bv.toInt : ZMod p) +
      v.toField * (g1.bv.toInt : ZMod p) := by
    rw [(ZMod.natCast_eq_natCast_iff' _ _ _).mpr r_post, ← Int.cast_natCast, hsum,
      field.FieldElement2625.toField_def, field.FieldElement2625.toField_def]
    push_cast
    rw [ZMod.natCast_self]
    ring
  rw [field.FieldElement2625.toField_def r, hr, hF, hG, Pornin.cofR]
  cases neg <;> simp
  ring

end Curve25519Dalek.backend.serial.u32.bingcd
