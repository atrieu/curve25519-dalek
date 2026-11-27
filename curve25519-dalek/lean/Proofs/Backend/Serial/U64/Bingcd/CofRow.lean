module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.CarryWide
import Proofs.Backend.Serial.U64.Bingcd.CofLimb
import Proofs.Backend.Serial.U64.Bingcd.Select
import Proofs.Helpers.Limbs
public section

open Aeneas Aeneas.Std Result
open Bingcd curve25519

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- A limb of a field element with limbs below `2^52`, as `index_usize` returns it. -/
private theorem limb_lt {u : field.FieldElement51} (hu : u.LimbsLt 52) (j : ℕ) (hj : j < 5) :
    (u.val[j]'(by scalar_tac)).val < 2 ^ 52 := by
  have h := hu j hj
  rwa [Array.getElem!_Nat_eq, getElem!_pos u.val j (by scalar_tac)] at h

private theorem limb_eq (u : field.FieldElement51) (j : ℕ) (hj : j < 5) :
    ((u.val[j]'(by scalar_tac)).val : ℤ) = u[j]!.val := by
  rw [Array.getElem!_Nat_eq, getElem!_pos u.val j (by scalar_tac)]

/-- **A row of the transition matrix applied to the cofactors**, without division: the result
represents `u * f + v * g` in the field, negated when `neg` is set, with limbs below `2^52`. -/
@[step]
theorem cof_row_spec (u v : field.FieldElement51) (f g : U64) (neg : Bool)
    (hu : u.LimbsLt 52) (hv : v.LimbsLt 52) (hf : |f.bv.toInt| ≤ 2 ^ 43)
    (hg : |g.bv.toInt| ≤ 2 ^ 43) :
    cof_row u v f g neg ⦃ (r : field.FieldElement51) =>
      r.toField = Pornin.cofR u.toField v.toField f.bv g.bv neg ∧ r.LimbsLt 52 ⦄ := by
  unfold cof_row
  have hu0 := limb_lt hu 0 (by norm_num)
  have hu1 := limb_lt hu 1 (by norm_num)
  have hu2 := limb_lt hu 2 (by norm_num)
  have hu3 := limb_lt hu 3 (by norm_num)
  have hu4 := limb_lt hu 4 (by norm_num)
  have hv0 := limb_lt hv 0 (by norm_num)
  have hv1 := limb_lt hv 1 (by norm_num)
  have hv2 := limb_lt hv 2 (by norm_num)
  have hv3 := limb_lt hv 3 (by norm_num)
  have hv4 := limb_lt hv 4 (by norm_num)
  have hP0 : P46_0.val = 158456325028527338180948525056 := by
    unfold P46_0
    rfl
  have hPI : P46_I.val = 158456325028528604818343723008 := by
    unfold P46_I
    rfl
  have hP0a : 2 ^ 96 ≤ P46_0.val := by rw [hP0]; norm_num
  have hP0b : P46_0.val < 2 ^ 97 := by rw [hP0]; norm_num
  have hPIa : 2 ^ 96 ≤ P46_I.val := by rw [hPI]; norm_num
  have hPIb : P46_I.val < 2 ^ 97 := by rw [hPI]; norm_num
  step as ⟨i, hi⟩
  step as ⟨f1, hf1⟩
  step as ⟨i1, hi1⟩
  step as ⟨g1, hg1⟩
  have h0 : UScalar.bv 0#u64 = 0#64 := rfl
  have hF : f1.bv.toInt = bif neg then -f.bv.toInt else f.bv.toInt := by
    have h : f1.bv = Word.select neg (-f.bv) f.bv := by
      simp only [hf1, hi, core.num.U64.wrapping_sub_bv_eq, h0, U64.bv, BitVec.zero_sub]
    rw [h]
    exact Pornin.toInt_select_neg (K := 43) (by norm_num) hf neg
  have hG : g1.bv.toInt = bif neg then -g.bv.toInt else g.bv.toInt := by
    have h : g1.bv = Word.select neg (-g.bv) g.bv := by
      simp only [hg1, hi1, core.num.U64.wrapping_sub_bv_eq, h0, U64.bv, BitVec.zero_sub]
    rw [h]
    exact Pornin.toInt_select_neg (K := 43) (by norm_num) hg neg
  have hF' : |f1.bv.toInt| ≤ 2 ^ 43 := by
    rw [hF]
    cases neg <;> simpa using hf
  have hG' : |g1.bv.toInt| ≤ 2 ^ 43 := by
    rw [hG]
    cases neg <;> simpa using hg
  step*
  refine ⟨?_, r_post1⟩
  -- the limbs sum to `2^46 * p + u * f + v * g`
  have hsum : ((i4.val + 2 ^ 51 * i7.val + 2 ^ 102 * i10.val + 2 ^ 153 * i13.val +
      2 ^ 204 * i16.val : ℕ) : ℤ) =
      2 ^ 46 * p + u.asNat * f1.bv.toInt + v.asNat * g1.bv.toInt := by
    push_cast
    rw [i4_post, i7_post, i10_post, i13_post, i16_post, i2_post, i3_post, i5_post, i6_post,
      i8_post, i9_post, i11_post, i12_post, i14_post, i15_post, limb_eq u 0 (by norm_num),
      limb_eq u 1 (by norm_num), limb_eq u 2 (by norm_num), limb_eq u 3 (by norm_num),
      limb_eq u 4 (by norm_num), limb_eq v 0 (by norm_num), limb_eq v 1 (by norm_num),
      limb_eq v 2 (by norm_num), limb_eq v 3 (by norm_num), limb_eq v 4 (by norm_num),
      field.FieldElement51.asNat_eq u, field.FieldElement51.asNat_eq v, hP0, hPI, p_eq_numeral]
    push_cast
    ring
  have hr : (r.asNat : ZMod p) = u.toField * (f1.bv.toInt : ZMod p) +
      v.toField * (g1.bv.toInt : ZMod p) := by
    rw [(ZMod.natCast_eq_natCast_iff' _ _ _).mpr r_post, ← Int.cast_natCast, hsum,
      field.FieldElement51.toField_def, field.FieldElement51.toField_def]
    push_cast
    rw [ZMod.natCast_self]
    ring
  rw [field.FieldElement51.toField_def r, hr, hF, hG, Pornin.cofR]
  cases neg <;> simp
  ring

end Curve25519Dalek.backend.serial.u64.bingcd
