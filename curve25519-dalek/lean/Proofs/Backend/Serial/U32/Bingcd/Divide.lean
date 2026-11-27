module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.Scale
import Proofs.Backend.Serial.U32.Bingcd.ScaledDiv
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result
open Bingcd
open Curve25519Dalek.SharedAFieldElement2625.Insts
  (CoreOpsArithMulSharedBFieldElement2625FieldElement2625.mul_spec)

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- **The translated field division** is the run of `scaled_div` from the cofactor
`x * 2 ^ -508`. -/
@[step]
theorem divide_spec (x : field.FieldElement2625) (z : Array U32 10#usize)
    (hx : ∀ i : ℕ, i < 10 → x[i]!.val < 3 * 2 ^ 26) :
    divide x z ⦃ (r : field.FieldElement2625) =>
      r.toField = Pornin.porninDivR 15 32 28 Limbs.Curve25519.U32.P (x.toField * SCALE.toField)
        (Limbs.Curve25519.U32.freeze (L10 z)) ∧ r.LimbsLt 26 ⦄ := by
  unfold divide
  have hS : ∀ i : ℕ, i < 10 → SCALE[i]!.val < 3 * 2 ^ 26 :=
    fun j hj => lt_trans (SCALE_limbsLt j hj) (by norm_num)
  step with CoreOpsArithMulSharedBFieldElement2625FieldElement2625.mul_spec x SCALE hx hS
    as ⟨fe, hfe, hfeb⟩
  step with scaled_div_spec fe z hfeb as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, field.FieldElement2625.toField_mul_of_mod hfe], hrb⟩

/-- **Correctness of `bingcd::divide`.** For `x` with limbs below `3 * 2 ^ 26` and `z` with limbs
within the bounds of the weak reduction (below `2 ^ 26` at even positions and below
`2 ^ 25 + 2 ^ 18` at odd ones), the function never panics, its result has limbs below `2 ^ 26`,
and it represents the quotient in the field of integers modulo `p` of the elements its
arguments represent (with a quotient by zero being zero). -/
theorem divide_correct (x z : field.FieldElement2625)
    (hx : ∀ i : ℕ, i < 10 → x[i]!.val < 3 * 2 ^ 26)
    (hz : ∀ i : ℕ, i < 10 → z[i]!.val < field.FieldElement2625.limbRadix i + i % 2 * 2 ^ 18) :
    divide x z ⦃ (r : field.FieldElement2625) =>
      r.toField = x.toField / z.toField ∧ r.LimbsLt 26 ⦄ := by
  refine WP.spec_mono (divide_spec x z hx) fun r ⟨hr, hb⟩ => ⟨?_, hb⟩
  rw [hr, Limbs.Curve25519.U32.porninDivR_freeze (tight_L10 hz), mul_assoc, SCALE_toField,
    mul_one, value_L10, ← field.FieldElement2625.toField_def]

end Curve25519Dalek.backend.serial.u32.bingcd
