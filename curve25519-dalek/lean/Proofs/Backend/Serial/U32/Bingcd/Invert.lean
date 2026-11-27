module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.Scale
import Proofs.Backend.Serial.U32.Bingcd.ScaledDiv
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- **The translated field inversion** is the run of `scaled_div` from the cofactor `2 ^ -508`. -/
@[step]
theorem invert_spec (z : Array U32 10#usize) :
    invert z ⦃ (r : field.FieldElement2625) =>
      r.toField = Pornin.porninDivR 15 32 28 Limbs.Curve25519.U32.P SCALE.toField
        (Limbs.Curve25519.U32.freeze (L10 z)) ∧ r.LimbsLt 26 ⦄ := by
  unfold invert
  step with scaled_div_spec SCALE z SCALE_limbsLt as ⟨r, hr, hrb⟩
  exact ⟨hr, hrb⟩

/-- **Correctness of `bingcd::invert`.** On ten limbs within the bounds of the weak reduction
(below `2 ^ 26` at even positions and below `2 ^ 25 + 2 ^ 18` at odd ones), the function never
panics, its result has limbs below `2 ^ 26`, and it represents the inverse in the field of
integers modulo `p` of the element its argument represents (with the inverse of zero being
zero). -/
theorem invert_correct (z : field.FieldElement2625)
    (hz : ∀ i : ℕ, i < 10 → z[i]!.val < field.FieldElement2625.limbRadix i + i % 2 * 2 ^ 18) :
    invert z ⦃ (r : field.FieldElement2625) => r.toField = z.toField⁻¹ ∧ r.LimbsLt 26 ⦄ := by
  refine WP.spec_mono (invert_spec z) fun r ⟨hr, hb⟩ => ⟨?_, hb⟩
  rw [hr, Limbs.Curve25519.U32.porninDivR_freeze (tight_L10 hz), SCALE_toField, value_L10,
    ← field.FieldElement2625.toField_def, one_div]

end Curve25519Dalek.backend.serial.u32.bingcd
