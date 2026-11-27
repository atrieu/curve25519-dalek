module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Scale
import Proofs.Backend.Serial.U64.Bingcd.ScaledDiv
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- **The translated field inversion** is the run of `scaled_div` from the cofactor `2 ^ -508`. -/
@[step]
theorem invert_spec (z : Array U64 5#usize) :
    invert z ⦃ (r : field.FieldElement51) =>
      r.toField = Pornin.porninDivR 31 15 43 Limbs.Curve25519.P SCALE.toField
        (Limbs.Curve25519.freeze (L5 z)) ∧ r.LimbsLt 52 ⦄ := by
  unfold invert
  step with scaled_div_spec SCALE z (fun j hj => lt_trans (SCALE_limbsLt j hj) (by norm_num))
    as ⟨r, hr, hrb⟩
  exact ⟨hr, hrb⟩

/-- **Correctness of `bingcd::invert`.** On five limbs of at most `2 ^ 51 + 2 ^ 23`, the
function never panics, its result has limbs below `2 ^ 52`, and it represents the inverse in
the field of integers modulo `p` of the element its argument represents (with the inverse of
zero being zero). -/
theorem invert_correct (z : field.FieldElement51)
    (hz : ∀ i : ℕ, i < 5 → z[i]!.val ≤ 2 ^ 51 + 2 ^ 23) :
    invert z ⦃ (r : field.FieldElement51) => r.toField = z.toField⁻¹ ∧ r.LimbsLt 52 ⦄ := by
  refine WP.spec_mono (invert_spec z) fun r ⟨hr, hb⟩ => ⟨?_, hb⟩
  rw [hr, Limbs.Curve25519.porninDivR_freeze (tight_L5 hz), SCALE_toField, value_L5,
    ← field.FieldElement51.toField_def, one_div]

end Curve25519Dalek.backend.serial.u64.bingcd
