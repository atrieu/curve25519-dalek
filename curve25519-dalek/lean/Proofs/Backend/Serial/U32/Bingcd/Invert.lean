module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.Freeze
import Proofs.Backend.Serial.U32.Bingcd.Ninv
import Proofs.Backend.Serial.U32.Bingcd.P
import Proofs.Backend.Serial.U32.Bingcd.PorninInv
import Proofs.Backend.Serial.U32.Bingcd.Rounds
import Proofs.Backend.Serial.U32.Bingcd.Unpack
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- **The translated field inversion**: canonical form, Pornin's inversion on eight 32-bit limbs
with 32 rounds and 28 last steps, and ten limbs again. On limbs within the bounds of the weak
reduction this is `Limbs.Curve25519.U32.inv` (`invert_eq_inv`). -/
@[step]
theorem invert_spec (z : Array U32 10#usize) :
    invert z ⦃ r => L10 r = Limbs.Curve25519.U32.unpack
      (Pornin.porninInvSL 15 32 28 Limbs.Curve25519.U32.P Limbs.Curve25519.U32.ninv
        (Limbs.Curve25519.U32.freeze (L10 z))) ⦄ := by
  unfold invert
  step*
  simp only [r_post, a1_post, a_post, L8_P, NINV_bv, ROUNDS_val, U32.bv]

/-- On tight limbs, the translated field inversion is `Limbs.Curve25519.U32.inv`: its 32
rounds and 28 last steps compute the same limbs as the 34 rounds of `inv`. -/
theorem invert_eq_inv (z : Array U32 10#usize) (hz : Limbs.Curve25519.U32.Tight (L10 z)) :
    invert z ⦃ r => L10 r = Limbs.Curve25519.U32.inv (L10 z) ⦄ := by
  refine WP.spec_mono (invert_spec z) fun r hr => ?_
  rw [hr, Limbs.Curve25519.U32.inv_eq_porninInvSL hz]

/-- **Correctness of `bingcd::invert`.** On ten limbs within the bounds of the weak reduction
(below `2 ^ 26` at even positions and below `2 ^ 25 + 2 ^ 18` at odd ones), the function never
panics, its result has limbs below `2 ^ 26`, and it represents the inverse in the field of
integers modulo `p` of the element its argument represents (with the inverse of zero being
zero). -/
theorem invert_correct (z : field.FieldElement2625)
    (hz : ∀ i : ℕ, i < 10 → z[i]!.val < field.FieldElement2625.limbRadix i + i % 2 * 2 ^ 18) :
    invert z ⦃ (r : field.FieldElement2625) => r.toField = z.toField⁻¹ ∧ r.LimbsLt 26 ⦄ := by
  refine WP.spec_mono (invert_eq_inv z (tight_L10 hz)) fun r hr => ?_
  obtain ⟨hb, hv⟩ := Limbs.Curve25519.U32.inv_spec (tight_L10 hz)
  rw [← hr] at hb hv
  rw [value_L10, value_L10] at hv
  rw [field.FieldElement2625.toField_def r, field.FieldElement2625.toField_def z]
  exact ⟨hv, limbsLt_of_reduced hb⟩

end Curve25519Dalek.backend.serial.u32.bingcd
