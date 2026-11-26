module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Freeze
import Proofs.Backend.Serial.U64.Bingcd.Ninv
import Proofs.Backend.Serial.U64.Bingcd.P
import Proofs.Backend.Serial.U64.Bingcd.PorninInv
import Proofs.Backend.Serial.U64.Bingcd.Rounds
import Proofs.Backend.Serial.U64.Bingcd.Unpack
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- **The translated field inversion**: canonical form, Pornin's inversion on four 64-bit limbs
with 15 rounds and 43 last steps, and five 51-bit limbs again. On limbs of at most
`2 ^ 51 + 2 ^ 23` this is `Limbs.Curve25519.inv` (`invert_eq_inv`). -/
@[step]
theorem invert_spec (z : Array U64 5#usize) :
    invert z ⦃ r => L5 r = Limbs.Curve25519.unpack
      (Pornin.porninInvSL 31 15 43 Limbs.Curve25519.P Limbs.Curve25519.ninv
        (Limbs.Curve25519.freeze (L5 z))) ⦄ := by
  unfold invert
  step*
  simp only [r_post, a1_post, a_post, L4_P, NINV_bv, ROUNDS_val, U64.bv]

/-- On limbs of at most `2 ^ 51 + 2 ^ 23`, the translated field inversion is
`Limbs.Curve25519.inv`: its 15 rounds and 43 last steps compute the same limbs as the 17 rounds
of `inv`. -/
theorem invert_eq_inv (z : Array U64 5#usize) (hz : Limbs.Curve25519.Tight (L5 z)) :
    invert z ⦃ r => L5 r = Limbs.Curve25519.inv (L5 z) ⦄ := by
  refine WP.spec_mono (invert_spec z) fun r hr => ?_
  rw [hr, Limbs.Curve25519.inv_eq_porninInvSL hz]

/-- **Correctness of `bingcd::invert`.** On five limbs of at most `2 ^ 51 + 2 ^ 23`, the
function never panics, its result has limbs below `2 ^ 51`, and it represents the inverse in
the field of integers modulo `p` of the element its argument represents (with the inverse of
zero being zero). -/
theorem invert_correct (z : field.FieldElement51)
    (hz : ∀ i : ℕ, i < 5 → z[i]!.val ≤ 2 ^ 51 + 2 ^ 23) :
    invert z ⦃ (r : field.FieldElement51) => r.toField = z.toField⁻¹ ∧ r.LimbsLt 51 ⦄ := by
  refine WP.spec_mono (invert_eq_inv z (tight_L5 hz)) fun r hr => ?_
  obtain ⟨hb, hv⟩ := Limbs.Curve25519.inv_spec (tight_L5 hz)
  rw [← hr] at hb hv
  rw [value_L5, value_L5] at hv
  rw [field.FieldElement51.toField_def r, field.FieldElement51.toField_def z]
  exact ⟨hv, limbsLt_of_bounded hb⟩

end Curve25519Dalek.backend.serial.u64.bingcd
