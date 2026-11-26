module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.Freeze
import Proofs.Backend.Serial.U32.Bingcd.Ninv
import Proofs.Backend.Serial.U32.Bingcd.P
import Proofs.Backend.Serial.U32.Bingcd.PorninDiv
import Proofs.Backend.Serial.U32.Bingcd.Rounds
import Proofs.Backend.Serial.U32.Bingcd.Unpack
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- **The translated field division**: canonical forms, Pornin's division on eight 32-bit limbs
with 32 rounds and 28 last steps, and ten limbs again. On limbs within the bounds of the weak
reduction this is `Limbs.Curve25519.U32.div` (`divide_eq_div`). -/
@[step]
theorem divide_spec (x z : Array U32 10#usize) :
    divide x z ⦃ r => L10 r = Limbs.Curve25519.U32.unpack
      (Pornin.porninDivSL 15 32 28 Limbs.Curve25519.U32.P Limbs.Curve25519.U32.ninv
        (Limbs.Curve25519.U32.freeze (L10 x)) (Limbs.Curve25519.U32.freeze (L10 z))) ⦄ := by
  unfold divide
  step*
  simp only [r_post, a2_post, a1_post, a_post, L8_P, NINV_bv, ROUNDS_val, U32.bv]

/-- On tight limbs, the translated field division is `Limbs.Curve25519.U32.div`. -/
theorem divide_eq_div (x z : Array U32 10#usize) (hx : Limbs.Curve25519.U32.Tight (L10 x))
    (hz : Limbs.Curve25519.U32.Tight (L10 z)) :
    divide x z ⦃ r => L10 r = Limbs.Curve25519.U32.div (L10 x) (L10 z) ⦄ := by
  refine WP.spec_mono (divide_spec x z) fun r hr => ?_
  rw [hr, Limbs.Curve25519.U32.div_eq_porninDivSL hx hz]

/-- **Correctness of `bingcd::divide`.** On limbs within the bounds of the weak reduction
(below `2 ^ 26` at even positions and below `2 ^ 25 + 2 ^ 18` at odd ones), the function never
panics, its result has limbs below `2 ^ 26`, and it represents the quotient in the field of
integers modulo `p` of the elements its arguments represent (with a quotient by zero being
zero). -/
theorem divide_correct (x z : field.FieldElement2625)
    (hx : ∀ i : ℕ, i < 10 → x[i]!.val < field.FieldElement2625.limbRadix i + i % 2 * 2 ^ 18)
    (hz : ∀ i : ℕ, i < 10 → z[i]!.val < field.FieldElement2625.limbRadix i + i % 2 * 2 ^ 18) :
    divide x z ⦃ (r : field.FieldElement2625) =>
      r.toField = x.toField / z.toField ∧ r.LimbsLt 26 ⦄ := by
  refine WP.spec_mono (divide_eq_div x z (tight_L10 hx) (tight_L10 hz)) fun r hr => ?_
  obtain ⟨hb, hv⟩ := Limbs.Curve25519.U32.div_spec (tight_L10 hx) (tight_L10 hz)
  rw [← hr] at hb hv
  rw [value_L10, value_L10, value_L10] at hv
  rw [field.FieldElement2625.toField_def r, field.FieldElement2625.toField_def x,
    field.FieldElement2625.toField_def z]
  exact ⟨hv, limbsLt_of_reduced hb⟩

end Curve25519Dalek.backend.serial.u32.bingcd
