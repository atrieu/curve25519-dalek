module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Freeze
import Proofs.Backend.Serial.U64.Bingcd.Ninv
import Proofs.Backend.Serial.U64.Bingcd.P
import Proofs.Backend.Serial.U64.Bingcd.PorninDiv
import Proofs.Backend.Serial.U64.Bingcd.Rounds
import Proofs.Backend.Serial.U64.Bingcd.Unpack
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- **The translated field division**: canonical forms, Pornin's division on four 64-bit limbs
with 15 rounds and 43 last steps, and five 51-bit limbs again. On limbs of at most
`2 ^ 51 + 2 ^ 23` this is `Limbs.Curve25519.div` (`divide_eq_div`). -/
@[step]
theorem divide_spec (x z : Array U64 5#usize) :
    divide x z ⦃ r => L5 r = Limbs.Curve25519.unpack
      (Pornin.porninDivSL 31 15 43 Limbs.Curve25519.P Limbs.Curve25519.ninv
        (Limbs.Curve25519.freeze (L5 x)) (Limbs.Curve25519.freeze (L5 z))) ⦄ := by
  unfold divide
  step*
  simp only [r_post, a2_post, a1_post, a_post, L4_P, NINV_bv, ROUNDS_val, U64.bv]

/-- On limbs of at most `2 ^ 51 + 2 ^ 23`, the translated field division is
`Limbs.Curve25519.div`. -/
theorem divide_eq_div (x z : Array U64 5#usize) (hx : Limbs.Curve25519.Tight (L5 x))
    (hz : Limbs.Curve25519.Tight (L5 z)) :
    divide x z ⦃ r => L5 r = Limbs.Curve25519.div (L5 x) (L5 z) ⦄ := by
  refine WP.spec_mono (divide_spec x z) fun r hr => ?_
  rw [hr, Limbs.Curve25519.div_eq_porninDivSL hx hz]

/-- **Correctness of `bingcd::divide`.** On limbs of at most `2 ^ 51 + 2 ^ 23`, the function
never panics, its result has limbs below `2 ^ 51`, and it represents the quotient in the field
of integers modulo `p` of the elements its arguments represent (with a quotient by zero being
zero). -/
theorem divide_correct (x z : field.FieldElement51)
    (hx : ∀ i : ℕ, i < 5 → x[i]!.val ≤ 2 ^ 51 + 2 ^ 23)
    (hz : ∀ i : ℕ, i < 5 → z[i]!.val ≤ 2 ^ 51 + 2 ^ 23) :
    divide x z ⦃ (r : field.FieldElement51) =>
      r.toField = x.toField / z.toField ∧ r.LimbsLt 51 ⦄ := by
  refine WP.spec_mono (divide_eq_div x z (tight_L5 hx) (tight_L5 hz)) fun r hr => ?_
  obtain ⟨hb, hv⟩ := Limbs.Curve25519.div_spec (tight_L5 hx) (tight_L5 hz)
  rw [← hr] at hb hv
  rw [value_L5, value_L5, value_L5] at hv
  rw [field.FieldElement51.toField_def r, field.FieldElement51.toField_def x,
    field.FieldElement51.toField_def z]
  exact ⟨hv, limbsLt_of_bounded hb⟩

end Curve25519Dalek.backend.serial.u64.bingcd
