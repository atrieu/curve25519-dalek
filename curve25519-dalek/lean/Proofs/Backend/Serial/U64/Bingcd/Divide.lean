module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Scale
import Proofs.Backend.Serial.U64.Bingcd.ScaledDiv
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Helpers.ToField
public section

open Aeneas Aeneas.Std Result
open Bingcd
open Curve25519Dalek.Shared0FieldElement51.Insts
  (CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec)

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- **The translated field division** is the run of `scaled_div` from the cofactor
`x * 2 ^ -508`. -/
@[step]
theorem divide_spec (x : field.FieldElement51) (z : Array U64 5#usize) (hx : x.LimbsLt 54) :
    divide x z ⦃ (r : field.FieldElement51) =>
      r.toField = Pornin.porninDivR 31 15 43 Limbs.Curve25519.P (x.toField * SCALE.toField)
        (Limbs.Curve25519.freeze (L5 z)) ∧ r.LimbsLt 52 ⦄ := by
  unfold divide
  have hS : SCALE.LimbsLt 54 := fun j hj => lt_trans (SCALE_limbsLt j hj) (by norm_num)
  step with CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec x SCALE hx hS
    as ⟨fe, hfe, hfeb⟩
  step with scaled_div_spec fe z hfeb as ⟨r, hr, hrb⟩
  exact ⟨by rw [hr, field.FieldElement51.toField_mul_of_mod hfe], hrb⟩

/-- **Correctness of `bingcd::divide`.** For `x` with limbs below `2 ^ 54` and `z` with limbs
of at most `2 ^ 51 + 2 ^ 23`, the function never panics, its result has limbs below `2 ^ 52`,
and it represents the quotient in the field of integers modulo `p` of the elements its
arguments represent (with a quotient by zero being zero). -/
theorem divide_correct (x z : field.FieldElement51) (hx : x.LimbsLt 54)
    (hz : ∀ i : ℕ, i < 5 → z[i]!.val ≤ 2 ^ 51 + 2 ^ 23) :
    divide x z ⦃ (r : field.FieldElement51) =>
      r.toField = x.toField / z.toField ∧ r.LimbsLt 52 ⦄ := by
  refine WP.spec_mono (divide_spec x z hx) fun r ⟨hr, hb⟩ => ⟨?_, hb⟩
  rw [hr, Limbs.Curve25519.porninDivR_freeze (tight_L5 hz), mul_assoc, SCALE_toField, mul_one,
    value_L5, ← field.FieldElement51.toField_def]

end Curve25519Dalek.backend.serial.u64.bingcd
