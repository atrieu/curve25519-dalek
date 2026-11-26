module
public import Curve25519Dalek.Funs
public import Proofs.Representation.FieldElement51
public import Proofs.Curve25519.Basic
public import Proofs.Curve25519.Prime
public import Mathlib.Algebra.Field.ZMod
import Proofs.Backend.Serial.U64.Bingcd.Divide
import Proofs.Backend.Serial.U64.Field.Reduce
import Proofs.Helpers.ToField
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `div_bingcd` returns the quotient modulo `p`, and zero for a divisor that is zero, with limbs
below `2^51`. There is no condition on the limbs of the arguments: `reduce` brings them below
`2^51 + 2^18`, within the bound of `bingcd::divide`. -/
@[step]
theorem div_bingcd_spec (self rhs : FieldElement51) :
    div_bingcd self rhs ⦃ (r : FieldElement51) =>
      (rhs.asNat % p ≠ 0 → r.asNat * rhs.asNat % p = self.asNat % p) ∧
      (rhs.asNat % p = 0 → r.asNat % p = 0) ∧ r.LimbsLt 51 ⦄ := by
  unfold div_bingcd
  step with reduce_exact_spec as ⟨fe, hfe, hfeb⟩
  step with reduce_exact_spec as ⟨fe1, hfe1, hfe1b⟩
  step with bingcd.divide_correct fe fe1 (fun i hi => (hfeb i hi).le.trans (by norm_num))
    (fun i hi => (hfe1b i hi).le.trans (by norm_num)) as ⟨r, hr, hrb⟩
  have hmod : fe.asNat % p = self.asNat % p := by
    rw [← hfe, Nat.add_mul_mod_self_left]
  have hmod1 : fe1.asNat % p = rhs.asNat % p := by
    rw [← hfe1, Nat.add_mul_mod_self_left]
  obtain ⟨h1, h0⟩ := mod_of_toField_div hr
  refine ⟨fun hx => ?_, fun hx => h0 (hmod1.trans hx), hrb⟩
  rw [Nat.mul_mod, ← hmod1, ← Nat.mul_mod, ← hmod]
  exact h1 (by rwa [hmod1])

/-- `div_bingcd` on the field elements: the quotient, with `x / 0 = 0`. -/
theorem div_bingcd_toField_spec (self rhs : FieldElement51) :
    div_bingcd self rhs ⦃ (r : FieldElement51) =>
      r.toField = self.toField / rhs.toField ∧ r.LimbsLt 51 ⦄ :=
  spec_mono (div_bingcd_spec self rhs) fun _ ⟨h1, h0, hb⟩ => ⟨toField_div_of_mod h1 h0, hb⟩

end Curve25519Dalek.backend.serial.u64.field.FieldElement51
