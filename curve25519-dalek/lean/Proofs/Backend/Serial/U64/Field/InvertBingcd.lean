module
public import Curve25519Dalek.Funs
public import Proofs.Representation.FieldElement51
public import Proofs.Curve25519.Basic
import Proofs.Backend.Serial.U64.Bingcd.Invert
import Proofs.Backend.Serial.U64.Field.Reduce
import Proofs.Helpers.ToField
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `invert_bingcd` returns the inverse modulo `p`, and zero at zero, with limbs below `2^51`.
There is no condition on the limbs of the argument: `reduce` brings them below `2^51 + 2^18`,
within the bound of `bingcd::invert`. -/
@[step]
theorem invert_bingcd_spec (self : FieldElement51) :
    invert_bingcd self ⦃ (r : FieldElement51) =>
      (self.asNat % p ≠ 0 → r.asNat * self.asNat % p = 1) ∧
      (self.asNat % p = 0 → r.asNat % p = 0) ∧ r.LimbsLt 51 ⦄ := by
  unfold invert_bingcd
  step with reduce_exact_spec as ⟨fe, hfe, hfeb⟩
  step with bingcd.invert_correct fe (fun i hi => (hfeb i hi).le.trans (by norm_num))
    as ⟨r, hr, hrb⟩
  have hmod : fe.asNat % p = self.asNat % p := by
    rw [← hfe, Nat.add_mul_mod_self_left]
  obtain ⟨h1, h0⟩ := mod_of_toField_inv hr
  refine ⟨fun hx => ?_, fun hx => h0 (hmod.trans hx), hrb⟩
  rw [Nat.mul_mod, ← hmod, ← Nat.mul_mod]
  exact h1 (by rwa [hmod])

/-- `invert_bingcd` on the field elements: the inverse, with `0⁻¹ = 0`. -/
theorem invert_bingcd_toField_spec (self : FieldElement51) :
    invert_bingcd self ⦃ (r : FieldElement51) =>
      r.toField = self.toField⁻¹ ∧ r.LimbsLt 51 ⦄ :=
  spec_mono (invert_bingcd_spec self) fun _ ⟨h1, h0, hb⟩ => ⟨toField_inv_of_mod h1 h0, hb⟩

end Curve25519Dalek.backend.serial.u64.field.FieldElement51
