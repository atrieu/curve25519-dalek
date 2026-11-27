module
public import Curve25519Dalek.Funs
public import Proofs.Representation.FieldElement2625
public import Proofs.Curve25519.Basic
public import Proofs.Helpers.Backend.U32
import Proofs.Backend.Serial.U32.Bingcd.Invert
import Proofs.Backend.Serial.U32.Field.WeakReduce
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `invert_bingcd` returns the inverse modulo `p`, and zero at zero, with limbs below `2^26`.
There is no condition on the limbs of the argument: `weak_reduce` brings them within the bounds
of `bingcd::invert`. -/
@[step]
theorem invert_bingcd_spec (self : FieldElement2625) :
    invert_bingcd self ⦃ (r : FieldElement2625) =>
      (self.asNat % p ≠ 0 → r.asNat * self.asNat % p = 1) ∧
      (self.asNat % p = 0 → r.asNat % p = 0) ∧ r.LimbsLt 26 ⦄ := by
  unfold invert_bingcd
  step with weak_reduce_spec as ⟨fe, hmod, _, hfeb⟩
  step with bingcd.invert_correct fe hfeb as ⟨r, hr, hrb⟩
  obtain ⟨h1, h0⟩ := mod_of_toField_inv hr
  refine ⟨fun hx => ?_, fun hx => h0 (hmod.trans hx), hrb⟩
  rw [Nat.mul_mod, ← hmod, ← Nat.mul_mod]
  exact h1 (by rwa [hmod])

/-- `invert_bingcd` on the field elements: the inverse, with `0⁻¹ = 0`. -/
theorem invert_bingcd_toField_spec (self : FieldElement2625) :
    invert_bingcd self ⦃ (r : FieldElement2625) =>
      r.toField = self.toField⁻¹ ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (invert_bingcd_spec self) fun _ ⟨h1, h0, hb⟩ => ⟨toField_inv_of_mod h1 h0, hb⟩

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace Curve25519Dalek.Backend

/-- The inversion of the `u32` backend, as a `Backend` spec. -/
theorem U32.invert_spec : U32.InvertSpec := fun a _ =>
  spec_mono (FieldElement2625.invert_bingcd_toField_spec a) fun _ ⟨h, hb⟩ => ⟨h, hb⟩

end Curve25519Dalek.Backend
