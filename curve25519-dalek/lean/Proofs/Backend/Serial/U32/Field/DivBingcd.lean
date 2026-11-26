module
public import Curve25519Dalek.Funs
public import Proofs.Representation.FieldElement2625
public import Proofs.Curve25519.Basic
public import Proofs.Curve25519.Prime
public import Mathlib.Algebra.Field.ZMod
import Proofs.Backend.Serial.U32.Bingcd.Divide
import Proofs.Backend.Serial.U32.Field.WeakReduce
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `div_bingcd` returns the quotient modulo `p`, and zero for a divisor that is zero, with limbs
below `2^26`. There is no condition on the limbs of the arguments: `weak_reduce` brings them
within the bounds of `bingcd::divide`. -/
@[step]
theorem div_bingcd_spec (self rhs : FieldElement2625) :
    div_bingcd self rhs ⦃ (r : FieldElement2625) =>
      (rhs.asNat % p ≠ 0 → r.asNat * rhs.asNat % p = self.asNat % p) ∧
      (rhs.asNat % p = 0 → r.asNat % p = 0) ∧ r.LimbsLt 26 ⦄ := by
  unfold div_bingcd
  step with weak_reduce_spec as ⟨fe, hmod, _, hfeb⟩
  step with weak_reduce_spec as ⟨fe1, hmod1, _, hfe1b⟩
  step with bingcd.divide_correct fe fe1 hfeb hfe1b as ⟨r, hr, hrb⟩
  obtain ⟨h1, h0⟩ := mod_of_toField_div hr
  refine ⟨fun hx => ?_, fun hx => h0 (hmod1.trans hx), hrb⟩
  rw [Nat.mul_mod, ← hmod1, ← Nat.mul_mod, ← hmod]
  exact h1 (by rwa [hmod1])

/-- `div_bingcd` on the field elements: the quotient, with `x / 0 = 0`. -/
theorem div_bingcd_toField_spec (self rhs : FieldElement2625) :
    div_bingcd self rhs ⦃ (r : FieldElement2625) =>
      r.toField = self.toField / rhs.toField ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (div_bingcd_spec self rhs) fun _ ⟨h1, h0, hb⟩ => ⟨toField_div_of_mod h1 h0, hb⟩

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625
