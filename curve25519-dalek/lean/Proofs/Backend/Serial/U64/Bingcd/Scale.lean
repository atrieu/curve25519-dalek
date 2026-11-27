module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Helpers.Limbs
import Proofs.Helpers.ToField
public section

open Aeneas Aeneas.Std Result
open Bingcd curve25519

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- The limbs of the constant `SCALE` are below `2^51`. -/
theorem SCALE_limbsLt : field.FieldElement51.LimbsLt 51 SCALE := by
  unfold SCALE
  decide

/-- The constant `SCALE` is `2 ^ -508` in the field. -/
theorem SCALE_toField : field.FieldElement51.toField SCALE * 2 ^ 508 = 1 := by
  have h : SCALE.asNat = Limbs.Curve25519.scale := by
    unfold SCALE
    simp only [field.FieldElement51.asNat_def, Array.asNat_def]
    decide
  rw [field.FieldElement51.toField_def, h]
  exact Limbs.Curve25519.scale_mul_two_pow

end Curve25519Dalek.backend.serial.u64.bingcd
