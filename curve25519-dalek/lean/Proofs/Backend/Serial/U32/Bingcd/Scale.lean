module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Helpers.FieldElement2625
public section

open Aeneas Aeneas.Std Result
open Bingcd curve25519

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- The limbs of the constant `SCALE` are below `2^26`. -/
theorem SCALE_limbsLt : field.FieldElement2625.LimbsLt 26 SCALE := by
  unfold SCALE
  decide

/-- The constant `SCALE` is `2 ^ -508` in the field. -/
theorem SCALE_toField : field.FieldElement2625.toField SCALE * 2 ^ 508 = 1 := by
  have h : SCALE.asNat = Limbs.Curve25519.scale := by
    unfold SCALE
    simp only [field.FieldElement2625.asNat_def, Array.asNat2625_make]
    decide
  rw [field.FieldElement2625.toField_def, h]
  exact Limbs.Curve25519.scale_mul_two_pow

end Curve25519Dalek.backend.serial.u32.bingcd
