module
public import Proofs.Curve25519.X25519
public import Curve25519Dalek.Funs
public import Proofs.Representation.Montgomery
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.ToBytes
import Proofs.Backend.Serial.U32.Field.DivBingcd
import Proofs.Backend.Serial.U64.Field.DivBingcd
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.ToBytes
import Proofs.Helpers.ToField2625
public import Proofs.Helpers.ByteValues
public section

/-! # `ProjectivePoint::as_affine` (Montgomery) -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek

namespace montgomery.«ProjectivePoint64bit-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ProjectivePoint::as_affine`: the canonical encoding of `U / W` (`0` at infinity). -/
@[step]
theorem as_affine_spec (self : montgomery.ProjectivePoint.«64bit-tables») (hself : self.LimbsLt 54)
    :
    as_affine self ⦃ (r : montgomery.MontgomeryPoint) => r.asNat = encodeU self.toXZ.toU ⦄ := by
  obtain ⟨hU, hW⟩ := hself
  unfold as_affine
  step as ⟨u, hu1, hu0, hu_lt⟩
  step as ⟨r, hr⟩
  rw [montgomery.MontgomeryPoint.asNat_def, hr, ← toField_val, toField_div_of_mod hu1 hu0,
    montgomery.ProjectivePoint.«64bit-tables».toXZ_def, MontgomeryModel.XZ.toU, encodeU]

end montgomery.«ProjectivePoint64bit-tables»

namespace montgomery.«ProjectivePoint32bit-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ProjectivePoint::as_affine`: the canonical encoding of `U / W` (`0` at infinity). -/
@[step]
theorem as_affine_spec (self : montgomery.ProjectivePoint.«32bit-tables») (hself : self.LimbsLt 27)
    :
    as_affine self ⦃ (r : montgomery.MontgomeryPoint) => r.asNat = encodeU self.toXZ.toU ⦄ := by
  obtain ⟨hU, hW⟩ := hself
  unfold as_affine
  step as ⟨u, hu1, hu0, hu_lt⟩
  step as ⟨r, hr⟩
  rw [montgomery.MontgomeryPoint.asNat_def, hr, ← toField_val, toField_div_of_mod hu1 hu0,
    montgomery.ProjectivePoint.«32bit-tables».toXZ_def, MontgomeryModel.XZ.toU, encodeU]

end montgomery.«ProjectivePoint32bit-tables»

namespace montgomery.«ProjectivePoint64bit-notables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `ProjectivePoint::as_affine`: the canonical encoding of `U / W` (`0` at infinity). -/
@[step]
theorem as_affine_spec (self : montgomery.ProjectivePoint.«64bit-notables») (hself : self.LimbsLt
    54) :
    as_affine self ⦃ (r : montgomery.MontgomeryPoint) => r.asNat = encodeU self.toXZ.toU ⦄ := by
  obtain ⟨hU, hW⟩ := hself
  unfold as_affine
  step as ⟨u, hu1, hu0, hu_lt⟩
  step as ⟨r, hr⟩
  rw [montgomery.MontgomeryPoint.asNat_def, hr, ← toField_val, toField_div_of_mod hu1 hu0,
    montgomery.ProjectivePoint.«64bit-notables».toXZ_def, MontgomeryModel.XZ.toU, encodeU]

end montgomery.«ProjectivePoint64bit-notables»

namespace montgomery.«ProjectivePoint32bit-notables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `ProjectivePoint::as_affine`: the canonical encoding of `U / W` (`0` at infinity). -/
@[step]
theorem as_affine_spec (self : montgomery.ProjectivePoint.«32bit-notables») (hself : self.LimbsLt
    27) :
    as_affine self ⦃ (r : montgomery.MontgomeryPoint) => r.asNat = encodeU self.toXZ.toU ⦄ := by
  obtain ⟨hU, hW⟩ := hself
  unfold as_affine
  step as ⟨u, hu1, hu0, hu_lt⟩
  step as ⟨r, hr⟩
  rw [montgomery.MontgomeryPoint.asNat_def, hr, ← toField_val, toField_div_of_mod hu1 hu0,
    montgomery.ProjectivePoint.«32bit-notables».toXZ_def, MontgomeryModel.XZ.toU, encodeU]

end montgomery.«ProjectivePoint32bit-notables»

end Curve25519Dalek
