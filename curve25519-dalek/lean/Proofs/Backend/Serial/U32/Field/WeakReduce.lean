module
public import Curve25519Dalek.Funs
public import Proofs.Representation.FieldElement2625
public import Proofs.Helpers.FieldElement2625
import Proofs.Backend.Serial.U32.Field.Reduce
public section

open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `weak_reduce` keeps the value modulo `p` and brings the limbs within the bounds of `reduce`:
below `2^26` at even positions and below `2^25 + 2^18` at odd ones. There is no condition on the
limbs of the argument: they are widened to `u64` and passed to `reduce`. -/
@[step]
theorem weak_reduce_spec (self : FieldElement2625) :
    weak_reduce self ⦃ (r : FieldElement2625) =>
      r.asNat % p = self.asNat % p ∧ r.LimbsLt 26 ∧
      ∀ i : ℕ, i < 10 → r[i]!.val < limbRadix i + i % 2 * 2 ^ 18 ⦄ := by
  unfold weak_reduce
  simp only [index_usize_eq, Nat.reduceLT, UScalar.ofNatCore_val_eq]
  step*
  · have h0 := (self[0]!).hBounds
    have h1 := (self[1]!).hBounds
    have h2 := (self[2]!).hBounds
    have h3 := (self[3]!).hBounds
    have h4 := (self[4]!).hBounds
    have h5 := (self[5]!).hBounds
    have h6 := (self[6]!).hBounds
    have h7 := (self[7]!).hBounds
    have h8 := (self[8]!).hBounds
    have h9 := (self[9]!).hBounds
    exact getElem!_make_le _ _ _ _ _ _ _ _ _ _ _ _ (by scalar_tac) (by scalar_tac)
      (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
      (by scalar_tac) (by scalar_tac) (by scalar_tac)
  · refine ⟨?_, r_post1, r_post2⟩
    rw [r_post, Array.asNat2625_make, asNat_expand]
    simp only [*, U32.cast_U64_val_eq]

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625
