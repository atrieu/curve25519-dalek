module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Select
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- `Limbs.topTwo` on four limbs, unfolded: three visits, each ending with two selections. -/
private theorem topTwo_four (m0 m1 m2 m3 x0 x1 x2 x3 : Word 64) :
    Limbs.topTwo #v[m0, m1, m2, m3] #v[x0, x1, x2, x3] =
      (Word.select (m3 == 0) (Word.select (m2 == 0) (Word.select (m1 == 0) 0 x1) x2) x3,
        Word.select (m3 == 0) (Word.select (m2 == 0) (Word.select (m1 == 0) 0 x0) x1) x2) :=
  rfl

/-- **The scan for the two limbs at the top of `m` is `Limbs.topTwo`.** -/
@[step]
theorem top_two_spec (m x : Array U64 4#usize) :
    top_two m x ⦃ (h : U64) (l : U64) =>
      h.bv = (Limbs.topTwo (L4 m) (L4 x)).1 ∧ l.bv = (Limbs.topTwo (L4 m) (L4 x)).2 ⦄ := by
  unfold top_two
  step*
  subst i_post i1_post i2_post i3_post i4_post i5_post i6_post
  have h0 : UScalar.bv 0#u64 = 0#64 := rfl
  rw [L4, L4, topTwo_four]
  simp only [h3_post, l3_post, h2_post, l2_post, h1_post, l1_post, U64.decide_eq_zero, h0,
    U64.bv]
  exact ⟨rfl, rfl⟩

end Curve25519Dalek.backend.serial.u64.bingcd
