module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.Select
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- `Limbs.topTwo` on eight limbs, unfolded: seven visits, each ending with two selections. -/
private theorem topTwo_eight (m0 m1 m2 m3 m4 m5 m6 m7 x0 x1 x2 x3 x4 x5 x6 x7 : Word 32) :
    Limbs.topTwo #v[m0, m1, m2, m3, m4, m5, m6, m7] #v[x0, x1, x2, x3, x4, x5, x6, x7] =
      (Word.select (m7 == 0) (Word.select (m6 == 0) (Word.select (m5 == 0) (Word.select (m4 == 0)
        (Word.select (m3 == 0) (Word.select (m2 == 0) (Word.select (m1 == 0) 0 x1) x2) x3) x4) x5)
        x6) x7,
        Word.select (m7 == 0) (Word.select (m6 == 0) (Word.select (m5 == 0) (Word.select (m4 == 0)
          (Word.select (m3 == 0) (Word.select (m2 == 0) (Word.select (m1 == 0) 0 x0) x1) x2) x3)
          x4) x5) x6) :=
  rfl

/-- **The scan for the two limbs at the top of `m` is `Limbs.topTwo`.** -/
@[step]
theorem top_two_spec (m x : Array U32 8#usize) :
    top_two m x ⦃ (h : U32) (l : U32) =>
      h.bv = (Limbs.topTwo (L8 m) (L8 x)).1 ∧ l.bv = (Limbs.topTwo (L8 m) (L8 x)).2 ⦄ := by
  unfold top_two
  step*
  subst i_post i1_post i2_post i3_post i4_post i5_post i6_post i7_post i8_post i9_post i10_post
    i11_post i12_post i13_post i14_post
  have h0 : UScalar.bv 0#u32 = 0#32 := rfl
  rw [L8, L8, topTwo_eight]
  simp only [h7_post, l7_post, h6_post, l6_post, h5_post, l5_post, h4_post, l4_post, h3_post,
    l3_post, h2_post, l2_post, h1_post, l1_post, U32.decide_eq_zero, h0, U32.bv]
  exact ⟨rfl, rfl⟩

end Curve25519Dalek.backend.serial.u32.bingcd
