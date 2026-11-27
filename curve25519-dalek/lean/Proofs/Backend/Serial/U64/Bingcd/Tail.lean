module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.TailStep
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- The loop of `tail`: the steps that remain, as steps of the inner loop on words. -/
@[local step]
private theorem tail_loop_spec (T : U32) (s : Tail) (i : U32) (hi : i.val ≤ T.val) :
    tail_loop T s i ⦃ r => r.toW = Pornin.InnerW.step^[T.val - i.val] s.toW ⦄ := by
  unfold tail_loop
  apply loop.spec_decr_nat (measure := fun x => T.val - x.2.val)
    (inv := fun x => x.2.val ≤ T.val ∧
      Pornin.InnerW.step^[T.val - x.2.val] x.1.toW = Pornin.InnerW.step^[T.val - i.val] s.toW)
  · rintro ⟨s', i'⟩ ⟨hi', hinv⟩
    simp only at hi' hinv ⊢
    unfold tail_loop.body
    by_cases h : i' < T
    · simp only [h, ↓reduceIte]
      step*
      have hk : T.val - i'.val = (T.val - i1.val) + 1 := by scalar_tac
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [← hinv, hk, Function.iterate_succ_apply, s1_post]
    · simp only [h, ↓reduceIte, WP.spec_ok]
      have hk : T.val - i'.val = 0 := by scalar_tac
      rw [← hinv, hk]
      rfl
  · exact ⟨hi, rfl⟩

/-- **The last steps are the inner loop on words**, from the two words and the identity matrix,
for any number `T` of steps. -/
@[step]
theorem tail_spec (T : U32) (a b : U64) :
    tail T a b ⦃ r => r.toW = Pornin.InnerW.step^[T.val] ⟨a.bv, b.bv, 1, 0, 0, 1⟩ ⦄ := by
  unfold tail
  step*
  rw [r_post, Nat.sub_zero]
  rfl

end Curve25519Dalek.backend.serial.u64.bingcd
