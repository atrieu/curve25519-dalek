module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.PorninDiv
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- **The translated inversion is `Pornin.porninInvSL`**: it is the division of `1`. -/
@[step]
theorem pornin_inv_spec (T : U32) (m : Array U32 8#usize) (ninv : U32) (rounds : U32)
    (y : Array U32 8#usize) (hT0 : 0 < T.val) (hT : T.val < 32) :
    pornin_inv T m ninv rounds y ⦃ r =>
      L8 r = Pornin.porninInvSL 15 rounds.val T.val (L8 m) ninv.bv (L8 y) ⦄ := by
  unfold pornin_inv
  step*
  have h1 : ∀ h, L8 (Array.make 8#usize
      [1#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32] h) = Limbs.ofNat 8 1 := by
    intro h
    rw [ofNat_eight_one]
    rfl
  rw [r_post, h1]
  rfl

/-- **Correctness of `bingcd::pornin_inv`.** Under the conditions of `pornin_div_correct` on the
modulus and the schedule: the function never panics, and for `y < m` coprime to `m` it returns
the inverse of `y` modulo `m`, in `[0, m)`. -/
theorem pornin_inv_correct (T : U32) (m : Array U32 8#usize) (ninv : U32) (rounds : U32)
    (y : Array U32 8#usize) (hT0 : 0 < T.val) (hT : T.val ≤ 29)
    (hN : 2 * (m.asNat 32).size ≤ 15 * rounds.val + T.val + 2)
    (hfit : 2 * (m.asNat 32).size ≤ 15 * rounds.val + 33)
    (hm1 : 1 < m.asNat 32) (hodd : m.asNat 32 % 2 = 1)
    (hinv : (m.asNat 32 * ninv.val + 1) % 2 ^ 32 = 0)
    (hy : y.asNat 32 < m.asNat 32) (hco : Nat.Coprime (y.asNat 32) (m.asNat 32)) :
    pornin_inv T m ninv rounds y ⦃ r =>
      r.asNat 32 < m.asNat 32 ∧ y.asNat 32 * r.asNat 32 % m.asNat 32 = 1 ⦄ := by
  refine WP.spec_mono (pornin_inv_spec T m ninv rounds y hT0 (by omega)) fun r hr' => ?_
  simp only [← toNat_L8] at hN hfit hm1 hodd hinv hy hco ⊢
  rw [hr']
  exact Pornin.porninInvSL_inv (K := 15) (by norm_num) (by norm_num) (by omega) (L8 m) ninv.bv
    hm1 hodd (by simpa using hinv) (L8 y) hy (by omega) hN hco

end Curve25519Dalek.backend.serial.u32.bingcd
