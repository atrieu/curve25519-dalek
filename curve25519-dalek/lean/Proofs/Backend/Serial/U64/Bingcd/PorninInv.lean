module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.PorninDiv
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- **The translated inversion is `Pornin.porninInvSL`**: it is the division of `1`. -/
@[step]
theorem pornin_inv_spec (T : U32) (m : Array U64 4#usize) (ninv : U64) (rounds : U32)
    (y : Array U64 4#usize) (hT0 : 0 < T.val) (hT : T.val < 64) :
    pornin_inv T m ninv rounds y ⦃ r =>
      L4 r = Pornin.porninInvSL 31 rounds.val T.val (L4 m) ninv.bv (L4 y) ⦄ := by
  unfold pornin_inv
  step*
  have h1 : ∀ h, L4 (Array.make 4#usize [1#u64, 0#u64, 0#u64, 0#u64] h) = Limbs.ofNat 4 1 := by
    intro h
    rw [ofNat_four_one]
    rfl
  rw [r_post, h1]
  rfl

/-- **Correctness of `bingcd::pornin_inv`.** Under the conditions of `pornin_div_correct` on the
modulus and the schedule: the function never panics, and for `y < m` coprime to `m` it returns
the inverse of `y` modulo `m`, in `[0, m)`. -/
theorem pornin_inv_correct (T : U32) (m : Array U64 4#usize) (ninv : U64) (rounds : U32)
    (y : Array U64 4#usize) (hT0 : 0 < T.val) (hT : T.val ≤ 61)
    (hN : 2 * (m.asNat 64).size ≤ 31 * rounds.val + T.val + 2)
    (hfit : 2 * (m.asNat 64).size ≤ 31 * rounds.val + 65)
    (hm1 : 1 < m.asNat 64) (hodd : m.asNat 64 % 2 = 1)
    (hinv : (m.asNat 64 * ninv.val + 1) % 2 ^ 64 = 0)
    (hy : y.asNat 64 < m.asNat 64) (hco : Nat.Coprime (y.asNat 64) (m.asNat 64)) :
    pornin_inv T m ninv rounds y ⦃ r =>
      r.asNat 64 < m.asNat 64 ∧ y.asNat 64 * r.asNat 64 % m.asNat 64 = 1 ⦄ := by
  refine WP.spec_mono (pornin_inv_spec T m ninv rounds y hT0 (by omega)) fun r hr' => ?_
  simp only [← toNat_L4] at hN hfit hm1 hodd hinv hy hco ⊢
  rw [hr']
  exact Pornin.porninInvSL_inv (K := 31) (by norm_num) (by norm_num) (by omega) (L4 m) ninv.bv
    hm1 hodd (by simpa using hinv) (L4 y) hy (by omega) hN hco

end Curve25519Dalek.backend.serial.u64.bingcd
