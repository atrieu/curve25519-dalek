module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Eq4
import Proofs.Backend.Serial.U64.Bingcd.LinCombRedc
import Proofs.Backend.Serial.U64.Bingcd.Round
import Proofs.Backend.Serial.U64.Bingcd.Select4
import Proofs.Backend.Serial.U64.Bingcd.Tail
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- The loop of `pornin_div`: the rounds that remain, as iterations of `Pornin.roundL`. -/
@[local step]
private theorem pornin_div_loop_spec (m : Array U64 4#usize) (ninv : U64) (rounds : U32)
    (s : State) (i : U32) (hi : i.val ≤ rounds.val) :
    pornin_div_loop m ninv rounds s i ⦃ r =>
      r.toL = (Pornin.roundL 31 (L4 m) ninv.bv)^[rounds.val - i.val] s.toL ⦄ := by
  unfold pornin_div_loop
  apply loop.spec_decr_nat (measure := fun x => rounds.val - x.2.val)
    (inv := fun x => x.2.val ≤ rounds.val ∧
      (Pornin.roundL 31 (L4 m) ninv.bv)^[rounds.val - x.2.val] x.1.toL =
        (Pornin.roundL 31 (L4 m) ninv.bv)^[rounds.val - i.val] s.toL)
  · rintro ⟨s', i'⟩ ⟨hi', hinv⟩
    simp only at hi' hinv ⊢
    unfold pornin_div_loop.body
    by_cases h : i' < rounds
    · simp only [h, ↓reduceIte]
      step*
      have hk : rounds.val - i'.val = (rounds.val - i1.val) + 1 := by scalar_tac
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [← hinv, hk, Function.iterate_succ_apply, s1_post]
    · simp only [h, ↓reduceIte, WP.spec_ok]
      have hk : rounds.val - i'.val = 0 := by scalar_tac
      rw [← hinv, hk]
      rfl
  · exact ⟨hi, rfl⟩

/-- **The translated division is `Pornin.porninDivSL`**, for any number of rounds and any
number `0 < T < 64` of last steps. -/
@[step]
theorem pornin_div_spec (T : U32) (m : Array U64 4#usize) (ninv : U64) (rounds : U32)
    (x y : Array U64 4#usize) (hT0 : 0 < T.val) (hT : T.val < 64) :
    pornin_div T m ninv rounds x y ⦃ r =>
      L4 r = Pornin.porninDivSL 31 rounds.val T.val (L4 m) ninv.bv (L4 x) (L4 y) ⦄ := by
  unfold pornin_div
  step*
  have h1 : ∀ h, L4 (Array.make 4#usize [1#u64, 0#u64, 0#u64, 0#u64] h) = Limbs.ofNat 4 1 := by
    intro h
    rw [ofNat_four_one]
    rfl
  have h0 : L4 (Array.repeat 4#usize 0#u64) = Limbs.ofNat 4 0 := by
    rw [ofNat_four_zero]
    rfl
  have hs : s.toL = (Pornin.roundL 31 (L4 m) ninv.bv)^[rounds.val]
      (L4 y, L4 x, L4 m, Limbs.ofNat 4 0) := by
    rw [s_post, Nat.sub_zero]
    simp only [State.toL, h0]
  -- the last steps start from the least significant limbs of `a` and `b`
  have ht : t.toW = Pornin.InnerW.step^[T.val] ⟨(L4 s.a)[0], (L4 s.b)[0], 1, 0, 0, 1⟩ := by
    rw [t_post, i_post, i1_post]
    rfl
  -- the final `b` is `b` with its least significant limb replaced
  have hb : ∀ h, L4 (Array.make 4#usize [t.b, i2, i3, i4] h) = (L4 s.b).set 0 t.b.bv := by
    intro h
    rw [i2_post, i3_post, i4_post]
    rfl
  rw [r_post, b_post, hb, h1, h0, v_post]
  unfold Pornin.porninDivSL
  simp only
  rw [← hs]
  simp only [Pornin.tailL, State.toL, Pornin.cofRow, Word.select_false]
  rw [← ht]
  rfl

/-- **Correctness of `bingcd::pornin_div`.** For an odd modulus `m > 1` on four 64-bit limbs,
with `ninv = -1 / m` modulo `2 ^ 64`, and a schedule of `rounds` rounds and `0 < T ≤ 61` last
steps such that `31 * rounds + T ≥ 2 * len m - 2` and `31 * rounds + 65 ≥ 2 * len m`: the
function never panics, and for `x, y < m` with `y` coprime to `m` it returns the `q` in `[0, m)`
with `y * q ≡ x` modulo `m`. -/
theorem pornin_div_correct (T : U32) (m : Array U64 4#usize) (ninv : U64) (rounds : U32)
    (x y : Array U64 4#usize) (hT0 : 0 < T.val) (hT : T.val ≤ 61)
    (hN : 2 * (m.asNat 64).size ≤ 31 * rounds.val + T.val + 2)
    (hfit : 2 * (m.asNat 64).size ≤ 31 * rounds.val + 65)
    (hm1 : 1 < m.asNat 64) (hodd : m.asNat 64 % 2 = 1)
    (hinv : (m.asNat 64 * ninv.val + 1) % 2 ^ 64 = 0)
    (hx : x.asNat 64 < m.asNat 64) (hy : y.asNat 64 < m.asNat 64)
    (hco : Nat.Coprime (y.asNat 64) (m.asNat 64)) :
    pornin_div T m ninv rounds x y ⦃ r =>
      r.asNat 64 < m.asNat 64 ∧ y.asNat 64 * r.asNat 64 % m.asNat 64 = x.asNat 64 ⦄ := by
  refine WP.spec_mono (pornin_div_spec T m ninv rounds x y hT0 (by omega)) fun r hr' => ?_
  simp only [← toNat_L4] at hN hfit hm1 hodd hinv hx hy hco ⊢
  rw [hr']
  exact Pornin.porninDivSL_div (K := 31) (by norm_num) (by norm_num) (by omega) (L4 m) ninv.bv
    hm1 hodd (by simpa using hinv) (L4 x) (L4 y) hx hy (by omega) hN hco

end Curve25519Dalek.backend.serial.u64.bingcd
