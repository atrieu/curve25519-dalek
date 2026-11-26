module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.Eq8
import Proofs.Backend.Serial.U32.Bingcd.LinCombRedc
import Proofs.Backend.Serial.U32.Bingcd.Round
import Proofs.Backend.Serial.U32.Bingcd.Select8
import Proofs.Backend.Serial.U32.Bingcd.Tail
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- The loop of `pornin_div`: the rounds that remain, as iterations of `Pornin.roundL`. -/
@[local step]
private theorem pornin_div_loop_spec (m : Array U32 8#usize) (ninv : U32) (rounds : U32)
    (s : State) (i : U32) (hi : i.val ≤ rounds.val) :
    pornin_div_loop m ninv rounds s i ⦃ r =>
      r.toL = (Pornin.roundL 15 (L8 m) ninv.bv)^[rounds.val - i.val] s.toL ⦄ := by
  unfold pornin_div_loop
  apply loop.spec_decr_nat (measure := fun x => rounds.val - x.2.val)
    (inv := fun x => x.2.val ≤ rounds.val ∧
      (Pornin.roundL 15 (L8 m) ninv.bv)^[rounds.val - x.2.val] x.1.toL =
        (Pornin.roundL 15 (L8 m) ninv.bv)^[rounds.val - i.val] s.toL)
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
number `0 < T < 32` of last steps. -/
@[step]
theorem pornin_div_spec (T : U32) (m : Array U32 8#usize) (ninv : U32) (rounds : U32)
    (x y : Array U32 8#usize) (hT0 : 0 < T.val) (hT : T.val < 32) :
    pornin_div T m ninv rounds x y ⦃ r =>
      L8 r = Pornin.porninDivSL 15 rounds.val T.val (L8 m) ninv.bv (L8 x) (L8 y) ⦄ := by
  unfold pornin_div
  step*
  have h1 : ∀ h, L8 (Array.make 8#usize
      [1#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32] h) = Limbs.ofNat 8 1 := by
    intro h
    rw [ofNat_eight_one]
    rfl
  have h0 : L8 (Array.repeat 8#usize 0#u32) = Limbs.ofNat 8 0 := by
    rw [ofNat_eight_zero]
    rfl
  have hs : s.toL = (Pornin.roundL 15 (L8 m) ninv.bv)^[rounds.val]
      (L8 y, L8 x, L8 m, Limbs.ofNat 8 0) := by
    rw [s_post, Nat.sub_zero]
    simp only [State.toL, h0]
  -- the last steps start from the least significant limbs of `a` and `b`
  have ht : t.toW = Pornin.InnerW.step^[T.val] ⟨(L8 s.a)[0], (L8 s.b)[0], 1, 0, 0, 1⟩ := by
    rw [t_post, i_post, i1_post]
    rfl
  -- the final `b` is `b` with its least significant limb replaced
  have hb : ∀ h, L8 (Array.make 8#usize [t.b, i2, i3, i4, i5, i6, i7, i8] h) =
      (L8 s.b).set 0 t.b.bv := by
    intro h
    rw [i2_post, i3_post, i4_post, i5_post, i6_post, i7_post, i8_post]
    rfl
  rw [r_post, b_post, hb, h1, h0, v_post]
  unfold Pornin.porninDivSL
  simp only
  rw [← hs]
  simp only [Pornin.tailL, State.toL, Pornin.cofRow, Word.select_false]
  rw [← ht]
  rfl

/-- **Correctness of `bingcd::pornin_div`.** For an odd modulus `m > 1` on eight 32-bit limbs,
with `ninv = -1 / m` modulo `2 ^ 32`, and a schedule of `rounds` rounds and `0 < T ≤ 29` last
steps such that `15 * rounds + T ≥ 2 * len m - 2` and `15 * rounds + 33 ≥ 2 * len m`: the
function never panics, and for `x, y < m` with `y` coprime to `m` it returns the `q` in `[0, m)`
with `y * q ≡ x` modulo `m`. -/
theorem pornin_div_correct (T : U32) (m : Array U32 8#usize) (ninv : U32) (rounds : U32)
    (x y : Array U32 8#usize) (hT0 : 0 < T.val) (hT : T.val ≤ 29)
    (hN : 2 * (m.asNat 32).size ≤ 15 * rounds.val + T.val + 2)
    (hfit : 2 * (m.asNat 32).size ≤ 15 * rounds.val + 33)
    (hm1 : 1 < m.asNat 32) (hodd : m.asNat 32 % 2 = 1)
    (hinv : (m.asNat 32 * ninv.val + 1) % 2 ^ 32 = 0)
    (hx : x.asNat 32 < m.asNat 32) (hy : y.asNat 32 < m.asNat 32)
    (hco : Nat.Coprime (y.asNat 32) (m.asNat 32)) :
    pornin_div T m ninv rounds x y ⦃ r =>
      r.asNat 32 < m.asNat 32 ∧ y.asNat 32 * r.asNat 32 % m.asNat 32 = x.asNat 32 ⦄ := by
  refine WP.spec_mono (pornin_div_spec T m ninv rounds x y hT0 (by omega)) fun r hr' => ?_
  simp only [← toNat_L8] at hN hfit hm1 hodd hinv hx hy hco ⊢
  rw [hr']
  exact Pornin.porninDivSL_div (K := 15) (by norm_num) (by norm_num) (by omega) (L8 m) ninv.bv
    hm1 hodd (by simpa using hinv) (L8 x) (L8 y) hx hy (by omega) hN hco

end Curve25519Dalek.backend.serial.u32.bingcd
