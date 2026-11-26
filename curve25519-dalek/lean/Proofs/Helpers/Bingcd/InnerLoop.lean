module
public import Mathlib.Init
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import Mathlib.Data.Nat.Size
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.Positivity

/-! # Pornin's optimized binary gcd: the inner loop

Pornin's modular inversion (*Optimized Binary GCD for Modular Inversion*, 2020) runs the
extended binary gcd in rounds of `K` steps. Within a round the steps are decided on
word-sized approximations `ab`, `bb` of the operands, and only build a transition matrix
`(f₀, g₀; f₁, g₁)`, which is applied to the full-size operands once per round.

This file defines the inner loop and the *ghost* run that carries along the values `A`, `B`
the operands would have if they were updated at every step (the `aₜ`, `bₜ` of Mahboubi,
Melquiond, Strub and Vallejos Parada, *Functional Correctness of an Optimized Modular
Inversion Algorithm*, ITP 2026). Because the decisions are taken on approximations, `A` and
`B` can become negative.

The parameter `K` is the number of inner steps; it is `k - 1` in the papers. It is `31` in
`bingcd.rs`. -/

@[expose] public section

/-! ## Odd numbers -/

namespace Bingcd

/-- An odd number is coprime to `2`. -/
theorem coprime_two_of_odd {y : ℕ} (h : y % 2 = 1) : Nat.Coprime 2 y := by
  have h₁ := Nat.gcd_dvd_left 2 y
  have h₂ := Nat.gcd_dvd_right 2 y
  have hle := Nat.le_of_dvd (by norm_num) h₁
  change Nat.gcd 2 y = 1
  generalize Nat.gcd 2 y = g at *
  have hg : g ≠ 0 := by
    rintro rfl
    simp at h₁
  rcases (by omega : g = 1 ∨ g = 2) with rfl | rfl
  · rfl
  · omega

end Bingcd

/-! ## Bit lengths -/

namespace Bingcd

/-! ### Halving and subtracting modulo `m` -/

/-- The bit length, computed from `Nat.log2`. -/
def bitLen (n : ℕ) : ℕ := if n = 0 then 0 else n.log2 + 1

/-- `Nat.size` is compiled as `bitLen`: Mathlib's definition recurses over the bits and is
slow on large numbers. -/
@[csimp] theorem size_eq_bitLen : @Nat.size = @bitLen := by
  funext n
  unfold bitLen
  split
  · next h => rw [h, Nat.size_zero]
  · next h =>
    refine eq_of_forall_ge_iff fun k => ?_
    rw [Nat.size_le, Nat.succ_le_iff, Nat.log2_lt h]

/-- Halving removes a bit. -/
theorem size_add_one_le_of_le_half {c x : ℕ} (h : c ≤ x / 2) (hx : x ≠ 0) :
    c.size + 1 ≤ x.size := by
  have hp := Nat.size_pos.mpr (Nat.pos_of_ne_zero hx)
  have hlt := Nat.lt_size_self x
  have e : 2 ^ x.size = 2 * 2 ^ (x.size - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have := Nat.size_le.mpr (by omega : c < 2 ^ (x.size - 1))
  omega

end Bingcd

/-! ## Halving and the gcd -/

namespace Bingcd

/-- Halving an even number does not change its gcd with an odd number. -/
theorem gcd_half {a b : ℤ} (ha : a % 2 = 1) (hb : b % 2 = 0) :
    Int.gcd a (b / 2) = Int.gcd a b := by
  have hb' : b = 2 * (b / 2) := by omega
  have hco : Nat.Coprime 2 a.natAbs := coprime_two_of_odd (by omega)
  conv_rhs => rw [hb']
  rw [Int.gcd_def, Int.gcd_def, Int.natAbs_mul]
  exact (Nat.Coprime.gcd_mul_left_cancel_right _ hco).symm

end Bingcd

/-! ## The inner loop and its ghost run -/

namespace Bingcd.Pornin

/-- The state of the inner loop: the approximations and the transition matrix. -/
structure Inner where
  /-- The approximation of `a`. -/
  abar : ℤ
  /-- The approximation of `b`. -/
  bbar : ℤ
  /-- The entry `f₀` of the transition matrix. -/
  f0 : ℤ
  /-- The entry `g₀` of the transition matrix. -/
  g0 : ℤ
  /-- The entry `f₁` of the transition matrix. -/
  f1 : ℤ
  /-- The entry `g₁` of the transition matrix. -/
  g1 : ℤ

/-- One step of the inner loop. The second row of the matrix is doubled at every step, so
that after `t` steps `2 ^ t * abₜ = ab * f₀ + bb * g₀` and `2 ^ t * bbₜ = ab * f₁ + bb * g₁`. -/
def Inner.step (s : Inner) : Inner :=
  if s.abar % 2 = 0 then ⟨s.abar / 2, s.bbar, s.f0, s.g0, 2 * s.f1, 2 * s.g1⟩
  else if s.abar < s.bbar then
    ⟨(s.bbar - s.abar) / 2, s.abar, s.f1 - s.f0, s.g1 - s.g0, 2 * s.f0, 2 * s.g0⟩
  else ⟨(s.abar - s.bbar) / 2, s.bbar, s.f0 - s.f1, s.g0 - s.g1, 2 * s.f1, 2 * s.g1⟩

/-- The step on the true values `(A, B)`, decided by the approximations. -/
def trueStep (abar bbar : ℤ) (x : ℤ × ℤ) : ℤ × ℤ :=
  if abar % 2 = 0 then (x.1 / 2, x.2)
  else if abar < bbar then ((x.2 - x.1) / 2, x.1)
  else ((x.1 - x.2) / 2, x.2)

/-- One step of the ghost run: the inner loop together with the true values. -/
def gstep (p : (ℤ × ℤ) × Inner) : (ℤ × ℤ) × Inner :=
  (trueStep p.2.abar p.2.bbar p.1, p.2.step)

theorem gstep_iterate_snd (t : ℕ) (p : (ℤ × ℤ) × Inner) :
    (gstep^[t] p).2 = Inner.step^[t] p.2 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

/-- A division-free description of a ghost step, when `A` has the parity of `ab` and `B`,
`bb` are odd: a halving, a swap followed by a subtraction, or a subtraction. -/
theorem gstep_spec {A B ab bb : ℤ} (f0 g0 f1 g1 : ℤ) (hA : A % 2 = ab % 2) (hB : B % 2 = 1)
    (hb : bb % 2 = 1) :
    ∃ A' ab' : ℤ,
      (ab = 2 * ab' ∧ A = 2 * A' ∧
        gstep ((A, B), ⟨ab, bb, f0, g0, f1, g1⟩) = ((A', B), ⟨ab', bb, f0, g0, 2 * f1, 2 * g1⟩)) ∨
      (ab % 2 = 1 ∧ ab < bb ∧ bb - ab = 2 * ab' ∧ B - A = 2 * A' ∧
        gstep ((A, B), ⟨ab, bb, f0, g0, f1, g1⟩) =
          ((A', A), ⟨ab', ab, f1 - f0, g1 - g0, 2 * f0, 2 * g0⟩)) ∨
      (ab % 2 = 1 ∧ bb ≤ ab ∧ ab - bb = 2 * ab' ∧ A - B = 2 * A' ∧
        gstep ((A, B), ⟨ab, bb, f0, g0, f1, g1⟩) =
          ((A', B), ⟨ab', bb, f0 - f1, g0 - g1, 2 * f1, 2 * g1⟩)) := by
  by_cases h1 : ab % 2 = 0
  · exact ⟨A / 2, ab / 2, Or.inl ⟨by omega, by omega, by simp [gstep, trueStep, Inner.step, h1]⟩⟩
  · by_cases h2 : ab < bb
    · exact ⟨(B - A) / 2, (bb - ab) / 2, Or.inr <| Or.inl ⟨by omega, h2, by omega, by omega,
        by simp [gstep, trueStep, Inner.step, h1, h2]⟩⟩
    · exact ⟨(A - B) / 2, (ab - bb) / 2, Or.inr <| Or.inr ⟨by omega, by omega, by omega, by omega,
        by simp [gstep, trueStep, Inner.step, h1, h2]⟩⟩

/-! ### The structural invariant -/

/-- The structural invariant of the ghost run after `t` of `K` steps from true values
`(a, b)`, with approximation error at most `2 ^ p`. -/
def Base (K p : ℕ) (a b : ℤ) (t : ℕ) (s : (ℤ × ℤ) × Inner) : Prop :=
  (2 : ℤ) ^ (K - t) ∣ s.1.1 - s.2.abar ∧ (2 : ℤ) ^ (K - t) ∣ s.1.2 - s.2.bbar ∧
    s.2.bbar % 2 = 1 ∧ s.1.2 % 2 = 1 ∧
    -2 ^ p ≤ s.1.1 - 2 ^ (p - K) * s.2.abar ∧ s.1.1 - 2 ^ (p - K) * s.2.abar ≤ 2 ^ p ∧
    -2 ^ p ≤ s.1.2 - 2 ^ (p - K) * s.2.bbar ∧ s.1.2 - 2 ^ (p - K) * s.2.bbar ≤ 2 ^ p ∧
    2 ^ t * s.1.1 = a * s.2.f0 + b * s.2.g0 ∧ 2 ^ t * s.1.2 = a * s.2.f1 + b * s.2.g1

/-- While steps remain, `A` has the parity of `ab`. -/
theorem Base.parity {K p : ℕ} {a b : ℤ} {t : ℕ} {s : (ℤ × ℤ) × Inner} (h : Base K p a b t s)
    (ht : t < K) : s.1.1 % 2 = s.2.abar % 2 := by
  obtain ⟨c, hc⟩ := h.1
  obtain ⟨j, rfl⟩ : ∃ j, K = t + 1 + j := ⟨K - t - 1, by omega⟩
  rw [show t + 1 + j - t = j + 1 by omega, pow_succ, mul_assoc, mul_comm, mul_assoc] at hc
  omega

theorem base_gstep {K p : ℕ} {a b : ℤ} {t : ℕ} {s : (ℤ × ℤ) × Inner} (h : Base K p a b t s)
    (ht : t < K) : Base K p a b (t + 1) (gstep s) := by
  have hpar := h.parity ht
  obtain ⟨⟨A, B⟩, ⟨ab, bb, f0, g0, f1, g1⟩⟩ := s
  obtain ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩, hb, hB, hA1, hA2, hB1, hB2, hl1, hl2⟩ := h
  simp only at hpar hc₁ hc₂ hb hB hA1 hA2 hB1 hB2 hl1 hl2
  obtain ⟨j, rfl⟩ : ∃ j, K = t + 1 + j := ⟨K - t - 1, by omega⟩
  rw [show t + 1 + j - t = j + 1 by omega, pow_succ] at hc₁ hc₂
  have hE : (0 : ℤ) ≤ 2 ^ p := by positivity
  unfold Base
  rw [show t + 1 + j - (t + 1) = j by omega]
  generalize (2 : ℤ) ^ (p - (t + 1 + j)) = e at *
  generalize (2 : ℤ) ^ p = E at *
  generalize (2 : ℤ) ^ j = D at *
  obtain ⟨A', ab', h | h | h⟩ := gstep_spec f0 g0 f1 g1 hpar hB hb
  · obtain ⟨rfl, rfl, heq⟩ := h
    rw [heq]
    dsimp only
    refine ⟨⟨c₁, by linarith⟩, ⟨2 * c₂, by linarith⟩, hb, hB, by linarith, by linarith, hB1,
      hB2, ?_, ?_⟩
    · rw [pow_succ]; linear_combination hl1
    · rw [pow_succ]; linear_combination 2 * hl2
  · obtain ⟨ha, -, hab', hA', heq⟩ := h
    rw [heq]
    dsimp only
    have he : 2 * (e * ab') = e * bb - e * ab := by linear_combination (-e) * hab'
    refine ⟨⟨c₂ - c₁, by linarith⟩, ⟨2 * c₁, by linarith⟩, ha, by omega, by linarith,
      by linarith, hA1, hA2, ?_, ?_⟩
    · rw [pow_succ]; linear_combination hl2 - hl1 - 2 ^ t * hA'
    · rw [pow_succ]; linear_combination 2 * hl1
  · obtain ⟨-, -, hab', hA', heq⟩ := h
    rw [heq]
    dsimp only
    have he : 2 * (e * ab') = e * ab - e * bb := by linear_combination (-e) * hab'
    refine ⟨⟨c₁ - c₂, by linarith⟩, ⟨2 * c₂, by linarith⟩, hb, hB, by linarith, by linarith,
      hB1, hB2, ?_, ?_⟩
    · rw [pow_succ]; linear_combination hl1 - hl2 - 2 ^ t * hA'
    · rw [pow_succ]; linear_combination 2 * hl2

theorem base_iterate {K p : ℕ} {a b : ℤ} {s : (ℤ × ℤ) × Inner} (h : Base K p a b 0 s) {t : ℕ}
    (ht : t ≤ K) : Base K p a b t (gstep^[t] s) := by
  induction t with
  | zero => exact h
  | succ t ih => rw [Function.iterate_succ_apply']; exact base_gstep (ih (by omega)) (by omega)

/-! ### The entries of the transition matrix are small -/

/-- After `t` steps, each row of the transition matrix has absolute sum at most `2 ^ t`. -/
def MatBound (t : ℕ) (s : Inner) : Prop :=
  |s.f0| + |s.g0| ≤ 2 ^ t ∧ |s.f1| + |s.g1| ≤ 2 ^ t

theorem matBound_step {t : ℕ} {s : Inner} (h : MatBound t s) : MatBound (t + 1) s.step := by
  obtain ⟨x, y, f0, g0, f1, g1⟩ := s
  obtain ⟨h0, h1⟩ := h
  dsimp only at h0 h1
  have e1 : ∀ z : ℤ, |2 * z| = 2 * |z| := fun z => by rw [abs_mul, abs_two]
  have hp : (0 : ℤ) < 2 ^ t := by positivity
  unfold MatBound Inner.step
  dsimp only
  rw [pow_succ]
  split_ifs
  · exact ⟨by dsimp only; linarith, by dsimp only; rw [e1, e1]; linarith⟩
  · exact ⟨by dsimp only; linarith [abs_sub f1 f0, abs_sub g1 g0],
      by dsimp only; rw [e1, e1]; linarith⟩
  · exact ⟨by dsimp only; linarith [abs_sub f0 f1, abs_sub g0 g1],
      by dsimp only; rw [e1, e1]; linarith⟩

theorem matBound_iterate (x y : ℤ) (t : ℕ) : MatBound t (Inner.step^[t] ⟨x, y, 1, 0, 0, 1⟩) := by
  induction t with
  | zero => exact ⟨by simp, by simp⟩
  | succ t ih => rw [Function.iterate_succ_apply']; exact matBound_step ih

/-! ### The signs of the transition matrix -/

/-- In each row of the transition matrix, one entry is positive and the other is not, and the
two rows have opposite patterns. A swap of the rows exchanges the two cases. -/
def MatSigns (s : Inner) : Prop :=
  (0 < s.f0 ∧ s.g0 ≤ 0 ∧ s.f1 ≤ 0 ∧ 0 < s.g1) ∨ (s.f0 < 0 ∧ 0 < s.g0 ∧ 0 < s.f1 ∧ s.g1 ≤ 0)

theorem matSigns_step {s : Inner} (h : MatSigns s) : MatSigns s.step := by
  obtain ⟨x, y, f0, g0, f1, g1⟩ := s
  unfold MatSigns at h ⊢
  unfold Inner.step
  dsimp only at h ⊢
  split_ifs <;> dsimp only <;> omega

theorem matSigns_iterate (x y : ℤ) (t : ℕ) : MatSigns (Inner.step^[t] ⟨x, y, 1, 0, 0, 1⟩) := by
  induction t with
  | zero => exact Or.inl ⟨by norm_num, le_refl _, le_refl _, by norm_num⟩
  | succ t ih => rw [Function.iterate_succ_apply']; exact matSigns_step ih

/-- With the bound and the signs, every entry of the transition matrix is in
`(-2 ^ t, 2 ^ t]`: an entry `-2 ^ t` would leave `0` for the other entry of its row, which the
signs exclude. -/
theorem entry_range {t : ℕ} {s : Inner} (hm : MatBound t s) (hs : MatSigns s) :
    (-2 ^ t < s.f0 ∧ s.f0 ≤ 2 ^ t) ∧ (-2 ^ t < s.g0 ∧ s.g0 ≤ 2 ^ t) ∧
      (-2 ^ t < s.f1 ∧ s.f1 ≤ 2 ^ t) ∧ (-2 ^ t < s.g1 ∧ s.g1 ≤ 2 ^ t) := by
  obtain ⟨x, y, f0, g0, f1, g1⟩ := s
  obtain ⟨h0, h1⟩ := hm
  unfold MatSigns at hs
  dsimp only at h0 h1 hs ⊢
  have a1 := le_abs_self f0
  have a2 := neg_abs_le f0
  have a3 := le_abs_self g0
  have a4 := neg_abs_le g0
  have a5 := le_abs_self f1
  have a6 := neg_abs_le f1
  have a7 := le_abs_self g1
  have a8 := neg_abs_le g1
  generalize |f0| = F0 at *
  generalize |g0| = G0 at *
  generalize |f1| = F1 at *
  generalize |g1| = G1 at *
  generalize (2 : ℤ) ^ t = T at *
  omega

/-- After `t` steps from the identity matrix, every entry is in `(-2 ^ t, 2 ^ t]`. -/
theorem entry_range_iterate (x y : ℤ) (t : ℕ) :
    (-2 ^ t < (Inner.step^[t] ⟨x, y, 1, 0, 0, 1⟩).f0 ∧
        (Inner.step^[t] ⟨x, y, 1, 0, 0, 1⟩).f0 ≤ 2 ^ t) ∧
      (-2 ^ t < (Inner.step^[t] ⟨x, y, 1, 0, 0, 1⟩).g0 ∧
        (Inner.step^[t] ⟨x, y, 1, 0, 0, 1⟩).g0 ≤ 2 ^ t) ∧
      (-2 ^ t < (Inner.step^[t] ⟨x, y, 1, 0, 0, 1⟩).f1 ∧
        (Inner.step^[t] ⟨x, y, 1, 0, 0, 1⟩).f1 ≤ 2 ^ t) ∧
      (-2 ^ t < (Inner.step^[t] ⟨x, y, 1, 0, 0, 1⟩).g1 ∧
        (Inner.step^[t] ⟨x, y, 1, 0, 0, 1⟩).g1 ≤ 2 ^ t) :=
  entry_range (matBound_iterate x y t) (matSigns_iterate x y t)

end Bingcd.Pornin
