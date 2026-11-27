module
public import Proofs.Helpers.Bingcd.Inversion

/-! # Pornin's optimized binary gcd: the schedule

The rounds of `Inversion.lean` run `K` steps each, decided on approximations. Two remarks of
Pornin's note fix how many steps are needed, for any odd modulus:

* `2 * ℓ(m) - 2` steps are enough. At that point `a` is `0` or both operands are `1`, so `b`
  is already the gcd; the last step would only bring `a` to `0`.
* The last steps need no round. Once `a` and `b` are short, the steps can be decided on the
  operands themselves: this is the plain binary gcd, there is no approximation and so no limit
  of `K` steps, and only the cofactor `v` has to be updated afterwards.

This file defines the last `T` steps on the operands (`tail`) and shows that, after `r` rounds
and these steps with `K * r + T ≥ 2 * ℓ(m) - 2`, `b` is the gcd and the cofactor `v` satisfies
`v * y ≡ 2 ^ (K * r + T) * b` modulo `m` (`rinv_tail`). For a 255-bit modulus this is 508
steps: 15 rounds and 43 steps for `K = 31`, 32 rounds and 28 steps for `K = 15`.

That the last steps fit in a machine word is a matter for the word-level refinement; nothing
here depends on it. -/

@[expose] public section

namespace Bingcd.Pornin

/-! ### Steps on the operands themselves -/

/-- From `ā = 0`, the steps only double the second row of the matrix, whatever `b̄` is. -/
theorem step_iterate_zero (y : ℤ) (t : ℕ) :
    Inner.step^[t] ⟨0, y, 1, 0, 0, 1⟩ = ⟨0, y, 1, 0, 0, 2 ^ t⟩ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [Inner.step, pow_succ, mul_comm]

/-- The structural invariant at the start of a run on the operands themselves. -/
theorem base_plain (K : ℕ) (a : ℤ) {b : ℤ} (hb : b % 2 = 1) :
    Base K K a b 0 ((a, b), ⟨a, b, 1, 0, 0, 1⟩) := by
  refine ⟨by simp, by simp, hb, hb, ?_, ?_, ?_, ?_, by simp, by simp⟩ <;> simp

/-- The state after `T` steps on the operands `(a, b)` themselves, which is the plain binary
gcd: `ā` and `b̄` are the current operands. They are nonnegative, have the gcd of `a` and `b`,
are given by the rows of the matrix, and a bit is removed at every step until `ā = 0`. -/
def Plain (a b : ℤ) (T : ℕ) (s : Inner) : Prop :=
  0 ≤ s.abar ∧ 0 < s.bbar ∧ 2 ^ T * s.abar = a * s.f0 + b * s.g0 ∧
    2 ^ T * s.bbar = a * s.f1 + b * s.g1 ∧ Int.gcd s.abar s.bbar = Int.gcd a b ∧
    (s.abar = 0 ∨ len s.abar + len s.bbar + T ≤ len a + len b) ∧ (a = 0 → s.abar = 0)

theorem plain_iterate {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) (hodd : b % 2 = 1) (T : ℕ) :
    Plain a b T (Inner.step^[T] ⟨a, b, 1, 0, 0, 1⟩) := by
  have hbase := base_plain T a hodd
  have hx := phase_iterate hbase (PhX (len a + len b)) ⟨rfl, rfl, ha, hb, Or.inr le_rfl⟩
    fun _ _ => phX_gstep
  have hgcd := gcd_iterate hbase
  have hzero := zero_iterate hbase
  have hfin := base_iterate hbase (le_refl T)
  have hsnd := gstep_iterate_snd T ((a, b), (⟨a, b, 1, 0, 0, 1⟩ : Inner))
  dsimp only at hsnd hgcd hzero
  rw [← hsnd]
  generalize gstep^[T] ((a, b), ⟨a, b, 1, 0, 0, 1⟩) = G at *
  obtain ⟨⟨A, B⟩, ⟨x, y, f0, g0, f1, g1⟩⟩ := G
  obtain ⟨hAx, hBy, hA0, hB0, hpot⟩ := hx
  obtain ⟨-, -, -, -, -, -, -, -, hl1, hl2⟩ := hfin
  dsimp only at hAx hBy hA0 hB0 hpot hl1 hl2 hgcd hzero ⊢
  subst hAx hBy
  exact ⟨hA0, hB0, hl1, hl2, hgcd, hpot, hzero⟩

/-! ### The last steps -/

/-- The last `T` steps, on the operands themselves, from a state `(a, u, b, v)`: the final
`b`, and the final `v` modulo `m`. The final `a` and `u` are not needed. -/
def tail (m T : ℕ) (s : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ :=
  let t := Inner.step^[T] ⟨s.1, s.2.2.1, 1, 0, 0, 1⟩
  (t.bbar.toNat, ((s.2.1 * t.f1 + s.2.2.2 * t.g1) % m).toNat)

/-- **After `2 * ℓ(m) - 2` steps, `b` is the gcd.** From the state of `r` rounds, `T` steps on
the operands with `K * r + T ≥ 2 * ℓ(m) - 2` leave `b = gcd y m`, and `v` with
`v * y ≡ 2 ^ (K * r + T) * b` modulo `m`. -/
theorem rinv_tail {y m K r T : ℕ} (hm : 0 < m) (hy : y < m) (hN : 2 * m.size ≤ K * r + T + 2)
    {s : ℕ × ℕ × ℕ × ℕ} (hs : RInv y m K r s) :
    (tail m T s).1 = Nat.gcd y m ∧ (tail m T s).2 < m ∧
      ((tail m T s).2 : ℤ) * y ≡ 2 ^ (K * r + T) * (Nat.gcd y m : ℕ) [ZMOD m] := by
  obtain ⟨a, u, b, v⟩ := s
  obtain ⟨hb, hg, -, -, hau, hbv, hpot⟩ := hs
  dsimp only at hb hg hau hbv hpot
  have hP := plain_iterate (a := (a : ℤ)) (b := b) (by positivity) (by omega) (by omega) T
  unfold tail
  dsimp only
  generalize Inner.step^[T] ⟨(a : ℤ), (b : ℤ), 1, 0, 0, 1⟩ = t at *
  obtain ⟨A, B, f0, g0, f1, g1⟩ := t
  obtain ⟨hA0, hB0, -, hl, hgcd, hpot', hzero⟩ := hP
  dsimp only at hA0 hB0 hl hgcd hpot' hzero ⊢
  have hm' : (m : ℤ) ≠ 0 := by omega
  have hB : B = (Nat.gcd y m : ℕ) := by
    rw [← hg, ← Int.gcd_natCast_natCast a b, ← hgcd]
    by_cases hA : A = 0
    · subst hA
      rw [Int.gcd_zero_left]
      omega
    · -- both operands have one bit
      have ha : a ≠ 0 := fun h => hA (hzero (by exact_mod_cast h))
      have hy' := Nat.size_le_size hy.le
      have h1 : 0 < A.natAbs.size := Nat.size_pos.mpr (by omega)
      have h2 : 0 < B.natAbs.size := Nat.size_pos.mpr (by omega)
      unfold len at hpot'
      simp only [Int.natAbs_natCast] at hpot'
      have h3 : A.natAbs < 2 ^ 1 := Nat.size_le.mp (by omega)
      have h4 : B.natAbs < 2 ^ 1 := Nat.size_le.mp (by omega)
      obtain rfl : A = 1 := by omega
      obtain rfl : B = 1 := by omega
      rfl
  refine ⟨by rw [hB, Int.toNat_natCast], ?_, ?_⟩
  · zify
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm')]
    exact Int.emod_lt_of_pos _ (by omega)
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm'), ← hB, pow_add]
    simpa using cofactor_modEq hau hbv hl 1

end Bingcd.Pornin

/-! ## Division

The cofactors `u`, `v` of the algorithm only go through linear combinations modulo `m`.
Starting them at `(x, 0)` instead of `(1, 0)` therefore multiplies them by `x` throughout, and
the same run returns a multiple of `x / y` instead of one of `1 / y`. -/

namespace Bingcd.Pornin

/-! ### Multiplying the cofactors by `x` -/

/-- The state with its cofactors multiplied by `x` modulo `m`. -/
def scale (m x : ℕ) (s : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (s.1, x * s.2.1 % m, s.2.2.1, x * s.2.2.2 % m)

/-- The run of the division starts from the scaled start of the inversion. -/
theorem scale_init {m x : ℕ} (hx : x < m) (y : ℕ) : scale m x (y, 1, m, 0) = (y, x, m, 0) := by
  simp [scale, Nat.mod_eq_of_lt hx]

/-- The cofactor update of a step, on cofactors multiplied by `x`: the result is multiplied
by `x`. -/
theorem cofactor_scale {m : ℕ} (hm : 0 < m) (x u v : ℕ) (f g H : ℤ) (P : Prop) [Decidable P] :
    ((if P then -(((x * u % m : ℕ) : ℤ) * f + ((x * v % m : ℕ) : ℤ) * g)
        else ((x * u % m : ℕ) : ℤ) * f + ((x * v % m : ℕ) : ℤ) * g) * H % m).toNat =
      x * ((if P then -((u : ℤ) * f + v * g) else (u : ℤ) * f + v * g) * H % m).toNat % m := by
  have hm' : (m : ℤ) ≠ 0 := by omega
  have hu : ((x * u % m : ℕ) : ℤ) ≡ x * u [ZMOD m] := by
    push_cast
    exact Int.mod_modEq _ _
  have hv : ((x * v % m : ℕ) : ℤ) ≡ x * v [ZMOD m] := by
    push_cast
    exact Int.mod_modEq _ _
  have h1 : ((x * u % m : ℕ) : ℤ) * f + ((x * v % m : ℕ) : ℤ) * g ≡
      x * ((u : ℤ) * f + v * g) [ZMOD m] := by
    have := (hu.mul_right f).add (hv.mul_right g)
    rwa [show (x : ℤ) * u * f + x * v * g = x * ((u : ℤ) * f + v * g) by ring] at this
  apply Int.natCast_inj.mp
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm')]
  push_cast
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm')]
  change _ ≡ _ [ZMOD m]
  split_ifs
  · calc -(((x * u % m : ℕ) : ℤ) * f + ((x * v % m : ℕ) : ℤ) * g) * H
        ≡ -(x * ((u : ℤ) * f + v * g)) * H [ZMOD m] := h1.neg.mul_right H
      _ = x * (-((u : ℤ) * f + v * g) * H) := by ring
      _ ≡ x * (-((u : ℤ) * f + v * g) * H % m) [ZMOD m] := (Int.mod_modEq _ _).symm.mul_left _
  · calc (((x * u % m : ℕ) : ℤ) * f + ((x * v % m : ℕ) : ℤ) * g) * H
        ≡ x * ((u : ℤ) * f + v * g) * H [ZMOD m] := h1.mul_right H
      _ = x * (((u : ℤ) * f + v * g) * H) := by ring
      _ ≡ x * (((u : ℤ) * f + v * g) * H % m) [ZMOD m] := (Int.mod_modEq _ _).symm.mul_left _

/-- **A round commutes with the multiplication of the cofactors by `x`.** -/
theorem round_scale {m K : ℕ} (hm : 0 < m) (x : ℕ) (s : ℕ × ℕ × ℕ × ℕ) :
    round m K (scale m x s) = scale m x (round m K s) := by
  obtain ⟨a, u, b, v⟩ := s
  unfold round scale
  dsimp only
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))
  · have h := cofactor_scale hm x u v
      (Inner.step^[K] ⟨approx K (max (max a.size b.size) (2 * K + 2) - K - 2) a,
        approx K (max (max a.size b.size) (2 * K + 2) - K - 2) b, 1, 0, 0, 1⟩).f0
      (Inner.step^[K] ⟨approx K (max (max a.size b.size) (2 * K + 2) - K - 2) a,
        approx K (max (max a.size b.size) (2 * K + 2) - K - 2) b, 1, 0, 0, 1⟩).g0 1
    simp only [mul_one] at h
    exact h _
  · have h := cofactor_scale hm x u v
      (Inner.step^[K] ⟨approx K (max (max a.size b.size) (2 * K + 2) - K - 2) a,
        approx K (max (max a.size b.size) (2 * K + 2) - K - 2) b, 1, 0, 0, 1⟩).f1
      (Inner.step^[K] ⟨approx K (max (max a.size b.size) (2 * K + 2) - K - 2) a,
        approx K (max (max a.size b.size) (2 * K + 2) - K - 2) b, 1, 0, 0, 1⟩).g1 1
    simp only [mul_one] at h
    exact h _

theorem round_iterate_scale {m K : ℕ} (hm : 0 < m) (x : ℕ) (s : ℕ × ℕ × ℕ × ℕ) (i : ℕ) :
    (round m K)^[i] (scale m x s) = scale m x ((round m K)^[i] s) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, round_scale hm]

end Bingcd.Pornin
