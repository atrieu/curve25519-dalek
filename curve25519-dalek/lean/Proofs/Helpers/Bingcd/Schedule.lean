module
public import Proofs.Helpers.Bingcd.Montgomery

/-! # Pornin's optimized binary gcd: a shorter schedule

`porninInv` runs `⌈(2 * ℓ(m) - 1) / K⌉` rounds of `K` steps, each decided on approximations.
Two remarks of Pornin's note shorten this, for any odd modulus:

* `2 * ℓ(m) - 2` steps are enough. At that point `a` is `0` or both operands are `1`, so `b`
  is already the gcd; the last step would only bring `a` to `0`.
* The last steps need no round. Once `a` and `b` are short, the steps can be decided on the
  operands themselves: this is the plain binary gcd, there is no approximation and so no limit
  of `K` steps, and only the cofactor `v` has to be updated afterwards.

This file defines the schedule of `r` rounds followed by `T` steps on the operands, and shows
that it computes the same inverse as `porninInv` when `K * r + T ≥ 2 * ℓ(m) - 2`. For a
255-bit modulus and `K = 31`, this is 15 rounds and 43 steps instead of 17 rounds.

That the last steps fit in a machine word is a matter for the word-level refinement, which
uses `roundM_iterate_fit`; nothing here depends on it. -/

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

/-! ### The inversion -/

/-- The inverse of `y` modulo an odd `m` by `r` rounds of `K` inner steps followed by `T`
steps on the operands themselves. It is `0` when `y` is not invertible. -/
def porninInvS (y m K r T : ℕ) : ℕ :=
  let p := tail m T ((round m K)^[r] (y, 1, m, 0))
  if p.1 = 1 then p.2 * powMod m ((m + 1) / 2) (K * r + T) % m else 0

/-- **Correctness of the shorter schedule.** For `K ≥ 1`, `m > 1` odd, `y < m` coprime to `m`
and `K * r + T ≥ 2 * ℓ(m) - 2`, the result is the inverse of `y` modulo `m`, in `[0, m)`. -/
theorem porninInvS_spec {y m K r T : ℕ} (hK : 1 ≤ K) (hm : 1 < m) (hodd : m % 2 = 1) (hy : y < m)
    (hN : 2 * m.size ≤ K * r + T + 2) (hc : Nat.Coprime y m) :
    porninInvS y m K r T < m ∧ y * porninInvS y m K r T % m = 1 := by
  obtain ⟨hb, -, hv⟩ := rinv_tail (T := T) (by omega) hy hN (rinv_iterate (y := y) hK hm hodd r)
  rw [hc] at hb hv
  simp only [porninInvS, hb, ite_true]
  generalize (tail m T ((round m K)^[r] (y, 1, m, 0))).2 = v at *
  generalize K * r + T = N at *
  refine ⟨Nat.mod_lt _ (by omega), ?_⟩
  have hv' : v * y ≡ 2 ^ N [MOD m] := Int.natCast_modEq_iff.mp (by simpa using hv)
  rw [mul_half_pow_modEq hodd hv', Nat.mod_eq_of_lt hm]

/-- When `y` is not invertible modulo `m`, the result is `0`. -/
theorem porninInvS_eq_zero {y m K r T : ℕ} (hK : 1 ≤ K) (hm : 1 < m) (hodd : m % 2 = 1)
    (hy : y < m) (hN : 2 * m.size ≤ K * r + T + 2) (hc : Nat.gcd y m ≠ 1) :
    porninInvS y m K r T = 0 := by
  obtain ⟨hb, -, -⟩ := rinv_tail (T := T) (by omega) hy hN (rinv_iterate (y := y) hK hm hodd r)
  simp [porninInvS, hb, hc]

/-- Two inverses of `y` modulo `m` in `[0, m)` are equal. -/
theorem inv_unique {m y x x' : ℕ} (hx : x < m) (hx' : x' < m) (h : y * x % m = 1)
    (h' : y * x' % m = 1) : x = x' := by
  have hm : 1 < m := by
    have := Nat.mod_lt (y * x) (by omega : 0 < m)
    omega
  have e : y * x ≡ 1 [MOD m] := by rw [Nat.ModEq, h, Nat.mod_eq_of_lt hm]
  have e' : y * x' ≡ 1 [MOD m] := by rw [Nat.ModEq, h', Nat.mod_eq_of_lt hm]
  have key : x ≡ x' [MOD m] := by
    calc x = x * 1 := (Nat.mul_one x).symm
      _ ≡ x * (y * x') [MOD m] := e'.symm.mul_left x
      _ = y * x * x' := by ring
      _ ≡ 1 * x' [MOD m] := e.mul_right x'
      _ = x' := Nat.one_mul x'
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx'] at key

/-- **The shorter schedule computes the same inverse.** -/
theorem porninInvS_eq {y m K r T : ℕ} (hK : 1 ≤ K) (hm : 1 < m) (hodd : m % 2 = 1) (hy : y < m)
    (hN : 2 * m.size ≤ K * r + T + 2) : porninInvS y m K r T = porninInv y m K := by
  by_cases hc : Nat.gcd y m = 1
  · obtain ⟨h1, h2⟩ := porninInvS_spec hK hm hodd hy hN hc
    obtain ⟨h3, h4⟩ := porninInv_spec hK hm hodd hy hc
    exact inv_unique h1 h3 h2 h4
  · rw [porninInvS_eq_zero hK hm hodd hy hN hc, porninInv_eq_zero hK hm hodd hy hc]

/-! ### Cofactors divided by a power of two -/

/-- The last `T` steps with the new cofactor divided by `2 ^ T` modulo `m`. -/
def tailM (m T : ℕ) (s : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ :=
  let t := Inner.step^[T] ⟨s.1, s.2.2.1, 1, 0, 0, 1⟩
  (t.bbar.toNat, ((s.2.1 * t.f1 + s.2.2.2 * t.g1) * (((m + 1) / 2 : ℕ) : ℤ) ^ T % m).toNat)

theorem sim_tail {m K i T : ℕ} (hm : 0 < m) {s s' : ℕ × ℕ × ℕ × ℕ} (h : Sim m K i s s') :
    (tailM m T s').1 = (tail m T s).1 ∧
      ((tailM m T s').2 : ℤ) = (tail m T s).2 * (((m + 1) / 2 : ℕ) : ℤ) ^ (K * i + T) % m := by
  obtain ⟨a, u, b, v⟩ := s
  obtain ⟨a', u', b', v'⟩ := s'
  obtain ⟨rfl, rfl, hu, hv⟩ := h
  dsimp only at hu hv
  have hm' : (m : ℤ) ≠ 0 := by omega
  unfold tail tailM
  dsimp only
  refine ⟨rfl, ?_⟩
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm'), Int.toNat_of_nonneg (Int.emod_nonneg _ hm'),
    pow_add]
  simpa using cofactor_sim hu hv False

/-- The inversion with `r` rounds and `T` last steps, the cofactors being divided by `2 ^ K`
at every round and by `2 ^ T` after the last steps. There is no final correction. -/
def porninInvSM (y m K r T : ℕ) : ℕ :=
  let p := tailM m T ((roundM m K)^[r] (y, 1, m, 0))
  if p.1 = 1 then p.2 else 0

theorem porninInvSM_eq {y m K r T : ℕ} (hm : 1 < m) :
    porninInvSM y m K r T = porninInvS y m K r T := by
  obtain ⟨hb, hv⟩ := sim_tail (T := T) (by omega : 0 < m) (sim_iterate (K := K) hm y r)
  unfold porninInvSM porninInvS
  dsimp only
  rw [hb]
  split_ifs
  · have h1 := (powMod_modEq m ((m + 1) / 2) (K * r + T)).mul_left
      (tail m T ((round m K)^[r] (y, 1, m, 0))).2
    rw [h1]
    exact_mod_cast hv
  · rfl

/-! ### The operands become short -/

/-- After `r` rounds, `a = 0` or both operands have at most `2 * ℓ(m) - K * r - 1` bits. With
`w` at least that, the last steps can run on `w`-bit words. -/
theorem roundM_iterate_fit {y m K w : ℕ} (hK : 1 ≤ K) (hm : 1 < m) (hodd : m % 2 = 1)
    (hy : y < m) {r : ℕ} (hfit : 2 * m.size ≤ K * r + w + 1) :
    ((roundM m K)^[r] (y, 1, m, 0)).1 = 0 ∨
      (((roundM m K)^[r] (y, 1, m, 0)).1 < 2 ^ w ∧
        ((roundM m K)^[r] (y, 1, m, 0)).2.2.1 < 2 ^ w) := by
  obtain ⟨ha, hb, -, -⟩ := sim_iterate (K := K) hm y r
  obtain ⟨hbo, -, -, -, -, -, hpot⟩ := rinv_iterate (y := y) hK hm hodd r
  rw [ha, hb]
  rcases hpot with h | h
  · exact Or.inl h
  · have hy' := Nat.size_le_size hy.le
    have h1 := Nat.size_pos.mpr
      (by omega : 0 < ((round m K)^[r] (y, 1, m, 0)).2.2.1)
    by_cases h0 : ((round m K)^[r] (y, 1, m, 0)).1 = 0
    · exact Or.inl h0
    · have h2 := Nat.size_pos.mpr (Nat.pos_of_ne_zero h0)
      exact Or.inr ⟨Nat.size_le.mp (by omega), Nat.size_le.mp (by omega)⟩

end Bingcd.Pornin

/-! ## Division

The cofactors `u`, `v` of the algorithm only go through linear combinations modulo `m`.
Starting them at `(x, 0)` instead of `(1, 0)` therefore multiplies them by `x` throughout, and
the same run returns `x / y` instead of `1 / y`: a quotient costs no multiplication more than
an inverse. -/

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

/-- The same for a round with the cofactors divided by `2 ^ K`. -/
theorem roundM_scale {m K : ℕ} (hm : 0 < m) (x : ℕ) (s : ℕ × ℕ × ℕ × ℕ) :
    roundM m K (scale m x s) = scale m x (roundM m K s) := by
  obtain ⟨a, u, b, v⟩ := s
  unfold roundM scale
  dsimp only
  exact Prod.ext rfl (Prod.ext (cofactor_scale hm x u v _ _ _ _)
    (Prod.ext rfl (cofactor_scale hm x u v _ _ _ _)))

/-- The same for the last steps: `b` is unchanged and `v` is multiplied by `x`. -/
theorem tailM_scale {m T : ℕ} (hm : 0 < m) (x : ℕ) (s : ℕ × ℕ × ℕ × ℕ) :
    tailM m T (scale m x s) = ((tailM m T s).1, x * (tailM m T s).2 % m) := by
  obtain ⟨a, u, b, v⟩ := s
  unfold tailM scale
  dsimp only
  refine Prod.ext rfl ?_
  have h := cofactor_scale hm x u v
    (Inner.step^[T] ⟨(a : ℤ), (b : ℤ), 1, 0, 0, 1⟩).f1
    (Inner.step^[T] ⟨(a : ℤ), (b : ℤ), 1, 0, 0, 1⟩).g1 ((((m + 1) / 2 : ℕ) : ℤ) ^ T) False
  simpa using h

theorem round_iterate_scale {m K : ℕ} (hm : 0 < m) (x : ℕ) (s : ℕ × ℕ × ℕ × ℕ) (i : ℕ) :
    (round m K)^[i] (scale m x s) = scale m x ((round m K)^[i] s) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, round_scale hm]

/-! ### Division -/

/-- The quotient of `x` by `y` modulo an odd `m`, by Pornin's algorithm with the cofactors
started at `(x, 0)`. It is `0` when `y` is not invertible. -/
def porninDiv (x y m K : ℕ) : ℕ :=
  let s := (round m K)^[rounds m K] (y, x, m, 0)
  if s.2.2.1 = 1 then
    s.2.2.2 * powMod m ((m + 1) / 2) (K * rounds m K) % m
  else 0

/-- **The division is the inverse multiplied by `x`.** -/
theorem porninDiv_eq {x y m K : ℕ} (hx : x < m) :
    porninDiv x y m K = x * porninInv y m K % m := by
  unfold porninDiv porninInv
  dsimp only
  rw [← scale_init hx, round_iterate_scale (by omega)]
  generalize (round m K)^[rounds m K] (y, 1, m, 0) = s
  obtain ⟨a, u, b, v⟩ := s
  simp only [scale]
  by_cases hb : b = 1
  · simp only [hb, ↓reduceIte]
    rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]
  · simp [hb]

theorem porninDiv_lt {x y m K : ℕ} (hx : x < m) : porninDiv x y m K < m := by
  rw [porninDiv_eq hx]
  exact Nat.mod_lt _ (by omega)

/-- **Correctness of the division.** For `K ≥ 1`, `m > 1` odd, `x, y < m` and `y` coprime to
`m`, the result `q` is in `[0, m)` and `y * q ≡ x` modulo `m`. -/
theorem porninDiv_spec {x y m K : ℕ} (hK : 1 ≤ K) (hm : 1 < m) (hodd : m % 2 = 1) (hx : x < m)
    (hy : y < m) (hc : Nat.Coprime y m) :
    porninDiv x y m K < m ∧ y * porninDiv x y m K % m = x := by
  obtain ⟨-, h⟩ := porninInv_spec hK hm hodd hy hc
  refine ⟨porninDiv_lt hx, ?_⟩
  rw [porninDiv_eq hx, Nat.mul_mod_mod, ← Nat.mul_assoc, Nat.mul_comm y x, Nat.mul_assoc,
    ← Nat.mul_mod_mod, h, Nat.mul_one, Nat.mod_eq_of_lt hx]

/-- Modulo an odd prime `p`, `porninDiv` computes the quotient in `ZMod p`, with the usual
convention that a quotient by `0` is `0`. -/
theorem natCast_porninDiv {x y p K : ℕ} [hp : Fact p.Prime] (hK : 1 ≤ K) (hodd : p % 2 = 1)
    (hx : x < p) (hy : y < p) : ((porninDiv x y p K : ℕ) : ZMod p) = (x : ZMod p) / y := by
  rw [porninDiv_eq hx, ZMod.natCast_mod, Nat.cast_mul, natCast_porninInv hK hodd hy,
    div_eq_mul_inv]

end Bingcd.Pornin
