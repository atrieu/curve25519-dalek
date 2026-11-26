module
public import Proofs.Helpers.Bingcd.InnerLoop

/-! # Pornin's optimized binary gcd: bit reduction of the inner loop

One round of `K` inner steps removes at least `K` bits from `ℓ(a) + ℓ(b)`, unless `a`
reaches zero, even though the steps are decided on approximations (Theorem 20 of Mahboubi,
Melquiond, Strub and Vallejos Parada, ITP 2026; Appendix A of Pornin's note).

The proof here is organised as four invariants of the ghost run, one for each way a round
can go, rather than around the first divergent step:

* `exact`: the approximations are exact, and the run is the plain binary gcd;
* `distA`: `a` is much larger than `b`; no swap happens (their Lemma 31);
* `distB`: `b` is much larger than `a`; one swap happens after the initial halvings, and
  none afterwards (their Lemma 32);
* `close`: the operands have similar sizes. Steps agree with the plain binary gcd until a
  first wrong comparison, after which either both values are small, or one is large and
  positive and the other small and nonpositive (their Section 3.3). -/

@[expose] public section

namespace Bingcd.Pornin

/-! ### Bit lengths of integers -/

/-- The bit length of `|x|`. -/
def len (x : ℤ) : ℕ := x.natAbs.size

theorem len_succ_le {x y : ℤ} (h : 2 * y.natAbs ≤ x.natAbs) (hx : x ≠ 0) :
    len y + 1 ≤ len x :=
  size_add_one_le_of_le_half (by omega) (by omega)

theorem len_mono {x y : ℤ} (h : y.natAbs ≤ x.natAbs) : len y ≤ len x := Nat.size_le_size h

theorem len_le_of_lt {x : ℤ} {j : ℕ} (h1 : -2 ^ j < x) (h2 : x < 2 ^ j) : len x ≤ j := by
  refine Nat.size_le.mpr ?_
  zify
  exact abs_lt.mpr ⟨h1, h2⟩

theorem len_le_succ {x y : ℤ} (h : x.natAbs ≤ 2 * y.natAbs) : len x ≤ len y + 1 := by
  refine Nat.size_le.mpr ?_
  have := Nat.lt_size_self y.natAbs
  rw [pow_succ]
  unfold len
  omega

/-! ### Iterating an invariant along the ghost run -/

theorem phase_iterate {K p : ℕ} {a b : ℤ} {s₀ : (ℤ × ℤ) × Inner} (hbase : Base K p a b 0 s₀)
    (Φ : ℕ → (ℤ × ℤ) × Inner → Prop) (h0 : Φ 0 s₀)
    (hstep : ∀ t s, t < K → Base K p a b t s → Φ t s → Φ (t + 1) (gstep s)) :
    Φ K (gstep^[K] s₀) := by
  suffices H : ∀ t, t ≤ K → Φ t (gstep^[t] s₀) from H K le_rfl
  intro t
  induction t with
  | zero => exact fun _ => h0
  | succ t ih =>
    intro ht
    rw [Function.iterate_succ_apply']
    exact hstep t _ (by omega) (base_iterate hbase (by omega)) (ih (by omega))

/-! ### Exact approximations -/

/-- The invariant when the approximations are exact. -/
def PhX (L t : ℕ) (s : (ℤ × ℤ) × Inner) : Prop :=
  s.1.1 = s.2.abar ∧ s.1.2 = s.2.bbar ∧ 0 ≤ s.1.1 ∧ 0 < s.1.2 ∧
    (s.1.1 = 0 ∨ len s.1.1 + len s.1.2 + t ≤ L)

theorem phX_gstep {K p L : ℕ} {a b : ℤ} {t : ℕ} {s : (ℤ × ℤ) × Inner} (ht : t < K)
    (hB : Base K p a b t s) (h : PhX L t s) : PhX L (t + 1) (gstep s) := by
  have hpar := hB.parity ht
  obtain ⟨⟨A, B⟩, ⟨x, y, f0, g0, f1, g1⟩⟩ := s
  obtain ⟨-, -, hy, hBo, -⟩ := hB
  obtain ⟨hAx, hBy, hA0, hB0, hpot⟩ := h
  dsimp only at hpar hy hBo hAx hBy hA0 hB0 hpot
  obtain ⟨A', x', h | h | h⟩ := gstep_spec f0 g0 f1 g1 hpar hBo hy
  · obtain ⟨hx, hA, heq⟩ := h
    rw [heq]
    refine ⟨by dsimp only; omega, hBy, by dsimp only; omega, hB0, ?_⟩
    dsimp only
    by_cases hA0' : A = 0
    · exact Or.inl (by omega)
    · have := len_succ_le (x := A) (y := A') (by omega) hA0'
      exact Or.inr (by omega)
  · obtain ⟨hx1, hxy, hx, hA, heq⟩ := h
    rw [heq]
    refine ⟨by dsimp only; omega, hAx, by dsimp only; omega, by dsimp only; omega, ?_⟩
    dsimp only
    have := len_succ_le (x := B) (y := A') (by omega) (by omega)
    exact Or.inr (by omega)
  · obtain ⟨hx1, hxy, hx, hA, heq⟩ := h
    rw [heq]
    refine ⟨by dsimp only; omega, hBy, by dsimp only; omega, hB0, ?_⟩
    dsimp only
    have := len_succ_le (x := A) (y := A') (by omega) (by omega)
    exact Or.inr (by omega)

/-- **Bit reduction, exact case.** -/
theorem bitReduction_exact {K p : ℕ} {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b)
    (hbase : Base K p a b 0 ((a, b), ⟨a, b, 1, 0, 0, 1⟩)) :
    (gstep^[K] ((a, b), ⟨a, b, 1, 0, 0, 1⟩)).1.1 = 0 ∨
      len (gstep^[K] ((a, b), ⟨a, b, 1, 0, 0, 1⟩)).1.1 +
        len (gstep^[K] ((a, b), ⟨a, b, 1, 0, 0, 1⟩)).1.2 + K ≤ len a + len b :=
  (phase_iterate hbase (PhX (len a + len b)) ⟨rfl, rfl, ha, hb, Or.inr le_rfl⟩
    fun _ _ => phX_gstep).2.2.2.2

/-! ### One operand dominates: no swap -/

/-- The invariant when `A` dominates `B`, on the true values and on the approximations. -/
def PhW (K L t : ℕ) (s : (ℤ × ℤ) × Inner) : Prop :=
  0 < s.1.2 ∧ 0 < s.2.bbar ∧ 2 ^ (K - t) * s.1.2 < s.1.1 + s.1.2 ∧
    2 ^ (K - t) * s.2.bbar < s.2.abar + s.2.bbar ∧ len s.1.1 + len s.1.2 + t ≤ L

theorem phW_gstep {K p L : ℕ} {a b : ℤ} {t : ℕ} {s : (ℤ × ℤ) × Inner} (ht : t < K)
    (hB : Base K p a b t s) (h : PhW K L t s) : PhW K L (t + 1) (gstep s) := by
  have hpar := hB.parity ht
  obtain ⟨⟨A, B⟩, ⟨x, y, f0, g0, f1, g1⟩⟩ := s
  obtain ⟨-, -, hy, hBo, -⟩ := hB
  obtain ⟨hB0, hy0, hAB, hxy, hpot⟩ := h
  dsimp only at hpar hy hBo hB0 hy0 hAB hxy hpot
  obtain ⟨j, rfl⟩ : ∃ j, K = t + 1 + j := ⟨K - t - 1, by omega⟩
  rw [show t + 1 + j - t = j + 1 by omega, pow_succ] at hAB hxy
  unfold PhW
  rw [show t + 1 + j - (t + 1) = j by omega]
  have hD : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  generalize (2 : ℤ) ^ j = D at *
  have hDB : B ≤ D * B := le_mul_of_one_le_left hB0.le hD
  have hDy : y ≤ D * y := le_mul_of_one_le_left hy0.le hD
  have hBA : B < A := by linarith
  have hyx : y < x := by linarith
  obtain ⟨A', x', h | h | h⟩ := gstep_spec f0 g0 f1 g1 hpar hBo hy
  · obtain ⟨hx, hA, heq⟩ := h
    rw [heq]
    dsimp only
    have := len_succ_le (x := A) (y := A') (by omega) (by omega)
    exact ⟨hB0, hy0, by linarith, by linarith, by omega⟩
  · obtain ⟨hx1, hlt, hx, hA, heq⟩ := h
    linarith
  · obtain ⟨hx1, hle, hx, hA, heq⟩ := h
    rw [heq]
    dsimp only
    have := len_succ_le (x := A) (y := A') (by omega) (by omega)
    exact ⟨hB0, hy0, by linarith, by linarith, by omega⟩

/-- **Bit reduction when `a` dominates `b`** (Lemma 31). -/
theorem bitReduction_distA {K p : ℕ} {a b x₀ y₀ : ℤ} (hb : 0 < b) (hy : 0 < y₀)
    (hab : 2 ^ K * b < a + b) (hxy : 2 ^ K * y₀ < x₀ + y₀)
    (hbase : Base K p a b 0 ((a, b), ⟨x₀, y₀, 1, 0, 0, 1⟩)) :
    len (gstep^[K] ((a, b), ⟨x₀, y₀, 1, 0, 0, 1⟩)).1.1 +
        len (gstep^[K] ((a, b), ⟨x₀, y₀, 1, 0, 0, 1⟩)).1.2 + K ≤ len a + len b :=
  (phase_iterate hbase (PhW K (len a + len b)) ⟨hb, hy, hab, hxy, le_rfl⟩
    fun _ _ => phW_gstep).2.2.2.2

/-! ### The other operand dominates: halvings, one swap, then no swap -/

/-- The invariant when `b` dominates `a`: only halvings so far, or one swap has happened and
the new `A` dominates. -/
def PhB (K L : ℕ) (a b x₀ y₀ : ℤ) (t : ℕ) (s : (ℤ × ℤ) × Inner) : Prop :=
  (2 ^ t * s.1.1 = a ∧ 2 ^ t * s.2.abar = x₀ ∧ s.1.2 = b ∧ s.2.bbar = y₀ ∧
    (s.1.1 = 0 ∨ len s.1.1 + len s.1.2 + t ≤ L)) ∨ PhW K L t s

theorem phB_gstep {K p L : ℕ} {a b x₀ y₀ : ℤ} (ha : 0 ≤ a) (hx₀ : 0 ≤ x₀)
    (hab : 2 ^ K * a < b) (hxy : 2 ^ K * x₀ < y₀) {t : ℕ} {s : (ℤ × ℤ) × Inner} (ht : t < K)
    (hB : Base K p a b t s) (h : PhB K L a b x₀ y₀ t s) :
    PhB K L a b x₀ y₀ (t + 1) (gstep s) := by
  rcases h with h | h
  swap
  · exact Or.inr (phW_gstep ht hB h)
  have hpar := hB.parity ht
  obtain ⟨⟨A, B⟩, ⟨x, y, f0, g0, f1, g1⟩⟩ := s
  obtain ⟨-, -, hy, hBo, -⟩ := hB
  obtain ⟨hA, hx, rfl, rfl, hpot⟩ := h
  dsimp only at hpar hy hBo hA hx hpot
  have h2t : (1 : ℤ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
  have h2K : (1 : ℤ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have hA0 : 0 ≤ A := by
    by_contra hneg
    have : 2 ^ t * A < 0 := mul_neg_of_pos_of_neg (by positivity) (not_le.mp hneg)
    linarith
  have hx0 : 0 ≤ x := by
    by_contra hneg
    have : 2 ^ t * x < 0 := mul_neg_of_pos_of_neg (by positivity) (not_le.mp hneg)
    linarith
  have hAa : A ≤ a := by rw [← hA]; exact le_mul_of_one_le_left hA0 h2t
  have hxx : x ≤ x₀ := by rw [← hx]; exact le_mul_of_one_le_left hx0 h2t
  have haK : a ≤ 2 ^ K * a := le_mul_of_one_le_left ha h2K
  have hxK : x₀ ≤ 2 ^ K * x₀ := le_mul_of_one_le_left hx₀ h2K
  obtain ⟨A', x', h | h | h⟩ := gstep_spec f0 g0 f1 g1 hpar hBo hy
  · obtain ⟨rfl, rfl, heq⟩ := h
    rw [heq]
    refine Or.inl ⟨by rw [pow_succ]; linarith, by rw [pow_succ]; linarith, rfl, rfl, ?_⟩
    dsimp only
    by_cases hA0' : A' = 0
    · exact Or.inl hA0'
    · have := len_succ_le (x := 2 * A') (y := A') (by omega) (by omega)
      exact Or.inr (by omega)
  · -- the swap: the new `A` is `(b - A) / 2` and the new `B` is the old `A`
    obtain ⟨hx1, hlt, hx', hA', heq⟩ := h
    rw [heq]
    right
    unfold PhW
    dsimp only
    have hpow : (2 : ℤ) ^ (K - (t + 1)) * 2 ≤ 2 ^ K := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hD : (0 : ℤ) < 2 ^ (K - (t + 1)) := by positivity
    generalize (2 : ℤ) ^ (K - (t + 1)) = D at *
    have h1 : D * 2 * A ≤ 2 ^ K * a := mul_le_mul hpow hAa hA0 (by positivity)
    have h2 : D * 2 * x ≤ 2 ^ K * x₀ := mul_le_mul hpow hxx hx0 (by positivity)
    have hAB : A < B := by linarith
    have := len_succ_le (x := B) (y := A') (by omega) (by omega)
    exact ⟨by omega, by omega, by linarith, by linarith, by omega⟩
  · obtain ⟨hx1, hle, -⟩ := h
    linarith

/-- **Bit reduction when `b` dominates `a`** (Lemma 32). -/
theorem bitReduction_distB {K p : ℕ} {a b x₀ y₀ : ℤ} (ha : 0 ≤ a) (hx₀ : 0 ≤ x₀)
    (hab : 2 ^ K * a < b) (hxy : 2 ^ K * x₀ < y₀)
    (hbase : Base K p a b 0 ((a, b), ⟨x₀, y₀, 1, 0, 0, 1⟩)) :
    (gstep^[K] ((a, b), ⟨x₀, y₀, 1, 0, 0, 1⟩)).1.1 = 0 ∨
      len (gstep^[K] ((a, b), ⟨x₀, y₀, 1, 0, 0, 1⟩)).1.1 +
        len (gstep^[K] ((a, b), ⟨x₀, y₀, 1, 0, 0, 1⟩)).1.2 + K ≤ len a + len b := by
  have h := phase_iterate hbase (PhB K (len a + len b) a b x₀ y₀)
    (Or.inl ⟨by simp, by simp, rfl, rfl, Or.inr le_rfl⟩)
    fun _ _ => phB_gstep ha hx₀ hab hxy
  rcases h with h | h
  · exact h.2.2.2.2
  · exact Or.inr h.2.2.2.2

/-! ### Operands of similar sizes: wrong comparisons can happen -/

/-- Both values are below `2 ^ (p + 2)` in absolute value. This is stable. -/
def PhQ (p : ℕ) (A B : ℤ) : Prop :=
  -(4 * 2 ^ p) < A ∧ A < 4 * 2 ^ p ∧ -(4 * 2 ^ p) < B ∧ B < 4 * 2 ^ p

/-- One value is at least `2 ^ (p + 2)` and the other is in `(-2 ^ (p + 1), 0]`. -/
def PhP (p : ℕ) (A B : ℤ) : Prop :=
  (4 * 2 ^ p ≤ B ∧ -(2 * 2 ^ p) < A ∧ A ≤ 0) ∨ (4 * 2 ^ p ≤ A ∧ -(2 * 2 ^ p) < B ∧ B ≤ 0)

/-- The invariant for operands of similar sizes: `A = 0`; or no wrong comparison has
happened, the values are positive and one bit was removed per step; or a wrong comparison
has happened, and either both values are small or the round has already removed `K` bits and
`PhP` holds. -/
def PhC (K p L : ℕ) (mn : ℤ) (t : ℕ) (s : (ℤ × ℤ) × Inner) : Prop :=
  s.1.1 = 0 ∨
    (0 < s.1.1 ∧ 0 < s.1.2 ∧ len s.1.1 + len s.1.2 + t ≤ L ∧ (s.1.1 ≤ mn ∨ s.1.2 ≤ mn)) ∨
    PhQ p s.1.1 s.1.2 ∨ (PhP p s.1.1 s.1.2 ∧ len s.1.1 + len s.1.2 + K ≤ L)

theorem phC_gstep {K p L : ℕ} {a b mn : ℤ} (hmax : p + K + 2 + len mn ≤ L)
    {t : ℕ} {s : (ℤ × ℤ) × Inner} (ht : t < K) (hB : Base K p a b t s)
    (h : PhC K p L mn t s) : PhC K p L mn (t + 1) (gstep s) := by
  have hpar := hB.parity ht
  obtain ⟨⟨A, B⟩, ⟨x, y, f0, g0, f1, g1⟩⟩ := s
  obtain ⟨-, -, hy, hBo, hA1, hA2, hB1, hB2, -⟩ := hB
  dsimp only at hpar hy hBo hA1 hA2 hB1 hB2 h
  unfold PhC PhQ PhP at h ⊢
  dsimp only at h
  have hlen1 : ∀ z : ℤ, -(2 * 2 ^ p) < z → z < 2 * 2 ^ p → len z ≤ p + 1 := fun z h1 h2 =>
    len_le_of_lt (by rw [pow_succ]; linarith) (by rw [pow_succ]; linarith)
  have hE : (0 : ℤ) < 2 ^ p := by positivity
  have he : (0 : ℤ) ≤ 2 ^ (p - K) := by positivity
  generalize (2 : ℤ) ^ p = E at *
  generalize (2 : ℤ) ^ (p - K) = e at *
  obtain ⟨A', x', hs | hs | hs⟩ := gstep_spec f0 g0 f1 g1 hpar hBo hy
  · -- halving
    obtain ⟨hx, hA, heq⟩ := hs
    rw [heq]
    dsimp only
    rcases h with hZ | ⟨hA0, hB0, hpot, hmn⟩ | ⟨q1, q2, q3, q4⟩ | ⟨hP, hgood⟩
    · exact Or.inl (by omega)
    · have := len_succ_le (x := A) (y := A') (by omega) (by omega)
      exact Or.inr <| Or.inl ⟨by omega, hB0, by omega, by omega⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨by linarith, by linarith, q3, q4⟩
    · have hl := len_mono (x := A) (y := A') (by omega)
      rcases hP with ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩
      · exact Or.inr <| Or.inr <| Or.inr ⟨Or.inl ⟨p1, by linarith, by linarith⟩, by omega⟩
      · by_cases h4 : 4 * E ≤ A'
        · exact Or.inr <| Or.inr <| Or.inr ⟨Or.inr ⟨h4, p2, p3⟩, by omega⟩
        · exact Or.inr <| Or.inr <| Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩
  · -- the approximations say `a < b`: swap, then subtract
    obtain ⟨hx1, hlt, hx, hA, heq⟩ := hs
    rw [heq]
    dsimp only
    have hexy : e * x ≤ e * y := mul_le_mul_of_nonneg_left hlt.le he
    rcases h with hZ | ⟨hA0, hB0, hpot, hmn⟩ | ⟨q1, q2, q3, q4⟩ | ⟨hP, hgood⟩
    · omega
    · by_cases hAB : A < B
      · have := len_succ_le (x := B) (y := A') (by omega) (by omega)
        exact Or.inr <| Or.inl ⟨by omega, hA0, by omega, Or.inr (by omega)⟩
      · -- a wrong comparison: `0 ≤ A - B ≤ 2 ^ (p + 1)`
        have hd : A - B ≤ 2 * E := by linarith
        by_cases h4 : A < 4 * E
        · exact Or.inr <| Or.inr <| Or.inl ⟨by linarith, by linarith, by linarith, h4⟩
        · have l1 := hlen1 A' (by linarith) (by linarith)
          have hA2B : A ≤ 2 * B := by linarith
          have l2 := len_le_succ (x := A) (y := B) (by omega)
          have l3 := len_mono (x := mn) (y := B) (by omega)
          exact Or.inr <| Or.inr <| Or.inr
            ⟨Or.inl ⟨by linarith, by linarith, by linarith⟩, by omega⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨by linarith, by linarith, q1, q2⟩
    · rcases hP with ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩
      · have hA'B : A' ≤ B := by linarith
        have hl := len_mono (x := B) (y := A') (by omega)
        by_cases h4 : 4 * E ≤ A'
        · exact Or.inr <| Or.inr <| Or.inr ⟨Or.inr ⟨h4, p2, p3⟩, by omega⟩
        · exact Or.inr <| Or.inr <| Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩
      · linarith
  · -- the approximations say `b ≤ a`: subtract
    obtain ⟨hx1, hle, hx, hA, heq⟩ := hs
    rw [heq]
    dsimp only
    have hexy : e * y ≤ e * x := mul_le_mul_of_nonneg_left hle he
    rcases h with hZ | ⟨hA0, hB0, hpot, hmn⟩ | ⟨q1, q2, q3, q4⟩ | ⟨hP, hgood⟩
    · omega
    · by_cases hAB : B ≤ A
      · by_cases hA'0 : A' = 0
        · exact Or.inl hA'0
        · have := len_succ_le (x := A) (y := A') (by omega) (by omega)
          exact Or.inr <| Or.inl ⟨by omega, hB0, by omega, Or.inr (by omega)⟩
      · -- a wrong comparison: `0 < B - A ≤ 2 ^ (p + 1)`
        have hd : B - A ≤ 2 * E := by linarith
        by_cases h4 : B < 4 * E
        · exact Or.inr <| Or.inr <| Or.inl ⟨by linarith, by linarith, by linarith, h4⟩
        · have l1 := hlen1 A' (by linarith) (by linarith)
          have hB2A : B ≤ 2 * A := by linarith
          have l2 := len_le_succ (x := B) (y := A) (by omega)
          have l3 := len_mono (x := mn) (y := A) (by omega)
          exact Or.inr <| Or.inr <| Or.inr
            ⟨Or.inl ⟨by linarith, by linarith, by linarith⟩, by omega⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨by linarith, by linarith, q3, q4⟩
    · rcases hP with ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩
      · linarith
      · have hA'A : A' ≤ A := by linarith
        have hl := len_mono (x := A) (y := A') (by omega)
        by_cases h4 : 4 * E ≤ A'
        · exact Or.inr <| Or.inr <| Or.inr ⟨Or.inr ⟨h4, p2, p3⟩, by omega⟩
        · exact Or.inr <| Or.inr <| Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Bit reduction for operands of similar sizes** (Theorem 42): here `p + K + 2` is the
larger of the two bit lengths, and the smaller one is more than `p + 1`. -/
theorem bitReduction_close {K p : ℕ} {a b x₀ y₀ : ℤ} (ha : 0 ≤ a) (hb : 0 < b)
    (hclose : 2 * p + 4 + K ≤ len a + len b)
    (hmax : p + K + 2 + len (min a b) ≤ len a + len b)
    (hbase : Base K p a b 0 ((a, b), ⟨x₀, y₀, 1, 0, 0, 1⟩)) :
    (gstep^[K] ((a, b), ⟨x₀, y₀, 1, 0, 0, 1⟩)).1.1 = 0 ∨
      len (gstep^[K] ((a, b), ⟨x₀, y₀, 1, 0, 0, 1⟩)).1.1 +
        len (gstep^[K] ((a, b), ⟨x₀, y₀, 1, 0, 0, 1⟩)).1.2 + K ≤ len a + len b := by
  have h0 : PhC K p (len a + len b) (min a b) 0 ((a, b), ⟨x₀, y₀, 1, 0, 0, 1⟩) := by
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    · exact Or.inr <| Or.inl ⟨lt_of_le_of_ne ha (Ne.symm ha0), hb, le_rfl,
        by rcases le_total a b with h | h <;> simp [h]⟩
  have h := phase_iterate hbase (PhC K p (len a + len b) (min a b)) h0
    fun _ _ => phC_gstep hmax
  rcases h with h | h | ⟨q1, q2, q3, q4⟩ | h
  · exact Or.inl h
  · exact Or.inr h.2.2.1
  · have l1 := len_le_of_lt (x := (gstep^[K] ((a, b), ⟨x₀, y₀, 1, 0, 0, 1⟩)).1.1) (j := p + 2)
      (by rw [pow_succ, pow_succ]; linarith) (by rw [pow_succ, pow_succ]; linarith)
    have l2 := len_le_of_lt (x := (gstep^[K] ((a, b), ⟨x₀, y₀, 1, 0, 0, 1⟩)).1.2) (j := p + 2)
      (by rw [pow_succ, pow_succ]; linarith) (by rw [pow_succ, pow_succ]; linarith)
    exact Or.inr (by omega)
  · exact Or.inr h.2

end Bingcd.Pornin
