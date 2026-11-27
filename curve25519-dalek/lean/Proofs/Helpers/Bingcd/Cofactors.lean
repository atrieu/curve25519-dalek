module
public import Proofs.Helpers.Bingcd.OnLimbs

/-! # Pornin's optimized binary gcd with the cofactors in a field

The cofactors `u`, `v` of the algorithm only matter modulo the modulus, and only go through
linear combinations. `bingcd.rs` keeps them as field elements and applies the rows of the
transition matrix to them without the division by `2 ^ K`: the factor `2 ^ (K * r + T)` they pick
up over `r` rounds and `T` last steps is removed by the value they start from.

This file defines that run, with the operands on limbs as in `Proofs/Helpers/Bingcd/OnLimbs.lean`
and the cofactors in a commutative ring, and shows that for a prime modulus `p` the final
cofactor is `u * 2 ^ (K * r + T) / y`, where `u` is the cofactor the run starts from (and `0`
when `y` is `0`). -/

@[expose] public section

namespace Bingcd.Pornin

/-! ### The matrix of the inner loop on words -/

/-- The rows of the matrix after `t` steps on words, from any two words, have absolute sums at
most `2 ^ t`. -/
theorem innerW_matBound {w t : ℕ} (hw : t + 2 ≤ w) (x y : Word w) :
    |(InnerW.step^[t] ⟨x, y, 1, 0, 0, 1⟩).f0.toInt| +
        |(InnerW.step^[t] ⟨x, y, 1, 0, 0, 1⟩).g0.toInt| ≤ 2 ^ t ∧
      |(InnerW.step^[t] ⟨x, y, 1, 0, 0, 1⟩).f1.toInt| +
        |(InnerW.step^[t] ⟨x, y, 1, 0, 0, 1⟩).g1.toInt| ≤ 2 ^ t := by
  obtain ⟨-, -, h0, h1, h2, h3⟩ :=
    refines_iterate hw (refines_identity (by omega) x y) (le_refl t)
  rw [h0, h1, h2, h3]
  exact matBound_iterate (x.toNat : ℤ) y.toNat t

/-! ### A limb of a row of cofactors -/

/-- A limb `c + a * f + b * g` of a row of cofactors, for signed words `f` and `g`, computed on
longer words with wrapping operations: when the value is in the unsigned range, it is exact. -/
theorem toNat_add_mul_signExtend {w v : ℕ} (hwv : w ≤ v) (c : Word v) (a b f g : Word w)
    (h0 : 0 ≤ (c.toNat : ℤ) + a.toNat * f.toInt + b.toNat * g.toInt)
    (h1 : (c.toNat : ℤ) + a.toNat * f.toInt + b.toNat * g.toInt < 2 ^ v) :
    ((c + a.setWidth v * f.signExtend v + b.setWidth v * g.signExtend v).toNat : ℤ) =
      c.toNat + a.toNat * f.toInt + b.toNat * g.toInt := by
  have hofInt : ∀ {u : ℕ} (_ : u ≤ v) (x : Word u),
      x.setWidth v = BitVec.ofInt v (x.toNat : ℤ) := by
    intro u hu x
    apply BitVec.eq_of_toNat_eq
    have hx : x.toNat < 2 ^ v := lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num) hu)
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, Nat.mod_eq_of_lt hx,
      Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hx), Int.toNat_natCast]
  have hc : c = BitVec.ofInt v (c.toNat : ℤ) := by
    rw [← hofInt le_rfl, BitVec.setWidth_eq]
  have e : c + a.setWidth v * f.signExtend v + b.setWidth v * g.signExtend v =
      BitVec.ofInt v ((c.toNat : ℤ) + a.toNat * f.toInt + b.toNat * g.toInt) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_mul, ← hc,
      ← hofInt hwv, ← hofInt hwv]
    rfl
  rw [e, BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (by exact_mod_cast h1)]
  exact Int.toNat_of_nonneg h0

/-- The word that `±f` is selected into has the signed value `±f`, for `f` away from the most
negative word. -/
theorem toInt_select_neg {w K : ℕ} (hw : K + 2 ≤ w) {f : Word w} (hf : |f.toInt| ≤ 2 ^ K)
    (neg : Bool) : (Word.select neg (-f) f).toInt = bif neg then -f.toInt else f.toInt := by
  cases neg
  · simp
  · simp only [Word.select_true, Bool.cond_true]
    exact Word.toInt_neg_of_inSRange (Word.inSRange_of_abs_le hw (by rwa [abs_neg]))

/-! ### The run with the cofactors in a ring -/

section Ring

variable {R : Type*} [CommRing R]

/-- `u * f + v * g` for a row `(f, g)` of the transition matrix, read as signed integers, and
negated when `neg` is set. There is no division by `2 ^ K`. -/
def cofR {w : ℕ} (u v : R) (f g : Word w) (neg : Bool) : R :=
  bif neg then -(u * (f.toInt : R) + v * (g.toInt : R))
  else u * (f.toInt : R) + v * (g.toInt : R)

/-- One round with the cofactors in a ring: `K` steps of the inner loop on the approximations
of the operands, then the rows of the matrix applied to the operands (`applyRow`) and, without
division, to the cofactors. -/
def roundR {w n : ℕ} (K : ℕ) (s : Limbs w (n + 1) × R × Limbs w (n + 1) × R) :
    Limbs w (n + 1) × R × Limbs w (n + 1) × R :=
  let p := max (max (Limbs.bitLen s.1) (Limbs.bitLen s.2.2.1)) (2 * K + 2) - K - 2
  let t := InnerW.step^[K] ⟨approxL K p s.1, approxL K p s.2.2.1, 1, 0, 0, 1⟩
  let ra := applyRow s.1 s.2.2.1 t.f0 t.g0 K
  let rb := applyRow s.1 s.2.2.1 t.f1 t.g1 K
  (ra.1, cofR s.2.1 s.2.2.2 t.f0 t.g0 ra.2, rb.1, cofR s.2.1 s.2.2.2 t.f1 t.g1 rb.2)

/-- The last steps with the cofactors in a ring: `T` steps of the inner loop on the least
significant limbs of `a` and `b`, then the second row of the matrix applied to the cofactors.
The result is the final `v`. -/
def tailR {w n : ℕ} (T : ℕ) (s : Limbs w (n + 1) × R × Limbs w (n + 1) × R) : R :=
  let t := InnerW.step^[T] ⟨s.1[0], s.2.2.1[0], 1, 0, 0, 1⟩
  cofR s.2.1 s.2.2.2 t.f1 t.g1 false

/-- The final cofactor `v` of `r` rounds and `T` last steps on the operands `y` and `m`, from
the cofactors `u` and `0`. -/
def porninDivR {w n : ℕ} (K r T : ℕ) (m : Limbs w (n + 1)) (u : R) (y : Limbs w (n + 1)) : R :=
  tailR T ((roundR K)^[r] (y, u, m, 0))

end Ring

/-! ### The run computes the integer-level one -/

/-- A state with cofactors in `ZMod m` represents an integer-level state. -/
def RelR (m : ℕ) {w n : ℕ} (s : Limbs w (n + 1) × ZMod m × Limbs w (n + 1) × ZMod m)
    (t : ℕ × ℕ × ℕ × ℕ) : Prop :=
  s.1.toNat = t.1 ∧ s.2.1 = (t.2.1 : ZMod m) ∧ s.2.2.1.toNat = t.2.2.1 ∧
    s.2.2.2 = (t.2.2.2 : ZMod m)

theorem natCast_emod_toNat {m : ℕ} (hm : 0 < m) (x : ℤ) :
    (((x % m).toNat : ℕ) : ZMod m) = (x : ZMod m) := by
  have h : ((x % (m : ℤ)).toNat : ℤ) = x % m :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  rw [← Int.cast_natCast, h, ZMod.intCast_mod]

/-- **A round with the cofactors in `ZMod m` computes the integer-level round.** -/
theorem roundR_spec {w n K : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) {m : ℕ} (hm : 0 < m)
    {s : Limbs w (n + 1) × ZMod m × Limbs w (n + 1) × ZMod m} {t : ℕ × ℕ × ℕ × ℕ}
    (h : RelR m s t) (hb : t.2.2.1 % 2 = 1) : RelR m (roundR K s) (round m K t) := by
  obtain ⟨a, u, b, v⟩ := s
  obtain ⟨ta, U, tb, V⟩ := t
  obtain ⟨h1, h2, h3, h4⟩ := h
  dsimp only at h1 h2 h3 h4 hb
  subst h1 h2 h3 h4
  obtain ⟨p, hp⟩ : ∃ p, p = max (max a.toNat.size b.toNat.size) (2 * K + 2) - K - 2 := ⟨_, rfl⟩
  have hbase := base_zero hK (by omega : K ≤ p) a.toNat hb
  have hfin := base_iterate hbase (le_refl K)
  have hsnd := gstep_iterate_snd K
    (((a.toNat : ℤ), (b.toNat : ℤ)), (⟨approx K p a.toNat, approx K p b.toNat, 1, 0, 0, 1⟩ : Inner))
  have href := innerW_spec (w := w) hK hw a.toNat b.toNat hp
  have hmat := matBound_iterate (approx K p a.toNat : ℤ) (approx K p b.toNat) K
  have hinit : (⟨approxL K p a, approxL K p b, 1, 0, 0, 1⟩ : InnerW w) =
      InnerW.init w K p a.toNat b.toNat := by
    rw [InnerW.init, approxL_eq hw a (Nat.size_le.mp (by omega)),
      approxL_eq hw b (Nat.size_le.mp (by omega))]
  dsimp only at hsnd
  unfold round roundR RelR
  dsimp only
  simp only [Limbs.bitLen_eq]
  rw [← hp, hinit, ← hsnd]
  rw [← hsnd] at href hmat
  generalize gstep^[K] (((a.toNat : ℤ), (b.toNat : ℤ)),
    ⟨approx K p a.toNat, approx K p b.toNat, 1, 0, 0, 1⟩) = G at *
  generalize InnerW.step^[K] (InnerW.init w K p a.toNat b.toNat) = s at *
  obtain ⟨⟨A, B⟩, ⟨x, y, f0, g0, f1, g1⟩⟩ := G
  obtain ⟨sa, sb, sf0, sg0, sf1, sg1⟩ := s
  obtain ⟨-, -, -, -, -, -, -, -, hl1, hl2⟩ := hfin
  obtain ⟨-, -, rfl, rfl, rfl, rfl⟩ := href
  obtain ⟨hm0, hm1⟩ := hmat
  dsimp only at hl1 hl2 hm0 hm1 ⊢
  have h2K : (2 : ℤ) ^ K ≠ 0 := by positivity
  rw [← hl1, ← hl2, Int.mul_ediv_cancel_left _ h2K, Int.mul_ediv_cancel_left _ h2K]
  obtain ⟨ha1, ha2⟩ := applyRow_spec (by omega : K + 2 ≤ w) a b hm0 hl1
  obtain ⟨hb1, hb2⟩ := applyRow_spec (by omega : K + 2 ≤ w) a b hm1 hl2
  refine ⟨Int.natCast_inj.mp (by rw [ha1, Int.natCast_natAbs]), ?_,
    Int.natCast_inj.mp (by rw [hb1, Int.natCast_natAbs]), ?_⟩
  · rw [ha2, natCast_emod_toNat hm, cofR]
    by_cases hA : A < 0 <;> simp [hA]
  · rw [hb2, natCast_emod_toNat hm, cofR]
    by_cases hB : B < 0 <;> simp [hB]

/-- The rounds from `(y, x, m, 0)` keep `b` odd. -/
theorem round_iterate_odd {m K : ℕ} (hK : 1 ≤ K) (hm : 1 < m) (hodd : m % 2 = 1) {x : ℕ}
    (hx : x < m) (y i : ℕ) : ((round m K)^[i] (y, x, m, 0)).2.2.1 % 2 = 1 := by
  rw [← scale_init hx, round_iterate_scale (by omega)]
  exact (rinv_iterate (y := y) hK hm hodd i).1

/-- **The rounds with the cofactors in `ZMod m` compute the integer-level ones.** -/
theorem roundR_iterate {w n K : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) {m : ℕ} (hm : 1 < m)
    (hodd : m % 2 = 1) (mL : Limbs w (n + 1)) (hmL : mL.toNat = m) (y : Limbs w (n + 1)) {x : ℕ}
    (hx : x < m) (i : ℕ) :
    RelR m ((roundR K)^[i] (y, (x : ZMod m), mL, 0)) ((round m K)^[i] (y.toNat, x, m, 0)) := by
  induction i with
  | zero => exact ⟨rfl, rfl, hmL, by simp⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact roundR_spec hK hw (by omega) ih (round_iterate_odd hK hm hodd hx y.toNat i)

/-- **The last steps with the cofactors in `ZMod m` compute the integer-level ones**, for
operands that fit in a word, or `a = 0`. -/
theorem tailR_spec {w n T : ℕ} (hT : T + 2 ≤ w) {m : ℕ} (hm : 0 < m)
    {s : Limbs w (n + 1) × ZMod m × Limbs w (n + 1) × ZMod m} {t : ℕ × ℕ × ℕ × ℕ}
    (h : RelR m s t) (hab : t.1 = 0 ∨ (t.1 < 2 ^ w ∧ t.2.2.1 < 2 ^ w)) :
    tailR T s = ((tail m T t).2 : ZMod m) := by
  obtain ⟨a, u, b, v⟩ := s
  obtain ⟨ta, U, tb, V⟩ := t
  obtain ⟨h1, h2, h3, h4⟩ := h
  dsimp only at h1 h2 h3 h4 hab
  subst h1 h2 h3 h4
  obtain ⟨hf1, hg1, -⟩ := innerW_tail (T := T) hT a b hab
  unfold tailR tail cofR
  dsimp only
  rw [hf1, hg1, Bool.cond_false, natCast_emod_toNat hm]
  push_cast
  rfl

/-! ### The cofactors of a run on `a = 0` -/

/-- A round on `a = 0` and `v = 0` leaves them at `0`, and does not change `b`. -/
theorem round_zero (m K u b : ℕ) : round m K (0, u, b, 0) = (0, u % m, b, 0) := by
  have ha : ((approx K (max (max (0 : ℕ).size b.size) (2 * K + 2) - K - 2) 0 : ℕ) : ℤ) = 0 := by
    simp [approx]
  unfold round
  dsimp only
  rw [ha, step_iterate_zero]
  simp only [CharP.cast_eq_zero, mul_one, mul_zero, add_zero, Int.zero_ediv, Int.natAbs_zero,
    lt_self_iff_false, ↓reduceIte, zero_add, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
    false_and, not_false_eq_true, mul_div_cancel_right₀, Int.natAbs_natCast, zero_mul, neg_zero,
    ite_self, Int.zero_emod, Int.toNat_zero, Prod.mk.injEq, and_true, true_and]
  rw [← Int.natCast_mod, Int.toNat_natCast]

theorem round_iterate_zero (m K u b i : ℕ) :
    ∃ u', (round m K)^[i] (0, u, b, 0) = (0, u', b, 0) := by
  induction i with
  | zero => exact ⟨u, rfl⟩
  | succ i ih =>
    obtain ⟨u', hu'⟩ := ih
    exact ⟨u' % m, by rw [Function.iterate_succ_apply', hu', round_zero]⟩

/-- The last steps on `a = 0` and `v = 0` end on `v = 0`. -/
theorem tail_zero (m T u b : ℕ) : (tail m T (0, u, b, 0)).2 = 0 := by
  unfold tail
  dsimp only
  rw [Nat.cast_zero, step_iterate_zero]
  simp

/-! ### Scaling, and operands that fit in a word -/

theorem tail_scale {m T : ℕ} (hm : 0 < m) (x : ℕ) (s : ℕ × ℕ × ℕ × ℕ) :
    tail m T (scale m x s) = ((tail m T s).1, x * (tail m T s).2 % m) := by
  obtain ⟨a, u, b, v⟩ := s
  unfold tail scale
  dsimp only
  refine Prod.ext rfl ?_
  have h := cofactor_scale hm x u v
    (Inner.step^[T] ⟨(a : ℤ), (b : ℤ), 1, 0, 0, 1⟩).f1
    (Inner.step^[T] ⟨(a : ℤ), (b : ℤ), 1, 0, 0, 1⟩).g1 1 False
  simpa using h

/-- After `r` rounds with `K * r + w + 1 ≥ 2 * ℓ(m)`, the operands fit in a word, unless `a`
is zero. -/
theorem round_iterate_fit {y m K w : ℕ} (hK : 1 ≤ K) (hm : 1 < m) (hodd : m % 2 = 1)
    (hy : y < m) {r : ℕ} (hfit : 2 * m.size ≤ K * r + w + 1) :
    ((round m K)^[r] (y, 1, m, 0)).1 = 0 ∨
      (((round m K)^[r] (y, 1, m, 0)).1 < 2 ^ w ∧
        ((round m K)^[r] (y, 1, m, 0)).2.2.1 < 2 ^ w) := by
  obtain ⟨hbo, -, -, -, -, -, hpot⟩ := rinv_iterate (y := y) hK hm hodd r
  rcases hpot with h | h
  · exact Or.inl h
  · have hy' := Nat.size_le_size hy.le
    have h1 := Nat.size_pos.mpr
      (by omega : 0 < ((round m K)^[r] (y, 1, m, 0)).2.2.1)
    by_cases h0 : ((round m K)^[r] (y, 1, m, 0)).1 = 0
    · exact Or.inl h0
    · have h2 := Nat.size_pos.mpr (Nat.pos_of_ne_zero h0)
      exact Or.inr ⟨Nat.size_le.mp (by omega), Nat.size_le.mp (by omega)⟩

/-! ### Correctness for a prime modulus -/

/-- **The final cofactor is the quotient, up to the power of two.** For a prime modulus `p` on
limbs, `y < p`, and a schedule of `r` rounds of `K` steps and `T` last steps with
`K * r + T ≥ 2 * ℓ(p) - 2` and `K * r + w + 1 ≥ 2 * ℓ(p)`: the run from the cofactor `u` ends on
`u * 2 ^ (K * r + T) / y` in `ZMod p`, which is `0` when `y` is `0`. -/
theorem porninDivR_spec {w n K r T : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) (hT : T + 2 ≤ w)
    {p : ℕ} [hp : Fact p.Prime] (hodd : p % 2 = 1) (mL : Limbs w (n + 1)) (hmL : mL.toNat = p)
    (y : Limbs w (n + 1)) (hy : y.toNat < p) (hfit : 2 * p.size ≤ K * r + w + 1)
    (hN : 2 * p.size ≤ K * r + T + 2) (u : ZMod p) :
    porninDivR K r T mL u y = u * 2 ^ (K * r + T) / (y.toNat : ZMod p) := by
  have hp1 := hp.out.one_lt
  have hp0 : 0 < p := by omega
  obtain ⟨x, hx, rfl⟩ : ∃ x : ℕ, x < p ∧ (x : ZMod p) = u :=
    ⟨u.val, ZMod.val_lt u, ZMod.natCast_zmod_val u⟩
  have hrel := roundR_iterate hK hw hp1 hodd mL hmL y hx r
  have hscale : (round p K)^[r] (y.toNat, x, p, 0) =
      scale p x ((round p K)^[r] (y.toNat, 1, p, 0)) := by
    rw [← scale_init hx, round_iterate_scale hp0]
  have hab := round_iterate_fit (w := w) hK hp1 hodd hy hfit
  have htail := tailR_spec (T := T) hT hp0 hrel (by rw [hscale]; exact hab)
  rw [porninDivR, htail, hscale, tail_scale hp0]
  dsimp only
  rw [ZMod.natCast_mod, Nat.cast_mul]
  by_cases hy0 : y.toNat = 0
  · -- `y = 0`: the cofactor `v` stays at `0`
    obtain ⟨u', hu'⟩ := round_iterate_zero p K 1 p r
    rw [hy0, hu', tail_zero]
    simp
  · have hc : Nat.gcd y.toNat p = 1 :=
      ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h =>
        absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hy0) h) (by omega)).symm
    obtain ⟨-, -, hv⟩ := rinv_tail (T := T) hp0 hy hN (rinv_iterate (y := y.toNat) hK hp1 hodd r)
    rw [hc] at hv
    have hv' : ((tail p T ((round p K)^[r] (y.toNat, 1, p, 0))).2 : ZMod p) * (y.toNat : ZMod p) =
        2 ^ (K * r + T) := by
      have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hv
      push_cast at this
      simpa using this
    have hyz : (y.toNat : ZMod p) ≠ 0 := fun h =>
      absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hy0) ((ZMod.natCast_eq_zero_iff _ _).mp h))
        (by omega)
    rw [eq_div_iff hyz, mul_assoc, hv']

end Bingcd.Pornin
