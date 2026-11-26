module
public import Proofs.Helpers.Bingcd.Bits
public import Proofs.Helpers.Bingcd.Schedule
public import Proofs.Helpers.Bingcd.Signed

/-! # Pornin's optimized binary gcd on words and limbs

The inner loop of Pornin's algorithm on `w`-bit words, without branches: the approximations
are unsigned words, the entries of the transition matrix are signed words, and the two
decisions of a step (is `ā` odd, is `ā < b̄`) drive selections rather than control flow.

For `K` inner steps and `w ≥ 2 * K + 2`, the approximations fit in a word, and the entries
of the matrix stay in `[-2 ^ K, 2 ^ K]` (`matBound_iterate`), so that no signed operation
overflows. The rest of a round is on multi-limb integers. The integer-level algorithm this
file refines is in `Proofs/Helpers/Bingcd/Schedule.lean` and the files it imports. -/

@[expose] public section

namespace Bingcd.Pornin

/-! ### The inner loop on words -/

/-- The state of the inner loop on `w`-bit words: the approximations are unsigned, the
entries of the transition matrix are signed. -/
structure InnerW (w : ℕ) where
  /-- The approximation of `a`. -/
  abar : Word w
  /-- The approximation of `b`. -/
  bbar : Word w
  /-- The entry `f₀` of the transition matrix. -/
  f0 : Word w
  /-- The entry `g₀` of the transition matrix. -/
  g0 : Word w
  /-- The entry `f₁` of the transition matrix. -/
  f1 : Word w
  /-- The entry `g₁` of the transition matrix. -/
  g1 : Word w

/-- One branch-free step of the inner loop. The rows are swapped when `ā` is odd and
`ā < b̄` (the borrow of `ā - b̄`), the second row is subtracted from the first when `ā` is
odd, then `ā` is halved and the second row of the matrix is doubled. -/
def InnerW.step {w : ℕ} (s : InnerW w) : InnerW w :=
  let odd : Bool := decide (s.abar.toNat % 2 = 1)
  let swap : Bool := odd && (Word.subb s.abar s.bbar false).2
  let a₁ := Word.select swap s.bbar s.abar
  let b₁ := Word.select swap s.abar s.bbar
  let f0₁ := Word.select swap s.f1 s.f0
  let g0₁ := Word.select swap s.g1 s.g0
  let f1₁ := Word.select swap s.f0 s.f1
  let g1₁ := Word.select swap s.g0 s.g1
  ⟨(a₁ - Word.select odd b₁ 0) >>> 1, b₁, f0₁ - Word.select odd f1₁ 0,
    g0₁ - Word.select odd g1₁ 0, f1₁ + f1₁, g1₁ + g1₁⟩

/-- A word state represents an integer state. -/
def Refines {w : ℕ} (s : InnerW w) (t : Inner) : Prop :=
  (s.abar.toNat : ℤ) = t.abar ∧ (s.bbar.toNat : ℤ) = t.bbar ∧ s.f0.toInt = t.f0 ∧
    s.g0.toInt = t.g0 ∧ s.f1.toInt = t.f1 ∧ s.g1.toInt = t.g1

theorem toNat_sub_shiftRight_one {w : ℕ} {x y : Word w} (h : y.toNat ≤ x.toNat) :
    (((x - y) >>> 1).toNat : ℤ) = ((x.toNat : ℤ) - y.toNat) / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub_of_le h]
  omega

theorem refines_step {w K j : ℕ} (hw : K + 2 ≤ w) (hj : j < K) {s : InnerW w} {t : Inner}
    (h : Refines s t) (hM : MatBound j t) : Refines s.step t.step := by
  have hM' := matBound_step hM
  obtain ⟨a, b, f0, g0, f1, g1⟩ := s
  obtain ⟨ta, tb, tf0, tg0, tf1, tg1⟩ := t
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  have hpow : (2 : ℤ) ^ (j + 1) ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
  have hr : ∀ z z' : ℤ, |z| + |z'| ≤ 2 ^ (j + 1) → Word.InSRange w z ∧ Word.InSRange w z' :=
    fun z z' hz => ⟨Word.inSRange_of_abs_le hw (by linarith [abs_nonneg z']),
      Word.inSRange_of_abs_le hw (by linarith [abs_nonneg z])⟩
  by_cases h1 : a.toNat % 2 = 0
  · -- halving
    have hstep : Inner.step ⟨a.toNat, b.toNat, f0.toInt, g0.toInt, f1.toInt, g1.toInt⟩ =
        ⟨(a.toNat : ℤ) / 2, b.toNat, f0.toInt, g0.toInt, 2 * f1.toInt, 2 * g1.toInt⟩ := by
      simp [Inner.step, show (a.toNat : ℤ) % 2 = 0 by omega]
    have hstepW : InnerW.step ⟨a, b, f0, g0, f1, g1⟩ =
        ⟨a >>> 1, b, f0, g0, f1 + f1, g1 + g1⟩ := by
      simp [InnerW.step, h1]
    rw [hstep] at hM' ⊢
    rw [hstepW]
    obtain ⟨hf, hg⟩ := hr _ _ hM'.2
    exact ⟨by simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow], rfl, rfl, rfl,
      Word.toInt_add_self hf, Word.toInt_add_self hg⟩
  · by_cases h2 : a.toNat < b.toNat
    · -- swap, then subtract
      have hstep : Inner.step ⟨a.toNat, b.toNat, f0.toInt, g0.toInt, f1.toInt, g1.toInt⟩ =
          ⟨((b.toNat : ℤ) - a.toNat) / 2, a.toNat, f1.toInt - f0.toInt, g1.toInt - g0.toInt,
            2 * f0.toInt, 2 * g0.toInt⟩ := by
        simp [Inner.step, show ¬(a.toNat : ℤ) % 2 = 0 by omega,
          show (a.toNat : ℤ) < b.toNat by omega]
      have hstepW : InnerW.step ⟨a, b, f0, g0, f1, g1⟩ =
          ⟨(b - a) >>> 1, a, f1 - f0, g1 - g0, f0 + f0, g0 + g0⟩ := by
        simp [InnerW.step, Word.subb_snd, show a.toNat % 2 = 1 by omega, h2]
      rw [hstep] at hM' ⊢
      rw [hstepW]
      obtain ⟨hf, hg⟩ := hr _ _ hM'.1
      obtain ⟨hf', hg'⟩ := hr _ _ hM'.2
      exact ⟨toNat_sub_shiftRight_one h2.le, rfl, Word.toInt_sub_of_inSRange hf,
        Word.toInt_sub_of_inSRange hg, Word.toInt_add_self hf', Word.toInt_add_self hg'⟩
    · -- subtract
      have hstep : Inner.step ⟨a.toNat, b.toNat, f0.toInt, g0.toInt, f1.toInt, g1.toInt⟩ =
          ⟨((a.toNat : ℤ) - b.toNat) / 2, b.toNat, f0.toInt - f1.toInt, g0.toInt - g1.toInt,
            2 * f1.toInt, 2 * g1.toInt⟩ := by
        simp [Inner.step, show ¬(a.toNat : ℤ) % 2 = 0 by omega,
          show ¬(a.toNat : ℤ) < b.toNat by omega]
      have hstepW : InnerW.step ⟨a, b, f0, g0, f1, g1⟩ =
          ⟨(a - b) >>> 1, b, f0 - f1, g0 - g1, f1 + f1, g1 + g1⟩ := by
        simp [InnerW.step, Word.subb_snd, show a.toNat % 2 = 1 by omega, h2]
      rw [hstep] at hM' ⊢
      rw [hstepW]
      obtain ⟨hf, hg⟩ := hr _ _ hM'.1
      obtain ⟨hf', hg'⟩ := hr _ _ hM'.2
      exact ⟨toNat_sub_shiftRight_one (by omega), rfl, Word.toInt_sub_of_inSRange hf,
        Word.toInt_sub_of_inSRange hg, Word.toInt_add_self hf', Word.toInt_add_self hg'⟩

theorem refines_iterate {w K : ℕ} (hw : K + 2 ≤ w) {s : InnerW w} {x y : ℤ}
    (h : Refines s ⟨x, y, 1, 0, 0, 1⟩) {t : ℕ} (ht : t ≤ K) :
    Refines (InnerW.step^[t] s) (Inner.step^[t] ⟨x, y, 1, 0, 0, 1⟩) := by
  induction t with
  | zero => exact h
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact refines_step hw (by omega : t < K) (ih (by omega)) (matBound_iterate x y t)

/-! ### The approximations fit in a word -/

theorem approx_lt_two_pow {K p a : ℕ} (h : a < 2 ^ (p + K + 2)) :
    approx K p a < 2 ^ (2 * K + 2) := by
  have hq : a / 2 ^ p < 2 ^ (K + 2) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact lt_of_lt_of_eq h (by congr 1; omega)
  have hr := Nat.mod_lt a (by positivity : 0 < 2 ^ K)
  have h1 : 2 ^ K * (a / 2 ^ p) ≤ 2 ^ K * (2 ^ (K + 2) - 1) := Nat.mul_le_mul_left _ (by omega)
  have e : 2 ^ (2 * K + 2) = 2 ^ K * 2 ^ (K + 2) := by rw [← pow_add]; congr 1; omega
  have h2 : 2 ^ K * (2 ^ (K + 2) - 1) + 2 ^ K = 2 ^ K * 2 ^ (K + 2) := by
    have : 1 ≤ 2 ^ (K + 2) := Nat.one_le_two_pow
    rw [Nat.mul_sub, Nat.mul_one]
    have := Nat.mul_le_mul_left (2 ^ K) this
    omega
  unfold approx
  omega

/-- The initial word state of a round: the approximations and the identity matrix. -/
def InnerW.init (w K p a b : ℕ) : InnerW w :=
  ⟨BitVec.ofNat w (approx K p a), BitVec.ofNat w (approx K p b), 1, 0, 0, 1⟩

theorem refines_init {w K p a b : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w)
    (ha : a < 2 ^ (p + K + 2)) (hb : b < 2 ^ (p + K + 2)) :
    Refines (InnerW.init w K p a b) ⟨approx K p a, approx K p b, 1, 0, 0, 1⟩ := by
  have hpow : 2 ^ (2 * K + 2) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have h16 : 2 ^ (2 * 1 + 2) ≤ 2 ^ (2 * K + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn : (1 : Word w).toNat = 1 := by
    change (BitVec.ofNat w 1).toNat = 1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : (1 : Word w).toInt = 1 := by
    rw [Word.toInt_eq_toNat_of_lt (by rw [hn]; omega), hn]
    rfl
  refine ⟨?_, ?_, h1, by simp [InnerW.init], by simp [InnerW.init], h1⟩
  · simp only [InnerW.init, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (approx_lt_two_pow ha) hpow)]
  · simp only [InnerW.init, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (approx_lt_two_pow hb) hpow)]

/-- **The inner loop on words computes the transition matrix of a round.** For `K ≥ 1` inner
steps on words of `w ≥ 2 * K + 2` bits, with `p` as in `round`, the signed values of the
matrix entries are those of the integer-level inner loop. -/
theorem innerW_spec {w K : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) (a b : ℕ) {p : ℕ}
    (hp : p = max (max a.size b.size) (2 * K + 2) - K - 2) :
    Refines (InnerW.step^[K] (InnerW.init w K p a b))
      (Inner.step^[K] ⟨approx K p a, approx K p b, 1, 0, 0, 1⟩) := by
  have hn : max (max a.size b.size) (2 * K + 2) = p + K + 2 := by omega
  have ha : a < 2 ^ (p + K + 2) := Nat.size_le.mp (by omega)
  have hb : b < 2 ^ (p + K + 2) := Nat.size_le.mp (by omega)
  exact refines_iterate (by omega) (refines_init hK hw ha hb) le_rfl

/-! ### Applying the matrix to the operands -/

/-- `|(a * f + b * g) / 2 ^ K|` and the sign of `(a * f + b * g) / 2 ^ K`, for multi-limb
`a`, `b` and a row `(f, g)` of the transition matrix. -/
def applyRow {w n : ℕ} (a b : Limbs w n) (f g : Word w) (K : ℕ) : Limbs w n × Bool :=
  let r := Limbs.linComb a b f g
  Limbs.shrAbs r.1 r.2 K

theorem applyRow_spec {w n K : ℕ} (hw : K + 2 ≤ w) (a b : Limbs w n) {f g : Word w}
    (hfg : |f.toInt| + |g.toInt| ≤ 2 ^ K) {A : ℤ}
    (hA : 2 ^ K * A = a.toNat * f.toInt + b.toNat * g.toInt) :
    ((applyRow a b f g K).1.toNat : ℤ) = |A| ∧ (applyRow a b f g K).2 = decide (A < 0) := by
  have h4 : (4 : ℤ) * 2 ^ K ≤ 2 ^ w := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hw
    rw [pow_succ, pow_succ] at this
    linarith
  obtain ⟨hv, -⟩ := Limbs.linComb_spec a b f g hfg h4
  have hK : (0 : ℤ) < 2 ^ K := by positivity
  -- `|A| < 2 ^ (w * n)`, since the row has absolute sum at most `2 ^ K`
  have ha : (a.toNat : ℤ) ≤ 2 ^ (w * n) - 1 := by
    have : (a.toNat : ℤ) < 2 ^ (w * n) := by exact_mod_cast Limbs.toNat_lt a
    linarith
  have hb : (b.toNat : ℤ) ≤ 2 ^ (w * n) - 1 := by
    have : (b.toNat : ℤ) < 2 ^ (w * n) := by exact_mod_cast Limbs.toNat_lt b
    linarith
  have hM : (0 : ℤ) ≤ 2 ^ (w * n) - 1 := by
    have : (1 : ℤ) ≤ 2 ^ (w * n) := one_le_pow₀ (by norm_num)
    linarith
  have hbound : 2 ^ K * |A| ≤ 2 ^ K * (2 ^ (w * n) - 1) := by
    calc 2 ^ K * |A| = |2 ^ K * A| := by rw [abs_mul, abs_of_pos hK]
      _ = |(a.toNat : ℤ) * f.toInt + b.toNat * g.toInt| := by rw [hA]
      _ ≤ |(a.toNat : ℤ) * f.toInt| + |(b.toNat : ℤ) * g.toInt| := abs_add_le _ _
      _ = a.toNat * |f.toInt| + b.toNat * |g.toInt| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ a.toNat),
            abs_of_nonneg (by positivity : (0 : ℤ) ≤ b.toNat)]
      _ ≤ (2 ^ (w * n) - 1) * |f.toInt| + (2 ^ (w * n) - 1) * |g.toInt| :=
          add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
      _ = (2 ^ (w * n) - 1) * (|f.toInt| + |g.toInt|) := by ring
      _ ≤ (2 ^ (w * n) - 1) * 2 ^ K := mul_le_mul_of_nonneg_left hfg hM
      _ = 2 ^ K * (2 ^ (w * n) - 1) := by ring
  have hlt : |A| < 2 ^ (w * n) := by
    have := le_of_mul_le_mul_left hbound hK
    linarith
  exact Limbs.shrAbs_spec _ _ (by omega) (hv.trans hA.symm) hlt

/-! ### Extracting the approximations from limbs -/

/-- The approximation of a multi-limb operand: the `w` bits from position `p`, shifted left
by `K`, plus the `K` low bits of the least significant limb. -/
def approxL {w n : ℕ} (K p : ℕ) (a : Limbs w (n + 1)) : Word w :=
  (Limbs.extract a p <<< K) + (a[0] &&& BitVec.ofNat w (2 ^ K - 1))

theorem approxL_eq {w n K p : ℕ} (hw : 2 * K + 2 ≤ w) (a : Limbs w (n + 1))
    (ha : a.toNat < 2 ^ (p + K + 2)) : approxL K p a = BitVec.ofNat w (approx K p a.toNat) := by
  have hlt := approx_lt_two_pow ha
  have hpow : 2 ^ (2 * K + 2) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hKw : 2 ^ (K + 2) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK1 : 2 ^ K ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKpos : 0 < 2 ^ K := by positivity
  have hq : a.toNat / 2 ^ p < 2 ^ (K + 2) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact lt_of_lt_of_eq ha (by congr 1; omega)
  have hmul : a.toNat / 2 ^ p * 2 ^ K < 2 ^ w := by
    unfold approx at hlt
    rw [Nat.mul_comm]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le hlt hpow)]
  simp only [approxL, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_and,
    BitVec.toNat_ofNat, Limbs.toNat_extract (by omega : 0 < w)]
  rw [Nat.mod_eq_of_lt (hq.trans_le hKw), Nat.shiftLeft_eq, Nat.mod_eq_of_lt hmul,
    Nat.mod_eq_of_lt (by omega : 2 ^ K - 1 < 2 ^ w), Nat.and_two_pow_sub_one_eq_mod,
    ← Limbs.toNat_mod_two_pow, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : K ≤ w))]
  unfold approx at hlt ⊢
  rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

/-! ### Approximations read from the top limb

`roundL` finds the position `p` from two bit lengths and then reads `w` bits of each operand
from there. Implementations do less work: `a ||| b` has the bit length of the longer operand,
so its most significant nonzero limb tells where the top of both operands is. The two limbs
of an operand at that position, shifted left by the number of leading zeros of that limb of
`a ||| b`, are the `w` bits below the top; the `K + 2` high ones are those of the
approximation. This is for words of exactly `w = 2 * K + 2` bits, the size implementations
use. -/

/-- The approximation of `a`, read from its limbs at the top of `m`: one scan for the two
limbs, one count of leading zeros, and one shift across the two limbs. When `m` fits in a
word, so does `a`, and the approximation is `a` itself. In a round, `m` is `a ||| b`. -/
def approxTop {w n : ℕ} (K : ℕ) (m a : Limbs w (n + 1)) : Word w :=
  let tm := (Limbs.topTwo m m).1
  let t := Limbs.topTwo m a
  let c := if tm = 0 then 0 else w - tm.toNat.size
  let win := Word.select (tm == 0) a[0] ((t.1 <<< c) ||| (t.2 >>> (w - c)))
  ((win >>> (w - K - 2)) <<< K) + (a[0] &&& BitVec.ofNat w (2 ^ K - 1))

/-- **The approximation read from the top limb is the approximation of the round**, for an
operand no longer than `m`, on words of `2 * K + 2` bits. -/
theorem approxTop_eq {w n K : ℕ} (hw : w = 2 * K + 2) (m a : Limbs w (n + 1))
    (ha : a.toNat.size ≤ m.toNat.size) :
    approxTop K m a = approxL K (max m.toNat.size (2 * K + 2) - K - 2) a := by
  have hwpos : 0 < w := by omega
  have hwK : w - K - 2 = K := by omega
  have hx : a.toNat < 2 ^ m.toNat.size := Nat.size_le.mp ha
  unfold approxTop approxL
  rw [Limbs.topTwo_eq m m, Limbs.topTwo_eq m a]
  by_cases hj : Limbs.topIdx m = 0
  · -- `m` fits in a word: the approximation is exact
    have hm : m.toNat.size ≤ w :=
      Nat.size_le.mpr (by simpa [hj] using Limbs.toNat_lt_two_pow_topIdx m)
    have hp : max m.toNat.size (2 * K + 2) - K - 2 = K := by omega
    have haw : a.toNat < 2 ^ w := hx.trans_le (Nat.pow_le_pow_right (by norm_num) hm)
    have ha0 : a[0].toNat = a.toNat := by rw [← Limbs.toNat_mod_two_pow, Nat.mod_eq_of_lt haw]
    simp only [hj, ↓reduceIte, beq_self_eq_true, Word.select_true]
    rw [hp, hwK]
    congr 2
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Limbs.toNat_extract hwpos, ha0, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt haw)]
  · -- the top of `m` is in limb `j ≥ 1`
    have hne := Limbs.limbD_topIdx_ne_zero m hj
    have hsize := Limbs.size_toNat_eq m hj
    obtain ⟨i, hi⟩ : ∃ i, Limbs.topIdx m = i + 1 := ⟨Limbs.topIdx m - 1, by omega⟩
    have hs1 : 0 < (Limbs.limbD m (Limbs.topIdx m)).toNat.size := by
      rw [Nat.size_pos]
      rcases Nat.eq_zero_or_pos (Limbs.limbD m (Limbs.topIdx m)).toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hne
      · exact h0
    have hs2 : (Limbs.limbD m (Limbs.topIdx m)).toNat.size ≤ w :=
      Nat.size_le.mpr (Limbs.limbD m (Limbs.topIdx m)).isLt
    simp only [hj, ↓reduceIte, hne, show (Limbs.limbD m (Limbs.topIdx m) == 0) = false by
      simpa using hne, Word.select_false]
    rw [hi] at hsize hs1 hs2 ⊢
    rw [Nat.add_sub_cancel]
    generalize (Limbs.limbD m (i + 1)).toNat.size = s at *
    have hp : max m.toNat.size (2 * K + 2) - K - 2 = w * i + s + K := by
      rw [hsize, Nat.mul_succ]
      omega
    have hN : m.toNat.size = w * i + s + w := by rw [hsize, Nat.mul_succ]; omega
    rw [hp, hwK]
    congr 2
    -- the two limbs, shifted, are the `w` bits of `a` from position `w * i + s`
    have hwin : (Limbs.limbD a (i + 1) <<< (w - s)) ||| (Limbs.limbD a i >>> (w - (w - s))) =
        BitVec.ofNat w (a.toNat / 2 ^ (w * i + s)) := by
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_ofNat, Nat.testBit_div_two_pow, hk, decide_true, Bool.true_and]
      by_cases h : k < w - s
      · rw [Limbs.getLsbD_limbD _ _ (by omega : w - (w - s) + k < w)]
        simp only [h, decide_true, Bool.not_true, Bool.false_and, Bool.false_or]
        congr 1
        omega
      · rw [Limbs.getLsbD_limbD _ _ (by omega : k - (w - s) < w),
          BitVec.getLsbD_of_ge _ _ (by omega : w ≤ w - (w - s) + k)]
        simp only [h, decide_false, Bool.not_false, Bool.true_and, Bool.or_false]
        congr 1
        rw [Nat.mul_succ]
        omega
    rw [hwin]
    have hq : a.toNat / 2 ^ (w * i + s) < 2 ^ w := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm w, ← hN]
      exact hx
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Limbs.toNat_extract hwpos,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hq, Nat.div_div_eq_div_mul, ← pow_add,
      Nat.mod_eq_of_lt]
    exact (Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ K))
      (by positivity)).trans_lt hq

/-- **The approximations of a round can be read from the top limb of `a ||| b`.** -/
theorem approxL_eq_approxTop {w n K : ℕ} (hw : w = 2 * K + 2) (a b : Limbs w (n + 1)) :
    approxL K (max (max (Limbs.bitLen a) (Limbs.bitLen b)) (2 * K + 2) - K - 2) a =
        approxTop K (Limbs.or a b) a ∧
      approxL K (max (max (Limbs.bitLen a) (Limbs.bitLen b)) (2 * K + 2) - K - 2) b =
        approxTop K (Limbs.or a b) b := by
  have hs : (Limbs.or a b).toNat.size = max (Limbs.bitLen a) (Limbs.bitLen b) := by
    rw [← Limbs.bitLen_eq, Limbs.bitLen_or]
  constructor
  · rw [approxTop_eq hw _ _ (by rw [hs, Limbs.bitLen_eq]; exact le_max_left _ _), hs]
  · rw [approxTop_eq hw _ _ (by rw [hs, Limbs.bitLen_eq (a := b)]; exact le_max_right _ _), hs]

/-! ### Applying the matrix to the cofactors -/

/-- `±(u * f + v * g) / 2 ^ K` modulo `m`, for a row `(f, g)` of the transition matrix, negated
when `neg` is set. -/
def cofRow {w n : ℕ} (u v : Limbs w (n + 1)) (f g : Word w) (neg : Bool) (m : Limbs w (n + 1))
    (ninv : Word w) (K : ℕ) : Limbs w (n + 1) :=
  Limbs.linCombRedc u v (Word.select neg (-f) f) (Word.select neg (-g) g) m ninv K

theorem cofRow_spec {w n K : ℕ} (hw : K + 3 ≤ w) (u v m : Limbs w (n + 1)) {f g : Word w}
    (ninv : Word w) (neg : Bool) (hfg : |f.toInt| + |g.toInt| ≤ 2 ^ K)
    (hu : u.toNat < m.toNat) (hv : v.toNat < m.toNat) (hodd : m.toNat % 2 = 1)
    (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0) :
    ((cofRow u v f g neg m ninv K).toNat : ℤ) =
      (if neg then -(u.toNat * f.toInt + v.toNat * g.toInt)
        else u.toNat * f.toInt + v.toNat * g.toInt) *
        (((m.toNat + 1) / 2 : ℕ) : ℤ) ^ K % m.toNat := by
  have hf : |f.toInt| ≤ 2 ^ K := by linarith [abs_nonneg g.toInt]
  have hg : |g.toInt| ≤ 2 ^ K := by linarith [abs_nonneg f.toInt]
  have hnf : (-f).toInt = -f.toInt :=
    Word.toInt_neg_of_inSRange (Word.inSRange_of_abs_le (K := K) (by omega) (by rwa [abs_neg]))
  have hng : (-g).toInt = -g.toInt :=
    Word.toInt_neg_of_inSRange (Word.inSRange_of_abs_le (K := K) (by omega) (by rwa [abs_neg]))
  cases neg
  · simp only [cofRow, Word.select_false, Bool.false_eq_true, ite_false]
    obtain ⟨h1, h2⟩ := Limbs.linCombRedc_spec hw u v m f g ninv hfg hu hv hinv
    exact Limbs.eq_mul_half_pow_emod hodd h1 h2
  · simp only [cofRow, Word.select_true, ite_true]
    obtain ⟨h1, h2⟩ := Limbs.linCombRedc_spec hw u v m (-f) (-g) ninv
      (by rw [hnf, hng, abs_neg, abs_neg]; exact hfg) hu hv hinv
    rw [hnf, hng, show (u.toNat : ℤ) * -f.toInt + v.toNat * -g.toInt =
      -(u.toNat * f.toInt + v.toNat * g.toInt) by ring] at h2
    exact Limbs.eq_mul_half_pow_emod hodd h1 h2

/-! ### One round on limbs -/

/-- One round on limbs: the approximations are extracted from the limbs, the inner loop runs
on words, then the rows of the matrix are applied to the operands and, with a Montgomery
reduction modulo `m`, to the cofactors. `ninv` is `-1 / m` modulo `2 ^ w`. -/
def roundL {w n : ℕ} (K : ℕ) (m : Limbs w (n + 1)) (ninv : Word w)
    (s : Limbs w (n + 1) × Limbs w (n + 1) × Limbs w (n + 1) × Limbs w (n + 1)) :
    Limbs w (n + 1) × Limbs w (n + 1) × Limbs w (n + 1) × Limbs w (n + 1) :=
  let p := max (max (Limbs.bitLen s.1) (Limbs.bitLen s.2.2.1)) (2 * K + 2) - K - 2
  let t := InnerW.step^[K] ⟨approxL K p s.1, approxL K p s.2.2.1, 1, 0, 0, 1⟩
  let ra := applyRow s.1 s.2.2.1 t.f0 t.g0 K
  let rb := applyRow s.1 s.2.2.1 t.f1 t.g1 K
  (ra.1, cofRow s.2.1 s.2.2.2 t.f0 t.g0 ra.2 m ninv K,
    rb.1, cofRow s.2.1 s.2.2.2 t.f1 t.g1 rb.2 m ninv K)

/-- The values of a limb-level state. -/
def vals {w n : ℕ} (s : Limbs w n × Limbs w n × Limbs w n × Limbs w n) : ℕ × ℕ × ℕ × ℕ :=
  (s.1.toNat, s.2.1.toNat, s.2.2.1.toNat, s.2.2.2.toNat)

/-- **A round on limbs computes the integer-level round.** -/
theorem roundL_spec {w n K : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) (m : Limbs w (n + 1))
    (ninv : Word w) (hodd : m.toNat % 2 = 1) (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0)
    (a u b v : Limbs w (n + 1)) (hb : b.toNat % 2 = 1) (hu : u.toNat < m.toNat)
    (hv : v.toNat < m.toNat) :
    vals (roundL K m ninv (a, u, b, v)) =
      roundM m.toNat K (a.toNat, u.toNat, b.toNat, v.toNat) := by
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
  unfold roundM roundL vals
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
  have hcu := cofRow_spec (by omega : K + 3 ≤ w) u v m ninv (applyRow a b sf0 sg0 K).2 hm0 hu hv
    hodd hinv
  have hcv := cofRow_spec (by omega : K + 3 ≤ w) u v m ninv (applyRow a b sf1 sg1 K).2 hm1 hu hv
    hodd hinv
  rw [ha2] at hcu
  rw [hb2] at hcv
  simp only [decide_eq_true_eq] at hcu hcv
  refine Prod.ext (Int.natCast_inj.mp (by rw [ha1, Int.natCast_natAbs])) (Prod.ext ?_
    (Prod.ext (Int.natCast_inj.mp (by rw [hb1, Int.natCast_natAbs])) ?_))
  · dsimp only
    rw [ha2, ← hcu, Int.toNat_natCast]
  · dsimp only
    rw [hb2, ← hcv, Int.toNat_natCast]

/-! ### The inversion on limbs -/

/-- The state of `roundM` keeps `b` odd and the cofactors reduced. -/
theorem roundM_iterate_inv {m K : ℕ} (hK : 1 ≤ K) (hm : 1 < m) (hodd : m % 2 = 1) (y i : ℕ) :
    ((roundM m K)^[i] (y, 1, m, 0)).2.2.1 % 2 = 1 ∧ ((roundM m K)^[i] (y, 1, m, 0)).2.1 < m ∧
      ((roundM m K)^[i] (y, 1, m, 0)).2.2.2 < m := by
  refine ⟨?_, ?_⟩
  · rw [(sim_iterate (K := K) hm y i).2.1]
    exact (rinv_iterate (y := y) hK hm hodd i).1
  · cases i with
    | zero => exact ⟨hm, (by omega : 0 < m)⟩
    | succ i => rw [Function.iterate_succ_apply']; exact roundM_lt (by omega) _

theorem roundL_iterate {w n K : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) (m : Limbs w (n + 1))
    (ninv : Word w) (hm1 : 1 < m.toNat) (hodd : m.toNat % 2 = 1)
    (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0) (y : Limbs w (n + 1)) (i : ℕ) :
    vals ((roundL K m ninv)^[i] (y, Limbs.ofNat _ 1, m, Limbs.ofNat _ 0)) =
      (roundM m.toNat K)^[i] (y.toNat, 1, m.toNat, 0) := by
  induction i with
  | zero =>
    have h1 : (Limbs.ofNat (n + 1) 1 : Limbs w (n + 1)).toNat = 1 :=
      Limbs.toNat_ofNat_of_lt (Nat.one_lt_two_pow (Nat.mul_pos (by omega) (by omega)).ne')
    simp [vals, h1]
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    obtain ⟨hb, hu, hv⟩ := roundM_iterate_inv hK hm1 hodd y.toNat i
    rw [← ih] at hb hu hv
    generalize (roundL K m ninv)^[i] (y, Limbs.ofNat _ 1, m, Limbs.ofNat _ 0) = s at *
    obtain ⟨a, u, b, v⟩ := s
    exact roundL_spec hK hw m ninv hodd hinv a u b v hb hu hv

/-- Pornin's modular inversion on limbs. `ninv` is `-1 / m` modulo `2 ^ w`. -/
def porninInvL {w n : ℕ} (K : ℕ) (m : Limbs w (n + 1)) (ninv : Word w) (y : Limbs w (n + 1)) :
    Limbs w (n + 1) :=
  let s := (roundL K m ninv)^[rounds m.toNat K] (y, Limbs.ofNat _ 1, m, Limbs.ofNat _ 0)
  Limbs.select (Limbs.eq s.2.2.1 (Limbs.ofNat _ 1)) s.2.2.2 (Limbs.ofNat _ 0)

/-- **The inversion on limbs computes the integer-level inversion.** -/
theorem porninInvL_spec {w n K : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) (m : Limbs w (n + 1))
    (ninv : Word w) (hm1 : 1 < m.toNat) (hodd : m.toNat % 2 = 1)
    (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0) (y : Limbs w (n + 1)) :
    (porninInvL K m ninv y).toNat = porninInv y.toNat m.toNat K := by
  have hv := roundL_iterate hK hw m ninv hm1 hodd hinv y (rounds m.toNat K)
  have h1 : (Limbs.ofNat (n + 1) 1 : Limbs w (n + 1)).toNat = 1 :=
    Limbs.toNat_ofNat_of_lt (Nat.one_lt_two_pow (Nat.mul_pos (by omega) (by omega)).ne')
  rw [← porninInvM_eq hm1]
  unfold porninInvL porninInvM
  dsimp only
  rw [← hv]
  generalize (roundL K m ninv)^[rounds m.toNat K] (y, Limbs.ofNat _ 1, m, Limbs.ofNat _ 0) = s
  obtain ⟨a, u, b, v⟩ := s
  simp only [vals]
  rw [Limbs.toNat_select, Limbs.eq_eq, Limbs.toNat_ofNat_zero]
  by_cases hb : b.toNat = 1
  · have : b = Limbs.ofNat _ 1 := Limbs.toNat_injective (hb.trans h1.symm)
    subst this
    simp [h1]
  · have : b ≠ Limbs.ofNat _ 1 := fun h => hb (h ▸ h1)
    simp [hb, this]

/-- **Correctness of Pornin's modular inversion on limbs.** For `y < m` coprime to an odd
`m > 1`, the result is the inverse of `y` modulo `m`, in `[0, m)`. -/
theorem porninInvL_inv {w n K : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) (m : Limbs w (n + 1))
    (ninv : Word w) (hm1 : 1 < m.toNat) (hodd : m.toNat % 2 = 1)
    (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0) (y : Limbs w (n + 1))
    (hy : y.toNat < m.toNat) (hco : Nat.Coprime y.toNat m.toNat) :
    (porninInvL K m ninv y).toNat < m.toNat ∧
      y.toNat * (porninInvL K m ninv y).toNat % m.toNat = 1 := by
  rw [porninInvL_spec hK hw m ninv hm1 hodd hinv y]
  exact porninInv_spec hK hm1 hodd hy hco

/-! ### The last steps on single words -/

/-- A word state with the identity matrix represents the integer state with the same
operands. -/
theorem refines_identity {w : ℕ} (hw : 2 ≤ w) (x y : Word w) :
    Refines (⟨x, y, 1, 0, 0, 1⟩ : InnerW w) ⟨x.toNat, y.toNat, 1, 0, 0, 1⟩ := by
  have h4 : 2 ^ 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hn : (1 : Word w).toNat = 1 := by
    change (BitVec.ofNat w 1).toNat = 1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : (1 : Word w).toInt = 1 := by
    rw [Word.toInt_eq_toNat_of_lt (by rw [hn]; omega), hn]
    rfl
  exact ⟨rfl, rfl, h1, by simp, by simp, h1⟩

/-- **The last steps run on single words.** When `a = 0` or both operands fit in a word, `T`
steps of the inner loop on the least significant limbs of `a` and `b` compute the second row
of the matrix of the plain binary gcd on `a` and `b`, for `T ≤ w - 2`; and `b` with its least
significant limb replaced by the word the loop ends on is the final `b`. -/
theorem innerW_tail {w n T : ℕ} (hw : T + 2 ≤ w) (a b : Limbs w (n + 1))
    (hab : a.toNat = 0 ∨ (a.toNat < 2 ^ w ∧ b.toNat < 2 ^ w)) :
    (InnerW.step^[T] ⟨a[0], b[0], 1, 0, 0, 1⟩).f1.toInt =
        (Inner.step^[T] ⟨a.toNat, b.toNat, 1, 0, 0, 1⟩).f1 ∧
      (InnerW.step^[T] ⟨a[0], b[0], 1, 0, 0, 1⟩).g1.toInt =
        (Inner.step^[T] ⟨a.toNat, b.toNat, 1, 0, 0, 1⟩).g1 ∧
      (Limbs.toNat (b.set 0 (InnerW.step^[T] ⟨a[0], b[0], 1, 0, 0, 1⟩).bbar) : ℤ) =
        (Inner.step^[T] ⟨a.toNat, b.toNat, 1, 0, 0, 1⟩).bbar := by
  have href := refines_iterate hw (refines_identity (by omega) a[0] b[0]) (le_refl T)
  have ha0 := Limbs.toNat_mod_two_pow a
  have hb0 := Limbs.toNat_mod_two_pow b
  rcases hab with ha | ⟨ha, hb⟩
  · -- `a = 0`: the steps do not look at `b`
    rw [ha, Nat.zero_mod] at ha0
    rw [← ha0, Nat.cast_zero, step_iterate_zero] at href
    rw [ha, Nat.cast_zero, step_iterate_zero]
    obtain ⟨-, hbb, -, -, hf1, hg1⟩ := href
    dsimp only at hbb hf1 hg1 ⊢
    have hbw : (InnerW.step^[T] ⟨a[0], b[0], 1, 0, 0, 1⟩).bbar = b[0] :=
      BitVec.eq_of_toNat_eq (by exact_mod_cast hbb)
    rw [hbw, Vector.set_getElem_self]
    exact ⟨hf1, hg1, rfl⟩
  · -- both operands are their least significant limbs
    rw [Nat.mod_eq_of_lt ha] at ha0
    rw [Nat.mod_eq_of_lt hb] at hb0
    rw [← ha0, ← hb0] at href
    obtain ⟨-, hbb, -, -, hf1, hg1⟩ := href
    refine ⟨hf1, hg1, ?_⟩
    have htail : Limbs.toNat b.tail = 0 := by
      have h := Limbs.toNat_eq_head_add b
      have hpos : 0 < 2 ^ w := by positivity
      rcases Nat.eq_zero_or_pos (Limbs.toNat b.tail) with h0 | h0
      · exact h0
      · have := Nat.mul_le_mul_left (2 ^ w) h0
        omega
    rw [Limbs.toNat_set_zero, htail, Nat.mul_zero, Nat.add_zero]
    exact hbb

/-- The last steps on limbs: `T` steps of the inner loop on the least significant limbs of
`a` and `b`, then the second row of the matrix applied to the cofactors, with a Montgomery
reduction by `2 ^ T`. The result is the final `b`, which is `b` with its least significant
limb replaced, and the final `v`. -/
def tailL {w n : ℕ} (T : ℕ) (m : Limbs w (n + 1)) (ninv : Word w)
    (s : Limbs w (n + 1) × Limbs w (n + 1) × Limbs w (n + 1) × Limbs w (n + 1)) :
    Limbs w (n + 1) × Limbs w (n + 1) :=
  let t := InnerW.step^[T] ⟨s.1[0], s.2.2.1[0], 1, 0, 0, 1⟩
  (s.2.2.1.set 0 t.bbar, cofRow s.2.1 s.2.2.2 t.f1 t.g1 false m ninv T)

/-- **The last steps on limbs compute the integer-level ones.** -/
theorem tailL_spec {w n T : ℕ} (hT : T + 3 ≤ w) (m : Limbs w (n + 1)) (ninv : Word w)
    (hodd : m.toNat % 2 = 1) (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0)
    (a u b v : Limbs w (n + 1)) (hab : a.toNat = 0 ∨ (a.toNat < 2 ^ w ∧ b.toNat < 2 ^ w))
    (hu : u.toNat < m.toNat) (hv : v.toNat < m.toNat) :
    ((tailL T m ninv (a, u, b, v)).1.toNat, (tailL T m ninv (a, u, b, v)).2.toNat) =
      tailM m.toNat T (a.toNat, u.toNat, b.toNat, v.toNat) := by
  obtain ⟨hf1, hg1, hbb⟩ := innerW_tail (T := T) (by omega) a b hab
  have hmat := (matBound_iterate (a.toNat : ℤ) b.toNat T).2
  unfold tailL tailM
  dsimp only
  generalize InnerW.step^[T] ⟨a[0], b[0], 1, 0, 0, 1⟩ = s at hf1 hg1 hbb ⊢
  generalize Inner.step^[T] ⟨(a.toNat : ℤ), (b.toNat : ℤ), 1, 0, 0, 1⟩ = t at hf1 hg1 hbb hmat ⊢
  rw [← hf1, ← hg1] at hmat ⊢
  have hc := cofRow_spec hT u v m ninv false hmat hu hv hodd hinv
  simp only [Bool.false_eq_true, ite_false] at hc
  rw [← hbb, ← hc, Int.toNat_natCast, Int.toNat_natCast]

/-- Pornin's modular inversion on limbs with `r` rounds followed by `T` steps on single
words. `ninv` is `-1 / m` modulo `2 ^ w`. -/
def porninInvSL {w n : ℕ} (K r T : ℕ) (m : Limbs w (n + 1)) (ninv : Word w)
    (y : Limbs w (n + 1)) : Limbs w (n + 1) :=
  let p := tailL T m ninv ((roundL K m ninv)^[r] (y, Limbs.ofNat _ 1, m, Limbs.ofNat _ 0))
  Limbs.select (Limbs.eq p.1 (Limbs.ofNat _ 1)) p.2 (Limbs.ofNat _ 0)

/-- **The inversion on limbs with the shorter schedule computes the integer-level one.** The
last steps need `T ≤ w - 3`, and operands that fit in a word after the `r` rounds, which
`2 * ℓ(m) ≤ K * r + w + 1` ensures. -/
theorem porninInvSL_spec {w n K r T : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) (hT : T + 3 ≤ w)
    (m : Limbs w (n + 1)) (ninv : Word w) (hm1 : 1 < m.toNat) (hodd : m.toNat % 2 = 1)
    (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0) (y : Limbs w (n + 1))
    (hy : y.toNat < m.toNat) (hfit : 2 * m.toNat.size ≤ K * r + w + 1) :
    (porninInvSL K r T m ninv y).toNat = porninInvS y.toNat m.toNat K r T := by
  have hv := roundL_iterate hK hw m ninv hm1 hodd hinv y r
  have h1 : (Limbs.ofNat (n + 1) 1 : Limbs w (n + 1)).toNat = 1 :=
    Limbs.toNat_ofNat_of_lt (Nat.one_lt_two_pow (Nat.mul_pos (by omega) (by omega)).ne')
  obtain ⟨-, hu, hv'⟩ := roundM_iterate_inv hK hm1 hodd y.toNat r
  have hab := roundM_iterate_fit hK hm1 hodd hy hfit
  rw [← porninInvSM_eq hm1]
  unfold porninInvSL porninInvSM
  dsimp only
  rw [← hv] at hu hv' hab ⊢
  generalize (roundL K m ninv)^[r] (y, Limbs.ofNat _ 1, m, Limbs.ofNat _ 0) = s at *
  obtain ⟨a, u, b, v⟩ := s
  simp only [vals] at hu hv' hab
  have ht : (_, _) = tailM m.toNat T (vals (a, u, b, v)) :=
    tailL_spec hT m ninv hodd hinv a u b v hab hu hv'
  generalize tailM m.toNat T (vals (a, u, b, v)) = q at ht ⊢
  subst ht
  generalize tailL T m ninv (a, u, b, v) = p
  obtain ⟨b', v'⟩ := p
  dsimp only
  rw [Limbs.toNat_select, Limbs.eq_eq, Limbs.toNat_ofNat_zero]
  by_cases hb : b'.toNat = 1
  · have : b' = Limbs.ofNat _ 1 := Limbs.toNat_injective (hb.trans h1.symm)
    subst this
    simp [h1]
  · have : b' ≠ Limbs.ofNat _ 1 := fun h => hb (h ▸ h1)
    simp [hb, this]

/-- **The shorter schedule computes the same limbs as `porninInvL`**, as soon as
`K * r + T ≥ 2 * ℓ(m) - 2`. -/
theorem porninInvSL_eq {w n K r T : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) (hT : T + 3 ≤ w)
    (m : Limbs w (n + 1)) (ninv : Word w) (hm1 : 1 < m.toNat) (hodd : m.toNat % 2 = 1)
    (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0) (y : Limbs w (n + 1))
    (hy : y.toNat < m.toNat) (hfit : 2 * m.toNat.size ≤ K * r + w + 1)
    (hN : 2 * m.toNat.size ≤ K * r + T + 2) :
    porninInvSL K r T m ninv y = porninInvL K m ninv y := by
  apply Limbs.toNat_injective
  rw [porninInvSL_spec hK hw hT m ninv hm1 hodd hinv y hy hfit,
    porninInvL_spec hK hw m ninv hm1 hodd hinv y, porninInvS_eq hK hm1 hodd hy hN]

/-- **Correctness of the shorter schedule on limbs.** For `y < m` coprime to an odd `m > 1`,
the result is the inverse of `y` modulo `m`, in `[0, m)`. -/
theorem porninInvSL_inv {w n K r T : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) (hT : T + 3 ≤ w)
    (m : Limbs w (n + 1)) (ninv : Word w) (hm1 : 1 < m.toNat) (hodd : m.toNat % 2 = 1)
    (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0) (y : Limbs w (n + 1))
    (hy : y.toNat < m.toNat) (hfit : 2 * m.toNat.size ≤ K * r + w + 1)
    (hN : 2 * m.toNat.size ≤ K * r + T + 2) (hco : Nat.Coprime y.toNat m.toNat) :
    (porninInvSL K r T m ninv y).toNat < m.toNat ∧
      y.toNat * (porninInvSL K r T m ninv y).toNat % m.toNat = 1 := by
  rw [porninInvSL_eq hK hw hT m ninv hm1 hodd hinv y hy hfit hN]
  exact porninInvL_inv hK hw m ninv hm1 hodd hinv y hy hco

/-! ### Division

The runs of the inversion with the cofactor `u` started at `x` instead of `1`. Their states
are those of the inversion with the cofactors multiplied by `x` (`roundL_iterate_scale`), so
they return `x / y`. -/

/-- The rounds on limbs from `(y, x, m, 0)`: the operands are those of the inversion, and the
cofactors are those of the inversion multiplied by `x` modulo `m`. -/
theorem roundL_iterate_scale {w n K : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w)
    (m : Limbs w (n + 1)) (ninv : Word w) (hm1 : 1 < m.toNat) (hodd : m.toNat % 2 = 1)
    (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0) (x y : Limbs w (n + 1))
    (hx : x.toNat < m.toNat) (i : ℕ) :
    vals ((roundL K m ninv)^[i] (y, x, m, Limbs.ofNat _ 0)) =
      scale m.toNat x.toNat ((roundM m.toNat K)^[i] (y.toNat, 1, m.toNat, 0)) := by
  induction i with
  | zero => simp [vals, scale, Nat.mod_eq_of_lt hx]
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ← roundM_scale (by omega : 0 < m.toNat), ← ih]
    obtain ⟨hb, -, -⟩ := roundM_iterate_inv hK hm1 hodd y.toNat i
    generalize (roundL K m ninv)^[i] (y, x, m, Limbs.ofNat _ 0) = s at ih ⊢
    generalize (roundM m.toNat K)^[i] (y.toNat, 1, m.toNat, 0) = S at ih hb
    obtain ⟨a, u, b, v⟩ := s
    obtain ⟨A, U, B, V⟩ := S
    simp only [vals, scale, Prod.mk.injEq] at ih
    obtain ⟨-, hu, hbB, hv⟩ := ih
    have hmod : ∀ z, z % m.toNat < m.toNat := fun z => Nat.mod_lt _ (by omega)
    exact roundL_spec hK hw m ninv hodd hinv a u b v (by rw [hbB]; exact hb)
      (by rw [hu]; exact hmod _) (by rw [hv]; exact hmod _)

/-- The quotient `x / y` modulo `m` on limbs: the rounds of `porninInvL` with the cofactor
`u` started at `x`. `ninv` is `-1 / m` modulo `2 ^ w`. -/
def porninDivL {w n : ℕ} (K : ℕ) (m : Limbs w (n + 1)) (ninv : Word w)
    (x y : Limbs w (n + 1)) : Limbs w (n + 1) :=
  let s := (roundL K m ninv)^[rounds m.toNat K] (y, x, m, Limbs.ofNat _ 0)
  Limbs.select (Limbs.eq s.2.2.1 (Limbs.ofNat _ 1)) s.2.2.2 (Limbs.ofNat _ 0)

/-- The quotient `x / y` modulo `m` on limbs with `r` rounds followed by `T` steps on single
words: the run of `porninInvSL` with the cofactor `u` started at `x`. -/
def porninDivSL {w n : ℕ} (K r T : ℕ) (m : Limbs w (n + 1)) (ninv : Word w)
    (x y : Limbs w (n + 1)) : Limbs w (n + 1) :=
  let p := tailL T m ninv ((roundL K m ninv)^[r] (y, x, m, Limbs.ofNat _ 0))
  Limbs.select (Limbs.eq p.1 (Limbs.ofNat _ 1)) p.2 (Limbs.ofNat _ 0)

/-- The result of a run on limbs, from the final `b` and `v`: `v` if `b = 1`, else `0`. -/
theorem toNat_select_eq_one {w n : ℕ} (hw : 0 < w) (b v : Limbs w (n + 1)) :
    (Limbs.select (Limbs.eq b (Limbs.ofNat _ 1)) v (Limbs.ofNat _ 0)).toNat =
      if b.toNat = 1 then v.toNat else 0 := by
  have h1 : (Limbs.ofNat (n + 1) 1 : Limbs w (n + 1)).toNat = 1 :=
    Limbs.toNat_ofNat_of_lt (Nat.one_lt_two_pow (Nat.mul_pos hw (by omega)).ne')
  rw [Limbs.toNat_select, Limbs.eq_eq, Limbs.toNat_ofNat_zero]
  by_cases hb : b.toNat = 1
  · have : b = Limbs.ofNat _ 1 := Limbs.toNat_injective (hb.trans h1.symm)
    subst this
    simp [h1]
  · have : b ≠ Limbs.ofNat _ 1 := fun h => hb (h ▸ h1)
    simp [hb, this]

/-- **The division on limbs computes the integer-level division.** -/
theorem porninDivL_spec {w n K : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) (m : Limbs w (n + 1))
    (ninv : Word w) (hm1 : 1 < m.toNat) (hodd : m.toNat % 2 = 1)
    (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0) (x y : Limbs w (n + 1))
    (hx : x.toNat < m.toNat) :
    (porninDivL K m ninv x y).toNat = porninDiv x.toNat y.toNat m.toNat K := by
  have hv := roundL_iterate_scale hK hw m ninv hm1 hodd hinv x y hx (rounds m.toNat K)
  rw [porninDiv_eq hx, ← porninInvM_eq hm1]
  unfold porninDivL porninInvM
  dsimp only
  generalize (roundL K m ninv)^[rounds m.toNat K] (y, x, m, Limbs.ofNat _ 0) = s at hv ⊢
  generalize (roundM m.toNat K)^[rounds m.toNat K] (y.toNat, 1, m.toNat, 0) = S at hv ⊢
  obtain ⟨a, u, b, v⟩ := s
  obtain ⟨A, U, B, V⟩ := S
  simp only [vals, scale, Prod.mk.injEq] at hv
  obtain ⟨-, -, hb, hvv⟩ := hv
  rw [toNat_select_eq_one (by omega), hb, hvv]
  by_cases hB : B = 1
  · simp [hB]
  · simp [hB]

/-- **The division on limbs with the shorter schedule computes the integer-level division**,
under the conditions of `porninInvSL_spec` and `porninInvS_eq`. -/
theorem porninDivSL_spec {w n K r T : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) (hT : T + 3 ≤ w)
    (m : Limbs w (n + 1)) (ninv : Word w) (hm1 : 1 < m.toNat) (hodd : m.toNat % 2 = 1)
    (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0) (x y : Limbs w (n + 1))
    (hx : x.toNat < m.toNat) (hy : y.toNat < m.toNat)
    (hfit : 2 * m.toNat.size ≤ K * r + w + 1) (hN : 2 * m.toNat.size ≤ K * r + T + 2) :
    (porninDivSL K r T m ninv x y).toNat = porninDiv x.toNat y.toNat m.toNat K := by
  have hv := roundL_iterate_scale hK hw m ninv hm1 hodd hinv x y hx r
  have hab := roundM_iterate_fit hK hm1 hodd hy hfit
  have hmod : ∀ z, z % m.toNat < m.toNat := fun z => Nat.mod_lt _ (by omega)
  rw [porninDiv_eq hx, ← porninInvS_eq hK hm1 hodd hy hN, ← porninInvSM_eq hm1]
  unfold porninDivSL porninInvSM
  dsimp only
  generalize (roundL K m ninv)^[r] (y, x, m, Limbs.ofNat _ 0) = s at hv ⊢
  generalize (roundM m.toNat K)^[r] (y.toNat, 1, m.toNat, 0) = S at hv hab ⊢
  obtain ⟨a, u, b, v⟩ := s
  obtain ⟨A, U, B, V⟩ := S
  simp only [vals, scale, Prod.mk.injEq] at hv
  obtain ⟨ha, hu, hb, hvv⟩ := hv
  have ht := tailL_spec hT m ninv hodd hinv a u b v (by rw [ha, hb]; exact hab)
    (by rw [hu]; exact hmod _) (by rw [hvv]; exact hmod _)
  have hsc := tailM_scale (m := m.toNat) (T := T) (by omega) x.toNat (A, U, B, V)
  simp only [scale] at hsc
  rw [ha, hu, hb, hvv, hsc] at ht
  generalize tailM m.toNat T (A, U, B, V) = q at ht ⊢
  generalize tailL T m ninv (a, u, b, v) = p at ht ⊢
  obtain ⟨b', v'⟩ := p
  obtain ⟨Bq, Vq⟩ := q
  simp only [Prod.mk.injEq] at ht
  obtain ⟨hb', hv'⟩ := ht
  rw [toNat_select_eq_one (by omega), hb', hv']
  by_cases hB : Bq = 1
  · simp [hB]
  · simp [hB]

/-- **The shorter schedule computes the same quotient as `porninDivL`.** -/
theorem porninDivSL_eq {w n K r T : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) (hT : T + 3 ≤ w)
    (m : Limbs w (n + 1)) (ninv : Word w) (hm1 : 1 < m.toNat) (hodd : m.toNat % 2 = 1)
    (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0) (x y : Limbs w (n + 1))
    (hx : x.toNat < m.toNat) (hy : y.toNat < m.toNat)
    (hfit : 2 * m.toNat.size ≤ K * r + w + 1) (hN : 2 * m.toNat.size ≤ K * r + T + 2) :
    porninDivSL K r T m ninv x y = porninDivL K m ninv x y := by
  apply Limbs.toNat_injective
  rw [porninDivSL_spec hK hw hT m ninv hm1 hodd hinv x y hx hy hfit hN,
    porninDivL_spec hK hw m ninv hm1 hodd hinv x y hx]

/-- **Correctness of the division on limbs.** For `x, y < m` with `y` coprime to an odd
`m > 1`, the result `q` is in `[0, m)` and `y * q ≡ x` modulo `m`. -/
theorem porninDivSL_div {w n K r T : ℕ} (hK : 1 ≤ K) (hw : 2 * K + 2 ≤ w) (hT : T + 3 ≤ w)
    (m : Limbs w (n + 1)) (ninv : Word w) (hm1 : 1 < m.toNat) (hodd : m.toNat % 2 = 1)
    (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0) (x y : Limbs w (n + 1))
    (hx : x.toNat < m.toNat) (hy : y.toNat < m.toNat)
    (hfit : 2 * m.toNat.size ≤ K * r + w + 1) (hN : 2 * m.toNat.size ≤ K * r + T + 2)
    (hco : Nat.Coprime y.toNat m.toNat) :
    (porninDivSL K r T m ninv x y).toNat < m.toNat ∧
      y.toNat * (porninDivSL K r T m ninv x y).toNat % m.toNat = x.toNat := by
  rw [porninDivSL_spec hK hw hT m ninv hm1 hodd hinv x y hx hy hfit hN]
  exact porninDiv_spec hK hm1 hodd hx hy hco

end Bingcd.Pornin
