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
overflows. The rest of a round is on multi-limb integers: this file has the update of the
operands and the extraction of the approximations, `Cofactors.lean` has the update of the
cofactors and the whole run. The integer-level algorithm this file refines is in
`Proofs/Helpers/Bingcd/Schedule.lean` and the files it imports. -/

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

A round finds the position `p` from two bit lengths and then reads `w` bits of each operand
from there (`approxL`). Implementations do less work: `a ||| b` has the bit length of the longer
operand, so its most significant nonzero limb tells where the top of both operands is. The two
limbs of an operand at that position, shifted left by the number of leading zeros of that limb
of `a ||| b`, are the `w` bits below the top; the `K + 2` high ones are those of the
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

end Bingcd.Pornin
