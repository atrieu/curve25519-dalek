module
public import Proofs.Helpers.Bingcd.Limbs
public import Mathlib.Algebra.Order.Ring.Abs

/-! # Signed linear combinations of multi-limb integers

A signed integer is represented here by `n` unsigned low limbs `r` and one signed top word
`c`, with value `r + 2 ^ (w * n) * c`. This is what a word-by-word loop with a signed carry
produces, and it is enough to apply a matrix with small signed entries to two multi-limb
operands, as the bulk updates of Pornin's binary gcd do. -/

@[expose] public section

namespace Bingcd

namespace Word

variable {w : ℕ}

/-- `a * f + b * g + c` with `a`, `b` unsigned and `f`, `g`, `c` signed: the low word, and the
high word as a signed carry. -/
def smulAdd2 (a b f g c : Word w) : Word w × Word w :=
  let z := a.toNat * f.toInt + b.toNat * g.toInt + c.toInt
  (BitVec.ofInt w z, BitVec.ofInt w (z / 2 ^ w))

theorem smulAdd2_spec (a b f g c : Word w)
    (h : InSRange w ((a.toNat * f.toInt + b.toNat * g.toInt + c.toInt) / 2 ^ w)) :
    ((smulAdd2 a b f g c).1.toNat : ℤ) + 2 ^ w * (smulAdd2 a b f g c).2.toInt =
        a.toNat * f.toInt + b.toNat * g.toInt + c.toInt ∧
      (smulAdd2 a b f g c).2.toInt =
        (a.toNat * f.toInt + b.toNat * g.toInt + c.toInt) / 2 ^ w := by
  have hP : (0 : ℤ) < 2 ^ w := by positivity
  simp only [smulAdd2]
  rw [toInt_ofInt_of_inSRange h, BitVec.toNat_ofInt]
  refine ⟨?_, rfl⟩
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
  push_cast
  exact Int.emod_add_mul_ediv _ _

end Word

namespace Limbs

variable {w n : ℕ}

/-- `a * f + b * g` for unsigned multi-limb `a`, `b` and signed words `f`, `g`: the `n` low
limbs and a signed carry word. -/
def linComb : {n : ℕ} → Limbs w n → Limbs w n → Word w → Word w → Limbs w n × Word w
  | 0, _, _, _, _ => (#v[], 0)
  | _ + 1, a, b, f, g =>
    let r := linComb a.pop b.pop f g
    let s := Word.smulAdd2 a.back b.back f g r.2
    (r.1.push s.1, s.2)

/-- For `|f| + |g| ≤ S ≤ 2 ^ (w - 2)`, the value of `linComb` is `a * f + b * g` and its
carry is at most `S` in absolute value. -/
theorem linComb_spec (a b : Limbs w n) (f g : Word w) {S : ℤ}
    (hS : |f.toInt| + |g.toInt| ≤ S) (hw : 4 * S ≤ 2 ^ w) :
    (toNat (linComb a b f g).1 : ℤ) + 2 ^ (w * n) * (linComb a b f g).2.toInt =
        a.toNat * f.toInt + b.toNat * g.toInt ∧ |(linComb a b f g).2.toInt| ≤ S := by
  have hS0 : 0 ≤ S := le_trans (add_nonneg (abs_nonneg _) (abs_nonneg _)) hS
  induction n with
  | zero => simp [linComb, toNat_zero, hS0]
  | succ n ih =>
    obtain ⟨h₁, hc⟩ := ih a.pop b.pop
    have hP : (0 : ℤ) < 2 ^ w := by positivity
    have hA : (a.back.toNat : ℤ) ≤ 2 ^ w - 1 := by
      have : (a.back.toNat : ℤ) < 2 ^ w := by exact_mod_cast a.back.isLt
      linarith
    have hB : (b.back.toNat : ℤ) ≤ 2 ^ w - 1 := by
      have : (b.back.toNat : ℤ) < 2 ^ w := by exact_mod_cast b.back.isLt
      linarith
    have hAf : |(a.back.toNat : ℤ) * f.toInt| ≤ (2 ^ w - 1) * |f.toInt| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right hA (abs_nonneg _)
    have hBg : |(b.back.toNat : ℤ) * g.toInt| ≤ (2 ^ w - 1) * |g.toInt| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right hB (abs_nonneg _)
    have hSS : (2 ^ w - 1) * (|f.toInt| + |g.toInt|) ≤ (2 ^ w - 1) * S :=
      mul_le_mul_of_nonneg_left hS (by linarith)
    obtain ⟨hc1, hc2⟩ := abs_le.mp hc
    obtain ⟨hf1, hf2⟩ := abs_le.mp hAf
    obtain ⟨hg1, hg2⟩ := abs_le.mp hBg
    set z := (a.back.toNat : ℤ) * f.toInt + b.back.toNat * g.toInt +
      (linComb a.pop b.pop f g).2.toInt with hz
    have hz1 : -S * 2 ^ w ≤ z := by rw [hz]; nlinarith
    have hz2 : z ≤ S * 2 ^ w := by rw [hz]; nlinarith
    have hq1 : -S ≤ z / 2 ^ w := Int.le_ediv_of_mul_le hP hz1
    have hq2 : z / 2 ^ w ≤ S := Int.ediv_le_of_le_mul hP hz2
    obtain ⟨h₂, h₃⟩ := Word.smulAdd2_spec a.back b.back f g (linComb a.pop b.pop f g).2
      ⟨by rw [← hz]; linarith, by rw [← hz]; linarith⟩
    rw [← hz] at h₂ h₃
    simp only [linComb, toNat_push, Nat.add_one_sub_one]
    refine ⟨?_, by rw [h₃]; exact abs_le.mpr ⟨hq1, hq2⟩⟩
    rw [toNat_eq_pop_add a, toNat_eq_pop_add b, Nat.mul_succ, pow_add]
    push_cast
    linear_combination h₁ + 2 ^ (w * n) * h₂

/-- The absolute value and the sign of the exact quotient by `2 ^ k` of the signed number
with low limbs `r` and signed top word `c`. -/
def shrAbs (r : Limbs w n) (c : Word w) (k : ℕ) : Limbs w n × Bool :=
  let low := (shr (r.push c) k).1.pop
  (select c.msb (sub (ofNat n 0) low) low, c.msb)

/-- If `r + 2 ^ (w * n) * c = 2 ^ k * A` with `|A| < 2 ^ (w * n)`, then `shrAbs` returns
`|A|` and whether `A` is negative. -/
theorem shrAbs_spec (r : Limbs w n) (c : Word w) {k : ℕ} (hk : k < w) {A : ℤ}
    (hV : (toNat r : ℤ) + 2 ^ (w * n) * c.toInt = 2 ^ k * A) (hA : |A| < 2 ^ (w * n)) :
    (toNat (shrAbs r c k).1 : ℤ) = |A| ∧ (shrAbs r c k).2 = decide (A < 0) := by
  have hM : (0 : ℤ) < 2 ^ (w * n) := by positivity
  have hkpos : (0 : ℤ) < 2 ^ k := by positivity
  have hmsb : c.msb = decide (c.toInt < 0) := BitVec.msb_eq_toInt
  have hr0 : (0 : ℤ) ≤ toNat r := by positivity
  have hrM : (toNat r : ℤ) < 2 ^ (w * n) := by exact_mod_cast toNat_lt r
  obtain ⟨hA1, hA2⟩ := abs_lt.mp hA
  -- the sign of `A` is the sign of the top word
  have hneg : c.toInt < 0 ↔ A < 0 := by
    constructor
    · intro hc
      have h1 : 2 ^ (w * n) * c.toInt ≤ 2 ^ (w * n) * (-1) :=
        mul_le_mul_of_nonneg_left (by omega) hM.le
      by_contra hA0
      have : 0 ≤ 2 ^ k * A := mul_nonneg hkpos.le (not_lt.mp hA0)
      linarith
    · intro hA0
      by_contra hc
      have h1 : 0 ≤ 2 ^ (w * n) * c.toInt := mul_nonneg hM.le (not_lt.mp hc)
      have : 2 ^ k * A < 0 := mul_neg_of_pos_of_neg hkpos hA0
      linarith
  -- the low limbs of the shifted number are `A` modulo `2 ^ (w * n)`
  have hlow : (toNat (shr (r.push c) k).1.pop : ℤ) = A % 2 ^ (w * n) := by
    obtain ⟨T, hT⟩ : ∃ T : ℤ, (c.toNat : ℤ) = c.toInt + 2 ^ k * T := by
      rcases Nat.lt_or_ge (2 * c.toNat) (2 ^ w) with h | h
      · exact ⟨0, by rw [Word.toInt_eq_toNat_of_lt h]; ring⟩
      · refine ⟨2 ^ (w - k), ?_⟩
        rw [Word.toInt_eq_toNat_sub_of_le h, ← pow_add, show k + (w - k) = w by omega]
        ring
    rw [toNat_pop, toNat_shr_fst _ hk, toNat_push]
    push_cast
    rw [hT, show (toNat r : ℤ) + 2 ^ (w * n) * (c.toInt + 2 ^ k * T) =
      2 ^ k * (A + 2 ^ (w * n) * T) by linear_combination hV,
      Int.mul_ediv_cancel_left _ hkpos.ne', Int.add_mul_emod_self_left]
  simp only [shrAbs]
  refine ⟨?_, by rw [hmsb]; exact decide_eq_decide.mpr hneg⟩
  rw [hmsb]
  by_cases hc : c.toInt < 0
  · have hA0 := hneg.mp hc
    rw [← Int.add_emod_right, Int.emod_eq_of_lt (by linarith) (by linarith)] at hlow
    have hlt := toNat_lt (shr (r.push c) k).1.pop
    simp only [hc, decide_true, select_true]
    rw [toNat_sub, toNat_ofNat_zero, abs_of_neg hA0]
    generalize toNat (shr (r.push c) k).1.pop = L at *
    have hcast : ((2 ^ (w * n) : ℕ) : ℤ) = 2 ^ (w * n) := by push_cast; rfl
    generalize 2 ^ (w * n) = Mn at *
    rw [← hcast] at hlow hA1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have hA0 : 0 ≤ A := not_lt.mp (mt hneg.mpr hc)
    rw [Int.emod_eq_of_lt hA0 hA2] at hlow
    simp only [hc, decide_false, select_false]
    rw [hlow, abs_of_nonneg hA0]

end Limbs

end Bingcd
