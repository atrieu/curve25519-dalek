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

/-! ### Montgomery reduction of a signed linear combination -/

/-- Shifting the signed number `r + 2 ^ (w * n) * c = 2 ^ k * A` right by `k`, as an unsigned
number on `n + 1` limbs: the result is `A`, plus a multiple of `2 ^ (w * n)` when `A` is
negative, and the sign of `A` is the sign of `c`. -/
theorem toNat_shr_push (r : Limbs w n) (c : Word w) {k : ℕ} (hk : k < w) {A : ℤ}
    (hV : (toNat r : ℤ) + 2 ^ (w * n) * c.toInt = 2 ^ k * A) :
    (c.toInt < 0 ↔ A < 0) ∧
      (toNat (shr (r.push c) k).1 : ℤ) =
        A + if c.toInt < 0 then 2 ^ (w * n) * 2 ^ (w - k) else 0 := by
  have hM : (0 : ℤ) < 2 ^ (w * n) := by positivity
  have hkpos : (0 : ℤ) < 2 ^ k := by positivity
  have hr0 : (0 : ℤ) ≤ toNat r := by positivity
  have hrM : (toNat r : ℤ) < 2 ^ (w * n) := by exact_mod_cast toNat_lt r
  constructor
  · constructor
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
  · rw [toNat_shr_fst _ hk, toNat_push]
    push_cast
    rcases Nat.lt_or_ge (2 * c.toNat) (2 ^ w) with h | h
    · have e := Word.toInt_eq_toNat_of_lt h
      have hc : ¬c.toInt < 0 := by rw [e]; exact not_lt.mpr (by positivity)
      simp only [hc, ↓reduceIte]
      rw [add_zero, ← e, hV, Int.mul_ediv_cancel_left _ hkpos.ne']
    · have e := Word.toInt_eq_toNat_sub_of_le h
      have hc : c.toInt < 0 := by
        have : (c.toNat : ℤ) < 2 ^ w := by exact_mod_cast c.isLt
        rw [e]
        linarith
      have hpow : (2 : ℤ) ^ w = 2 ^ k * 2 ^ (w - k) := by
        rw [← pow_add, show k + (w - k) = w by omega]
      simp only [hc, ↓reduceIte]
      rw [show (toNat r : ℤ) + 2 ^ (w * n) * (c.toNat : ℤ) =
        2 ^ k * (A + 2 ^ (w * n) * 2 ^ (w - k)) by rw [e] at hV; linear_combination hV +
          2 ^ (w * n) * hpow, Int.mul_ediv_cancel_left _ hkpos.ne']

/-- The end of a Montgomery reduction: shift right by `k`, then add `m` if the result is
negative, or subtract `m` if it is at least `m`. -/
def redcTail (r : Limbs w n) (c : Word w) (m : Limbs w n) (k : ℕ) : Limbs w n :=
  let sh := (shr (r.push c) k).1
  select c.msb (add sh.pop m) (condSub sh.pop (decide (sh.back.toNat ≠ 0)) m)

theorem redcTail_spec (r : Limbs w n) (c : Word w) (m : Limbs w n) {k : ℕ} (hk : k < w) {A : ℤ}
    (hV : (toNat r : ℤ) + 2 ^ (w * n) * c.toInt = 2 ^ k * A) (hA1 : -(m.toNat : ℤ) < A)
    (hA2 : A < 2 * m.toNat) : (toNat (redcTail r c m k) : ℤ) = A % m.toNat := by
  obtain ⟨hneg, hsh⟩ := toNat_shr_push r c hk hV
  have hmsb : c.msb = decide (c.toInt < 0) := BitVec.msb_eq_toInt
  have hmM := toNat_lt m
  have hpop := toNat_pop (shr (r.push c) k).1
  have hback := toNat_back (shr (r.push c) k).1
  simp only [redcTail, hmsb]
  generalize (shr (r.push c) k).1 = sh at *
  generalize sh.pop = L at *
  generalize sh.back = top at *
  have hcast : ((2 ^ (w * n) : ℕ) : ℤ) = 2 ^ (w * n) := by push_cast; rfl
  by_cases hc : c.toInt < 0
  · have hA0 := hneg.mp hc
    simp only [hc, decide_true, select_true, ite_true] at hsh ⊢
    have hL : (toNat L : ℤ) = A + 2 ^ (w * n) := by
      rw [hpop]
      push_cast
      rw [hsh, Int.add_mul_emod_self_left, ← Int.add_emod_right,
        Int.emod_eq_of_lt (by rw [← hcast]; omega) (by linarith)]
    rw [toNat_add, ← Int.add_emod_right, Int.emod_eq_of_lt (by linarith) (by linarith)]
    generalize 2 ^ (w * n) = Mn at *
    rw [← hcast] at hL
    have : (toNat L + m.toNat) % Mn = toNat L + m.toNat - Mn := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · have hA0 : 0 ≤ A := not_lt.mp (mt hneg.mpr hc)
    simp only [hc, decide_false, select_false, ite_false, add_zero] at hsh ⊢
    have hlt : sh.toNat < 2 * m.toNat := by omega
    have hdiv : sh.toNat / 2 ^ (w * n) ≤ 1 := by
      have : sh.toNat / 2 ^ (w * n) < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]
        omega
      omega
    have hcarry : (decide (top.toNat ≠ 0)).toNat = sh.toNat / 2 ^ (w * n) := by
      rw [hback]
      rcases Nat.eq_zero_or_pos (sh.toNat / 2 ^ (w * n)) with h0 | h0
      · simp [h0]
      · have h1 : sh.toNat / 2 ^ (w * n) = 1 := by omega
        simp [h1]
    have hsum : toNat L + 2 ^ (w * n) * (decide (top.toNat ≠ 0)).toNat = sh.toNat := by
      rw [hcarry, hpop]
      exact Nat.mod_add_div _ _
    rw [toNat_condSub _ _ _ (by rw [hsum]; exact hlt), hsum, ← hsh]
    push_cast
    rfl

/-- `(u * f + v * g) / 2 ^ k` modulo `m`, by a Montgomery reduction: a multiple `q * m` of the
modulus, with `q < 2 ^ k` computed from the low word and `ninv = -1 / m` modulo `2 ^ w`, makes
the sum divisible by `2 ^ k`; the quotient is then brought into `[0, m)` by adding or
subtracting `m` once. -/
def linCombRedc (u v : Limbs w (n + 1)) (f g : Word w) (m : Limbs w (n + 1)) (ninv : Word w)
    (k : ℕ) : Limbs w (n + 1) :=
  let r := linComb u v f g
  let q := (r.1[0] * ninv) &&& BitVec.ofNat w (2 ^ k - 1)
  let s := mulAddRow r.1 m q 0#w
  redcTail s.1 (s.2 + r.2) m k

/-- For `k + 3 ≤ w`, `|f| + |g| ≤ 2 ^ k`, reduced `u`, `v` and `m * ninv ≡ -1` modulo `2 ^ w`,
the result `R` of `linCombRedc` is reduced and `2 ^ k * R ≡ u * f + v * g` modulo `m`. -/
theorem linCombRedc_spec {k : ℕ} (hk : k + 3 ≤ w) (u v m : Limbs w (n + 1)) (f g ninv : Word w)
    (hfg : |f.toInt| + |g.toInt| ≤ 2 ^ k) (hu : u.toNat < m.toNat) (hv : v.toNat < m.toNat)
    (hinv : (m.toNat * ninv.toNat + 1) % 2 ^ w = 0) :
    toNat (linCombRedc u v f g m ninv k) < m.toNat ∧
      2 ^ k * (toNat (linCombRedc u v f g m ninv k) : ℤ) ≡
        u.toNat * f.toInt + v.toNat * g.toInt [ZMOD m.toNat] := by
  have hw2 : (2 : ℤ) ^ (k + 3) ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) hk
  rw [pow_succ, pow_succ, pow_succ] at hw2
  have hkpos : (0 : ℤ) < 2 ^ k := by positivity
  have hKw : 2 ^ k ∣ 2 ^ w := pow_dvd_pow 2 (by omega)
  have h2kw : 2 * 2 ^ k ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : k + 1 ≤ w)
    rwa [pow_succ, mul_comm] at this
  have hmlt := toNat_lt m
  obtain ⟨hT, hc⟩ := linComb_spec u v f g hfg (by linarith)
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  have hdef : linCombRedc u v f g m ninv k =
      redcTail (mulAddRow (linComb u v f g).1 m
        (((linComb u v f g).1[0] * ninv) &&& BitVec.ofNat w (2 ^ k - 1)) 0#w).1
        ((mulAddRow (linComb u v f g).1 m
          (((linComb u v f g).1[0] * ninv) &&& BitVec.ofNat w (2 ^ k - 1)) 0#w).2 +
          (linComb u v f g).2) m k := rfl
  rw [hdef]
  generalize linComb u v f g = rc at *
  obtain ⟨r, c⟩ := rc
  dsimp only at hT hc hc1 hc2 ⊢
  obtain ⟨q, hqdef⟩ : ∃ q, q = (r[0] * ninv) &&& BitVec.ofNat w (2 ^ k - 1) := ⟨_, rfl⟩
  rw [← hqdef]
  have hq : q.toNat = r[0].toNat * ninv.toNat % 2 ^ k := by
    rw [hqdef, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_mul, Nat.mod_mod_of_dvd _ hKw]
  have hqlt : q.toNat < 2 ^ k := hq ▸ Nat.mod_lt _ (by positivity)
  have hs := mulAddRow_spec r m q 0#w
  generalize mulAddRow r m q 0#w = s at *
  obtain ⟨s1, s2⟩ := s
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at hs
  -- the carry of `r + m * q` is below `2 ^ k`
  have hs2 : s2.toNat < 2 ^ k := by
    have hrlt := toNat_lt r
    have h1 : m.toNat * q.toNat ≤ m.toNat * (2 ^ k - 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : m.toNat * (2 ^ k - 1) ≤ 2 ^ (w * (n + 1)) * (2 ^ k - 1) :=
      Nat.mul_le_mul_right _ hmlt.le
    have h3 : 2 ^ (w * (n + 1)) * (2 ^ k - 1) + 2 ^ (w * (n + 1)) = 2 ^ (w * (n + 1)) * 2 ^ k := by
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [Nat.mul_sub, Nat.mul_one]
      have := Nat.mul_le_mul_left (2 ^ (w * (n + 1))) h1
      omega
    by_contra hge
    have := Nat.mul_le_mul_left (2 ^ (w * (n + 1))) (not_lt.mp hge)
    omega
  have hs2i : s2.toInt = s2.toNat := Word.toInt_eq_toNat_of_lt (by omega)
  have hs2z : (s2.toNat : ℤ) < 2 ^ k := by exact_mod_cast hs2
  have ht : (s2 + c).toInt = s2.toNat + c.toInt := by
    rw [Word.toInt_add_of_inSRange (by rw [hs2i]; exact ⟨by linarith, by linarith⟩), hs2i]
  have hs' : (toNat s1 : ℤ) + 2 ^ (w * (n + 1)) * s2.toNat = toNat r + m.toNat * q.toNat := by
    exact_mod_cast hs
  have hV : (toNat s1 : ℤ) + 2 ^ (w * (n + 1)) * (s2 + c).toInt =
      (u.toNat * f.toInt + v.toNat * g.toInt) + m.toNat * q.toNat := by
    rw [ht]
    linear_combination hs' + hT
  -- `r + m * q` is divisible by `2 ^ k`
  obtain ⟨B, hB⟩ : ∃ B : ℕ, toNat r + m.toNat * q.toNat = 2 ^ k * B := by
    have h1 : toNat r ≡ r[0].toNat [MOD 2 ^ k] := by
      have := (Nat.mod_modEq (toNat r) (2 ^ w)).symm.of_dvd hKw
      rwa [toNat_mod_two_pow] at this
    have h2 : q.toNat ≡ r[0].toNat * ninv.toNat [MOD 2 ^ k] := by
      rw [hq]
      exact Nat.mod_modEq _ _
    have h3 : m.toNat * ninv.toNat + 1 ≡ 0 [MOD 2 ^ k] :=
      (Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_of_mod_eq_zero hinv)).of_dvd hKw
    have h4 : toNat r + m.toNat * q.toNat ≡ 0 [MOD 2 ^ k] := by
      calc toNat r + m.toNat * q.toNat
          ≡ r[0].toNat + m.toNat * (r[0].toNat * ninv.toNat) [MOD 2 ^ k] :=
            h1.add (h2.mul_left _)
        _ = r[0].toNat * (m.toNat * ninv.toNat + 1) := by ring
        _ ≡ r[0].toNat * 0 [MOD 2 ^ k] := h3.mul_left _
        _ = 0 := by ring
    exact Nat.modEq_zero_iff_dvd.mp h4
  obtain ⟨M', hM'⟩ : ∃ M' : ℤ, (2 : ℤ) ^ (w * (n + 1)) = 2 ^ k * M' := by
    refine ⟨2 ^ (w * (n + 1) - k), ?_⟩
    rw [← pow_add]
    congr 1
    have : w ≤ w * (n + 1) := Nat.le_mul_of_pos_right w (by omega)
    omega
  have hB' : (toNat r : ℤ) + m.toNat * q.toNat = 2 ^ k * B := by exact_mod_cast hB
  have hA : (u.toNat : ℤ) * f.toInt + v.toNat * g.toInt + m.toNat * q.toNat =
      2 ^ k * (B + M' * c.toInt) := by
    linear_combination hB' - hT + c.toInt * hM'
  generalize (B : ℤ) + M' * c.toInt = A at hA
  -- `-m < A < 2 * m`
  have hu' : (u.toNat : ℤ) ≤ m.toNat - 1 := by omega
  have hv' : (v.toNat : ℤ) ≤ m.toNat - 1 := by omega
  have hm0 : (0 : ℤ) ≤ m.toNat - 1 := by omega
  have hTb : |(u.toNat : ℤ) * f.toInt + v.toNat * g.toInt| ≤ (m.toNat - 1) * 2 ^ k := by
    calc |(u.toNat : ℤ) * f.toInt + v.toNat * g.toInt|
        ≤ |(u.toNat : ℤ) * f.toInt| + |(v.toNat : ℤ) * g.toInt| := abs_add_le _ _
      _ = u.toNat * |f.toInt| + v.toNat * |g.toInt| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ u.toNat),
            abs_of_nonneg (by positivity : (0 : ℤ) ≤ v.toNat)]
      _ ≤ (m.toNat - 1) * |f.toInt| + (m.toNat - 1) * |g.toInt| :=
          add_le_add (mul_le_mul_of_nonneg_right hu' (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hv' (abs_nonneg _))
      _ = (m.toNat - 1) * (|f.toInt| + |g.toInt|) := by ring
      _ ≤ (m.toNat - 1) * 2 ^ k := mul_le_mul_of_nonneg_left hfg hm0
  obtain ⟨hT1, hT2⟩ := abs_le.mp hTb
  have hq0 : (0 : ℤ) ≤ q.toNat := by positivity
  have hq1 : (q.toNat : ℤ) ≤ 2 ^ k - 1 := by
    have : (q.toNat : ℤ) < 2 ^ k := by exact_mod_cast hqlt
    linarith
  have hmq0 : (0 : ℤ) ≤ m.toNat * q.toNat := by positivity
  have hmq1 : (m.toNat : ℤ) * q.toNat ≤ m.toNat * (2 ^ k - 1) :=
    mul_le_mul_of_nonneg_left hq1 (by positivity)
  have hA1 : -(m.toNat : ℤ) < A := by
    refine lt_of_mul_lt_mul_left ?_ hkpos.le
    linarith
  have hA2 : A < 2 * m.toNat := by
    refine lt_of_mul_lt_mul_left ?_ hkpos.le
    linarith
  have key := redcTail_spec s1 (s2 + c) m (by omega : k < w) (hV.trans hA) hA1 hA2
  have hmpos : (0 : ℤ) < m.toNat := by omega
  constructor
  · zify
    rw [key]
    exact Int.emod_lt_of_pos _ hmpos
  · rw [key]
    calc 2 ^ k * (A % m.toNat) ≡ 2 ^ k * A [ZMOD m.toNat] := (Int.mod_modEq _ _).mul_left _
      _ = u.toNat * f.toInt + v.toNat * g.toInt + m.toNat * q.toNat := hA.symm
      _ ≡ u.toNat * f.toInt + v.toNat * g.toInt [ZMOD m.toNat] :=
          Int.modEq_iff_dvd.mpr ⟨-q.toNat, by ring⟩

/-- A reduced `R` with `2 ^ K * R ≡ X` modulo an odd `m` is `X * ((m + 1) / 2) ^ K mod m`. -/
theorem eq_mul_half_pow_emod {m R K : ℕ} (hodd : m % 2 = 1) (hR : R < m) {X : ℤ}
    (h : 2 ^ K * (R : ℤ) ≡ X [ZMOD m]) : (R : ℤ) = X * (((m + 1) / 2 : ℕ) : ℤ) ^ K % m := by
  have h2 : (2 : ℤ) * (((m + 1) / 2 : ℕ) : ℤ) = m + 1 := by omega
  have h1 : ((m : ℤ) + 1) ≡ 1 [ZMOD m] := Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
  have key : X * (((m + 1) / 2 : ℕ) : ℤ) ^ K ≡ R [ZMOD m] := by
    calc X * (((m + 1) / 2 : ℕ) : ℤ) ^ K
        ≡ 2 ^ K * (R : ℤ) * (((m + 1) / 2 : ℕ) : ℤ) ^ K [ZMOD m] := h.symm.mul_right _
      _ = (2 * (((m + 1) / 2 : ℕ) : ℤ)) ^ K * R := by rw [mul_pow]; ring
      _ ≡ 1 ^ K * R [ZMOD m] := by rw [h2]; exact (h1.pow K).mul_right _
      _ = R := by ring
  rw [key, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hR)]

end Limbs

end Bingcd
