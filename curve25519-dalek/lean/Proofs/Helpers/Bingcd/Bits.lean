module
public import Proofs.Helpers.Bingcd.Limbs
public import Mathlib.Data.Nat.Size

/-! # Bit lengths and bit fields of multi-limb integers

The bit length of a multi-limb integer, the limbs at its top, and the bitwise or of two of
them: what the approximations of the operands are read from. -/

@[expose] public section

namespace Bingcd.Limbs

variable {w n : ℕ}

/-! ### Bit length -/

/-- The bit length of `r + 2 ^ N * h` for `r < 2 ^ N` and `h > 0`. -/
theorem size_add_two_pow_mul {r h N : ℕ} (hr : r < 2 ^ N) (hh : 0 < h) :
    (r + 2 ^ N * h).size = N + h.size := by
  refine eq_of_forall_ge_iff fun j => ?_
  rw [Nat.size_le]
  by_cases hj : N ≤ j
  · obtain ⟨d, rfl⟩ : ∃ d, j = N + d := ⟨j - N, by omega⟩
    rw [Nat.add_le_add_iff_left, Nat.size_le, pow_add]
    constructor
    · intro h1
      by_contra h2
      have := Nat.mul_le_mul_left (2 ^ N) (not_lt.mp h2)
      omega
    · intro h1
      have := Nat.mul_le_mul_left (2 ^ N) (Nat.succ_le_of_lt h1)
      rw [Nat.mul_succ] at this
      omega
  · have h1 : 2 ^ j < 2 ^ N := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ N * 1 ≤ 2 ^ N * h := Nat.mul_le_mul_left _ hh
    constructor
    · intro h3
      omega
    · intro h3
      omega

/-- The bit length of a multi-limb integer: the position of its most significant nonzero
limb, plus the bit length of that limb. Every limb is visited, from the least significant
one, and each visit ends with a selection. -/
def bitLen : {n : ℕ} → Limbs w n → ℕ
  | 0, _ => 0
  | n + 1, a =>
    let l := bitLen a.pop
    let t := w * n + a.back.toNat.size
    bif a.back == 0 then l else t

theorem bitLen_eq (a : Limbs w n) : bitLen a = a.toNat.size := by
  induction n with
  | zero => simp [bitLen, toNat_zero]
  | succ n ih =>
    rw [bitLen, toNat_eq_pop_add]
    by_cases h : a.back = 0
    · rw [ih, h]; simp
    · rw [show (a.back == 0) = false by simpa using h, Bool.cond_false]
      have hpos : 0 < a.back.toNat := by
        rcases Nat.eq_zero_or_pos a.back.toNat with h0 | h0
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) h
        · exact h0
      exact (size_add_two_pow_mul (toNat_lt a.pop) hpos).symm

/-! ### Bit fields -/

/-- Limb `i`, or zero beyond the last limb. Every limb is visited, and the wanted one is kept
by a selection. -/
def limbD : {n : ℕ} → Limbs w n → ℕ → Word w
  | 0, _, _ => 0
  | n + 1, a, i => Word.select (decide (i = n)) a.back (limbD a.pop i)

theorem limbD_eq (a : Limbs w n) (i : ℕ) : limbD a i = if h : i < n then a[i] else 0 := by
  induction n with
  | zero => simp [limbD]
  | succ n ih =>
    rw [limbD, ih, Word.select_eq]
    by_cases h1 : i = n
    · subst h1
      simp [Vector.back]
    · by_cases h2 : i < n
      · simp [h1, h2, show i < n + 1 by omega]
      · simp [h1, h2, show ¬i < n + 1 by omega]

theorem getLsbD_limbD (a : Limbs w n) (i : ℕ) {j : ℕ} (hj : j < w) :
    (limbD a i).getLsbD j = a.toNat.testBit (w * i + j) := by
  rw [limbD_eq]
  split
  · next h =>
    rw [BitVec.getLsbD, toNat_getElem a _ h, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
      decide_eq_true hj, Bool.true_and, Nat.add_comm]
  · next h =>
    have e : (0 : Word w).getLsbD j = false := by simp
    rw [e]
    symm
    apply Nat.testBit_lt_two_pow
    refine (toNat_lt a).trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
    have := Nat.mul_le_mul_left w (not_lt.mp h)
    omega

/-- The `w` bits of `a` starting at bit `p`, as a word: the bits of limb `p / w` from position
`p % w` upwards, completed by the low bits of the next limb. -/
def extract (a : Limbs w n) (p : ℕ) : Word w :=
  (limbD a (p / w) >>> (p % w)) ||| (limbD a (p / w + 1) <<< (w - p % w))

theorem extract_eq (hw : 0 < w) (a : Limbs w n) (p : ℕ) :
    extract a p = BitVec.ofNat w (a.toNat / 2 ^ p) := by
  have hr : p % w < w := Nat.mod_lt _ hw
  have hp := Nat.div_add_mod p w
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extract, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat, Nat.testBit_div_two_pow, hi, decide_true, Bool.true_and]
  by_cases h : p % w + i < w
  · rw [getLsbD_limbD _ _ h]
    have : i < w - p % w := by omega
    simp only [this, decide_true, Bool.not_true, Bool.false_and, Bool.or_false]
    congr 1
    omega
  · have h1 : ¬i < w - p % w := by omega
    rw [BitVec.getLsbD_of_ge _ _ (by omega), getLsbD_limbD _ _ (by omega : i - (w - p % w) < w)]
    simp only [h1, decide_false, Bool.not_false, Bool.true_and, Bool.false_or]
    congr 1
    rw [Nat.mul_succ]
    omega

theorem toNat_extract (hw : 0 < w) (a : Limbs w n) (p : ℕ) :
    (extract a p).toNat = a.toNat / 2 ^ p % 2 ^ w := by
  rw [extract_eq hw, BitVec.toNat_ofNat]

/-! ### Bitwise or -/

/-- The bit length of a bitwise or is the larger of the two bit lengths. -/
theorem size_or (x y : ℕ) : (x ||| y).size = max x.size y.size := by
  refine le_antisymm ?_ (max_le (Nat.size_le_size Nat.left_le_or)
    (Nat.size_le_size Nat.right_le_or))
  rw [Nat.size_le]
  exact Nat.or_lt_two_pow
    ((Nat.lt_size_self x).trans_le (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)))
    ((Nat.lt_size_self y).trans_le (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)))

/-- The limb-wise or. -/
def or (a b : Limbs w n) : Limbs w n := Vector.zipWith (· ||| ·) a b

theorem toNat_or (a b : Limbs w n) : toNat (or a b) = a.toNat ||| b.toNat := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have h : ∀ x : Limbs 0 n, x.toNat = 0 := fun x => by
      have := toNat_lt x
      simpa using this
    rw [h, h a, h b]
    rfl
  · apply Nat.eq_of_testBit_eq
    intro i
    have hr := Nat.mod_lt i hw
    rw [Nat.testBit_or, ← Nat.div_add_mod i w, ← getLsbD_limbD _ _ hr, ← getLsbD_limbD _ _ hr,
      ← getLsbD_limbD _ _ hr, limbD_eq, limbD_eq, limbD_eq]
    split
    · simp [or]
    · simp

theorem bitLen_or (a b : Limbs w n) : bitLen (or a b) = max (bitLen a) (bitLen b) := by
  rw [bitLen_eq, bitLen_eq, bitLen_eq, toNat_or, size_or]

/-! ### The limbs at the top of another number -/

/-- The position of the most significant nonzero limb, and `0` if there is none. -/
def topIdx : {n : ℕ} → Limbs w n → ℕ
  | 0, _ => 0
  | n + 1, m => bif m.back == 0 then topIdx m.pop else n

/-- The limb of `a` at the position of the most significant nonzero limb of `m`, and the limb
of `a` just below it; both are `0` when no limb of `m` above the least significant one is
nonzero. Every limb is visited, from the least significant one, and each visit ends with two
selections. -/
def topTwo : {n : ℕ} → Limbs w n → Limbs w n → Word w × Word w
  | 0, _, _ => (0, 0)
  | 1, _, _ => (0, 0)
  | n + 2, m, a =>
    let ap : Limbs w (n + 1) := a.pop
    let r := topTwo (m.pop : Limbs w (n + 1)) ap
    (Word.select (m.back == 0) r.1 a.back, Word.select (m.back == 0) r.2 ap.back)

theorem topIdx_le (m : Limbs w n) : topIdx m ≤ n - 1 := by
  induction n with
  | zero => simp [topIdx]
  | succ n ih =>
    rw [topIdx]
    cases m.back == 0
    · simp
    · have := ih m.pop
      simp only [Bool.cond_true]
      omega

/-- Below the last limb, `limbD` does not see the last limb. -/
theorem limbD_pop (a : Limbs w (n + 1)) {i : ℕ} (hi : i ≠ n) : limbD a i = limbD a.pop i := by
  rw [limbD]
  simp [hi]

theorem toNat_lt_two_pow_topIdx (m : Limbs w n) : m.toNat < 2 ^ (w * (topIdx m + 1)) := by
  induction n with
  | zero => rw [toNat_zero]; positivity
  | succ n ih =>
    rw [topIdx]
    by_cases h : m.back = 0
    · have h0 : m.toNat = toNat m.pop := by rw [toNat_eq_pop_add, h]; simp
      rw [show (m.back == 0) = true by simpa using h, Bool.cond_true, h0]
      exact ih m.pop
    · rw [show (m.back == 0) = false by simpa using h, Bool.cond_false]
      exact toNat_lt m

theorem limbD_topIdx_ne_zero (m : Limbs w n) (h : topIdx m ≠ 0) : limbD m (topIdx m) ≠ 0 := by
  induction n with
  | zero => exact absurd rfl h
  | succ n ih =>
    rw [topIdx] at h ⊢
    by_cases hb : m.back = 0
    · rw [show (m.back == 0) = true by simpa using hb, Bool.cond_true] at h ⊢
      have hle := topIdx_le m.pop
      rw [limbD_pop m (by omega)]
      exact ih m.pop h
    · rw [show (m.back == 0) = false by simpa using hb, Bool.cond_false]
      rw [limbD]
      simpa using hb

/-- The bit length of `m`, from its most significant nonzero limb. -/
theorem size_toNat_eq (m : Limbs w n) (h : topIdx m ≠ 0) :
    m.toNat.size = w * topIdx m + (limbD m (topIdx m)).toNat.size := by
  have hle := topIdx_le m
  have hlt : topIdx m < n := by omega
  have hne := limbD_topIdx_ne_zero m h
  have hbound : m.toNat / 2 ^ (w * topIdx m) < 2 ^ w := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm, ← Nat.mul_succ]
    exact toNat_lt_two_pow_topIdx m
  have hval : (limbD m (topIdx m)).toNat = m.toNat / 2 ^ (w * topIdx m) := by
    rw [limbD_eq]
    simp only [hlt, ↓reduceDIte]
    rw [toNat_getElem, Nat.mod_eq_of_lt hbound]
  have hpos : 0 < m.toNat / 2 ^ (w * topIdx m) := by
    rw [← hval]
    rcases Nat.eq_zero_or_pos (limbD m (topIdx m)).toNat with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hne
    · exact h0
  rw [hval]
  conv_lhs => rw [← Nat.mod_add_div m.toNat (2 ^ (w * topIdx m))]
  exact size_add_two_pow_mul (Nat.mod_lt _ (by positivity)) hpos

/-- **The scan returns the two limbs at the top of `m`.** -/
theorem topTwo_eq (m a : Limbs w n) :
    topTwo m a =
      if topIdx m = 0 then (0, 0) else (limbD a (topIdx m), limbD a (topIdx m - 1)) := by
  induction n with
  | zero => simp [topTwo, topIdx]
  | succ n ih =>
    cases n with
    | zero =>
      have h : topIdx m = 0 := by
        have := topIdx_le m
        omega
      simp [topTwo, h]
    | succ n =>
      rw [topTwo, topIdx]
      by_cases hb : m.back = 0
      · have hle := topIdx_le m.pop
        simp only [show (m.back == 0) = true by simpa using hb, Bool.cond_true, Word.select_true,
          ih m.pop a.pop]
        split
        · rfl
        · rw [limbD_pop a (i := topIdx m.pop) (by omega),
            limbD_pop a (i := topIdx m.pop - 1) (by omega)]
      · simp only [show (m.back == 0) = false by simpa using hb, Bool.cond_false, Word.select_false,
          limbD_eq]
        simp [Vector.back]

end Bingcd.Limbs
