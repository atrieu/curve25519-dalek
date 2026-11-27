module
public import Proofs.Helpers.Bingcd.Word
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.LinearCombination

/-! # Multi-limb integers

The functions of `bingcd.rs` on four limbs, and on eight for the 32-bit backend, are specified
by functions on vectors of words, for any bitwidth `w` and any number `n` of limbs:
`Limbs w n := Vector (Word w) n`, least significant limb first, with the value `Limbs.toNat`. -/

@[expose] public section

/-! ## Limbs and their value -/

namespace Bingcd

/-- An unsigned integer of `n` limbs of `w` bits each, least significant limb first. -/
abbrev Limbs (w n : ℕ) : Type := Vector (Word w) n

namespace Limbs

variable {w n m : ℕ}

/-! ### Evaluation -/

/-- The limbs as a list of natural-number digits, least significant first. -/
def digits (a : Limbs w n) : List ℕ := a.toList.map BitVec.toNat

/-- The value of `a` in radix `r`: `∑ i, a[i] * r ^ i`. -/
def eval (r : ℕ) (a : Limbs w n) : ℕ := Nat.ofDigits r a.digits

/-- The value of `a` as a natural number, in radix `2 ^ w`. -/
def toNat (a : Limbs w n) : ℕ := eval (2 ^ w) a

theorem eval_push (r : ℕ) (a : Limbs w n) (x : Word w) :
    eval r (a.push x) = eval r a + r ^ n * x.toNat := by
  simp [eval, digits, Vector.toList_push, Nat.ofDigits_append]

@[simp] theorem toNat_empty : toNat (#v[] : Limbs w 0) = 0 := rfl

theorem toNat_zero (a : Limbs w 0) : a.toNat = 0 := by
  rw [Vector.eq_empty (xs := a), toNat_empty]

theorem toNat_push (a : Limbs w n) (x : Word w) :
    toNat (a.push x) = a.toNat + 2 ^ (w * n) * x.toNat := by
  rw [toNat, eval_push, pow_mul, toNat]

/-- A nonempty limb vector splits into its low limbs and its most significant limb. -/
theorem toNat_eq_pop_add (a : Limbs w (n + 1)) :
    a.toNat = toNat a.pop + 2 ^ (w * n) * a.back.toNat := by
  conv_lhs => rw [← Vector.push_pop_back a]
  exact toNat_push _ _

/-- A nonempty limb vector splits into its least significant limb and its high limbs. -/
theorem toNat_eq_head_add (a : Limbs w (n + 1)) :
    a.toNat = a[0].toNat + 2 ^ w * toNat a.tail := by
  rcases a with ⟨⟨l⟩, h⟩
  cases l with
  | nil => simp at h
  | cons x l =>
    obtain rfl : l.length = n := by simpa using h
    simp [toNat, eval, digits, Nat.ofDigits_cons, Vector.tail]

/-- Replacing the least significant limb. -/
theorem toNat_set_zero (a : Limbs w (n + 1)) (x : Word w) :
    toNat (a.set 0 x) = x.toNat + 2 ^ w * toNat a.tail := by
  rw [toNat_eq_head_add, Vector.getElem_set_self]
  congr 3
  ext i hi : 1
  simp only [Vector.tail_eq_cast_extract, Vector.getElem_cast, Vector.getElem_extract]
  exact Vector.getElem_set_ne _ _ (by omega)

/-! ### Splitting -/

/-- The value modulo `2 ^ w` is the least significant limb. -/
theorem toNat_mod_two_pow (a : Limbs w (n + 1)) : a.toNat % 2 ^ w = a[0].toNat := by
  rw [toNat_eq_head_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a[0].isLt]

/-- Induction on limb vectors by pushing a most significant limb. -/
@[elab_as_elim]
theorem induction {motive : ∀ n, Limbs w n → Prop} (empty : motive 0 #v[])
    (push : ∀ n (a : Limbs w n) (x : Word w), motive n a → motive (n + 1) (a.push x)) :
    ∀ {n} (a : Limbs w n), motive n a
  | 0, a => by rw [Vector.eq_empty (xs := a)]; exact empty
  | n + 1, a => by
    rw [← Vector.push_pop_back a]
    exact push n _ _ (induction empty push _)

/-! ### Bounds and limb extraction -/

theorem toNat_lt (a : Limbs w n) : a.toNat < 2 ^ (w * n) := by
  induction a using Limbs.induction with
  | empty => simp
  | push n a x ih =>
    rw [toNat_push, Nat.mul_succ, pow_add]
    have hx := x.isLt
    nlinarith [Nat.two_pow_pos (w * n)]

theorem toNat_pop (a : Limbs w (n + 1)) : toNat a.pop = a.toNat % 2 ^ (w * n) := by
  rw [toNat_eq_pop_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (toNat_lt (n := n) a.pop)]

/-- Limb `i` holds the bits `w * i, …, w * i + w - 1` of the value. -/
theorem toNat_getElem (a : Limbs w n) (i : ℕ) (hi : i < n) :
    a[i].toNat = a.toNat / 2 ^ (w * i) % 2 ^ w := by
  induction a using Limbs.induction with
  | empty => omega
  | push n a x ih =>
    rw [Vector.getElem_push, toNat_push]
    split
    · next h =>
      obtain ⟨k, rfl⟩ : ∃ k, n = i + (k + 1) := ⟨n - i - 1, by omega⟩
      rw [ih h, show 2 ^ (w * (i + (k + 1))) * x.toNat
        = 2 ^ (w * i) * (2 ^ w * (2 ^ (w * k) * x.toNat)) by ring,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_left]
    · next h =>
      obtain rfl : i = n := by omega
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (toNat_lt _),
        Nat.zero_add, Nat.mod_eq_of_lt x.isLt]

theorem toNat_injective : Function.Injective (toNat : Limbs w n → ℕ) := by
  intro a b h
  ext i hi : 1
  apply BitVec.eq_of_toNat_eq
  rw [toNat_getElem, toNat_getElem, h]

/-! ### Conversion from natural numbers -/

/-- The `n` low limbs of a natural number. -/
def ofNat : (n : ℕ) → ℕ → Limbs w n
  | 0, _ => #v[]
  | n + 1, x => (ofNat n x).push (BitVec.ofNat w (x / 2 ^ (w * n)))

theorem toNat_ofNat (n x : ℕ) : (ofNat n x : Limbs w n).toNat = x % 2 ^ (w * n) := by
  induction n with
  | zero => simp [ofNat, Nat.mod_one]
  | succ n ih =>
    rw [ofNat, toNat_push, ih, BitVec.toNat_ofNat, Nat.mul_succ, pow_add, Nat.mod_mul]

/-- The zero of `n` limbs is `ofNat n 0`. -/
@[simp] theorem toNat_ofNat_zero : (ofNat n 0 : Limbs w n).toNat = 0 := by simp [toNat_ofNat]

end Limbs

end Bingcd

/-! ## Subtraction

Ripple-borrow subtraction of multi-limb integers, built from the one-word primitive
`Word.subb`. -/

namespace Bingcd.Limbs

variable {w n : ℕ}

/-- Subtract with borrow: ripple the borrow from the least to the most significant limb. -/
def subb : {n : ℕ} → Limbs w n → Limbs w n → Bool → Limbs w n × Bool
  | 0, _, _, c => (#v[], c)
  | _ + 1, a, b, c =>
    let r := subb a.pop b.pop c
    let s := Word.subb a.back b.back r.2
    (r.1.push s.1, s.2)

theorem subb_spec (a b : Limbs w n) (c : Bool) :
    (toNat (subb a b c).1 : ℤ) - 2 ^ (w * n) * (subb a b c).2.toNat =
      a.toNat - b.toNat - c.toNat := by
  induction n with
  | zero => simp [subb, toNat_zero]
  | succ n ih =>
    have h₁ := ih a.pop b.pop
    have h₂ := Word.subb_spec a.back b.back (subb a.pop b.pop c).2
    simp only [subb, toNat_push, Nat.add_one_sub_one]
    rw [toNat_eq_pop_add a, toNat_eq_pop_add b, Nat.mul_succ, pow_add]
    push_cast
    linear_combination h₁ + 2 ^ (w * n) * h₂

/-- The borrow out is set exactly when the true difference is negative. -/
theorem subb_snd (a b : Limbs w n) (c : Bool) :
    (subb a b c).2 = decide (a.toNat < b.toNat + c.toNat) := by
  have h := subb_spec a b c
  have hr := toNat_lt (subb a b c).1
  have ha := toNat_lt a
  have hpos : (0 : ℤ) < 2 ^ (w * n) := by positivity
  cases hb : (subb a b c).2 <;> simp only [hb, Bool.toNat_false, Bool.toNat_true] at h
  · symm; rw [decide_eq_false_iff_not]; omega
  · symm; rw [decide_eq_true_iff]; zify at hr ha ⊢; omega

/-- Wrapping subtraction. -/
def sub (a b : Limbs w n) : Limbs w n := (subb a b false).1

/-- Subtraction is exact when it does not underflow. -/
theorem toNat_sub_of_le {a b : Limbs w n} (h : b.toNat ≤ a.toNat) :
    toNat (sub a b) = a.toNat - b.toNat := by
  have hs := subb_spec a b false
  have hb : (subb a b false).2 = false := by
    rw [subb_snd, decide_eq_false_iff_not]; simp only [Bool.toNat_false]; omega
  rw [hb] at hs
  simp only [Bool.toNat_false] at hs
  rw [sub]
  omega

/-- On underflow, subtraction wraps around by `2 ^ (w * n)`. -/
theorem toNat_sub_of_lt {a b : Limbs w n} (h : a.toNat < b.toNat) :
    toNat (sub a b) = a.toNat + 2 ^ (w * n) - b.toNat := by
  have hs := subb_spec a b false
  have hb : (subb a b false).2 = true := by
    rw [subb_snd, decide_eq_true_iff]; simp only [Bool.toNat_false]; omega
  rw [hb] at hs
  simp only [Bool.toNat_false, Bool.toNat_true] at hs
  push_cast at hs
  rw [sub]
  zify [show b.toNat ≤ a.toNat + 2 ^ (w * n) from by have := toNat_lt b; omega]
  linarith

theorem toNat_sub (a b : Limbs w n) :
    toNat (sub a b) = (a.toNat + 2 ^ (w * n) - b.toNat) % 2 ^ (w * n) := by
  have hb := toNat_lt b
  rcases Nat.lt_or_ge a.toNat b.toNat with h | h
  · rw [toNat_sub_of_lt h, Nat.mod_eq_of_lt (by omega)]
  · rw [toNat_sub_of_le h, show a.toNat + 2 ^ (w * n) - b.toNat
      = a.toNat - b.toNat + 2 ^ (w * n) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by have := toNat_lt a; omega)]

end Bingcd.Limbs

/-! ## Selection

Branch-free selection between two multi-limb integers, limb by limb through `Word.select`. -/

namespace Bingcd.Limbs

variable {w n : ℕ}

/-- Branch-free selection: `a` if `c`, `b` otherwise. -/
def select (c : Bool) (a b : Limbs w n) : Limbs w n := Vector.zipWith (Word.select c) a b

@[simp] theorem select_true (a b : Limbs w n) : select true a b = a := by
  ext i hi : 1
  simp [select]

@[simp] theorem select_false (a b : Limbs w n) : select false a b = b := by
  ext i hi : 1
  simp [select]

end Bingcd.Limbs

/-! ## Division by a single word

Long division by one word, from the most significant limb down, built from the one-word
primitive `Word.div2by1`. -/

namespace Bingcd.Limbs

variable {w n : ℕ}

/-- Divide `a + 2 ^ (w * n) * r` by the word `d`, returning the quotient and the
remainder. The incoming remainder `r` must satisfy `r < d`. -/
def divRem1 : {n : ℕ} → Limbs w n → Word w → Word w → Limbs w n × Word w
  | 0, _, _, r => (#v[], r)
  | _ + 1, a, d, r =>
    let s := Word.div2by1 r a.back d
    let q := divRem1 a.pop d s.2
    (q.1.push s.1, q.2)

theorem divRem1_snd_lt (a : Limbs w n) {d r : Word w} (h : r.toNat < d.toNat) :
    (divRem1 a d r).2.toNat < d.toNat := by
  induction n generalizing r with
  | zero => exact h
  | succ n ih => exact ih a.pop (Word.div2by1_snd_lt a.back h)

theorem divRem1_spec (a : Limbs w n) {d r : Word w} (h : r.toNat < d.toNat) :
    toNat (divRem1 a d r).1 * d.toNat + (divRem1 a d r).2.toNat =
      a.toNat + 2 ^ (w * n) * r.toNat := by
  induction n generalizing r with
  | zero => simp [divRem1, toNat_zero]
  | succ n ih =>
    have h₁ := Word.div2by1_spec a.back h
    have h₂ := ih a.pop (Word.div2by1_snd_lt a.back h)
    simp only [divRem1, toNat_push, Nat.add_one_sub_one]
    rw [toNat_eq_pop_add a, Nat.mul_succ, pow_add]
    linear_combination h₂ + 2 ^ (w * n) * h₁

/-- The quotient of `a` by a nonzero word. -/
def div1 (a : Limbs w n) (d : Word w) : Limbs w n := (divRem1 a d 0#w).1

/-- The remainder of `a` by a nonzero word. -/
def mod1 (a : Limbs w n) (d : Word w) : Word w := (divRem1 a d 0#w).2

theorem div1_mod1_spec (a : Limbs w n) {d : Word w} (hd : 0 < d.toNat) :
    toNat (div1 a d) * d.toNat + (mod1 a d).toNat = a.toNat := by
  have h := divRem1_spec a (d := d) (r := 0#w) (by simpa using hd)
  simpa [div1, mod1] using h

theorem toNat_div1 (a : Limbs w n) {d : Word w} (hd : 0 < d.toNat) :
    toNat (div1 a d) = a.toNat / d.toNat := by
  have h := div1_mod1_spec a hd
  have hlt : (mod1 a d).toNat < d.toNat := divRem1_snd_lt a (by simpa using hd)
  rw [← h, Nat.mul_comm, Nat.mul_add_div hd, Nat.div_eq_of_lt hlt, Nat.add_zero]

end Bingcd.Limbs

/-! ## Right shifts

A right shift by `k < w` bits is a division by the word `2 ^ k`, an instance of the
single-word chain `divRem1`; the bits shifted out are returned as a word. -/

namespace Bingcd.Limbs

variable {w n : ℕ}

/-- The word `2 ^ k`. -/
def twoPow (w k : ℕ) : Word w := BitVec.ofNat w (2 ^ k)

theorem toNat_twoPow {k : ℕ} (hk : k < w) : (twoPow w k).toNat = 2 ^ k := by
  rw [twoPow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hk)]

/-- Shift right by `k < w` bits, returning the quotient and the bits shifted out. -/
def shr (a : Limbs w n) (k : ℕ) : Limbs w n × Word w := divRem1 a (twoPow w k) 0#w

theorem toNat_shr_fst (a : Limbs w n) {k : ℕ} (hk : k < w) :
    toNat (shr a k).1 = a.toNat / 2 ^ k := by
  have h := toNat_div1 a (d := twoPow w k) (by rw [toNat_twoPow hk]; positivity)
  rwa [toNat_twoPow hk] at h

end Bingcd.Limbs

/-! ## Conditional subtraction

A subtraction followed by a branch-free correction. -/

namespace Bingcd.Limbs

variable {w n : ℕ}

/-- Subtract `p` from `a + 2 ^ (w * n) * c` unless that would be negative. -/
def condSub (a : Limbs w n) (c : Bool) (p : Limbs w n) : Limbs w n :=
  let r := subb a p false
  select (r.2 && !c) a r.1

/-- A value below `2 * p` is reduced modulo `p` by one conditional subtraction. -/
theorem toNat_condSub (a : Limbs w n) (c : Bool) (p : Limbs w n)
    (h : a.toNat + 2 ^ (w * n) * c.toNat < 2 * p.toNat) :
    toNat (condSub a c p) = (a.toNat + 2 ^ (w * n) * c.toNat) % p.toNat := by
  have ha := toNat_lt a
  have hp := toNat_lt p
  have hr : (subb a p false).1 = sub a p := rfl
  cases c
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at h ⊢
    by_cases hlt : a.toNat < p.toNat
    · simp [condSub, subb_snd, hlt, Nat.mod_eq_of_lt hlt]
    · simp only [condSub, subb_snd, Bool.toNat_false, Nat.add_zero, hlt, decide_false,
        Bool.false_and, select_false, hr]
      rw [toNat_sub_of_le (not_lt.mp hlt), Nat.mod_eq_sub_mod (not_lt.mp hlt),
        Nat.mod_eq_of_lt (by omega)]
  · simp only [Bool.toNat_true, Nat.mul_one] at h ⊢
    simp only [condSub, Bool.not_true, Bool.and_false, select_false, hr]
    rw [toNat_sub_of_lt (by omega), Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

end Bingcd.Limbs
