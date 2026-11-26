module
public import Mathlib.Init
public import Mathlib.Data.BitVec
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.Log

/-! # Machine words

The functions of `bingcd.rs` on single words are specified by functions on bit vectors, for
any bitwidth `w`: a word is a `BitVec w`, read as a natural number by `BitVec.toNat`, or as
a signed number by `BitVec.toInt`. -/

@[expose] public section

/-! ## Unsigned words

A machine word of `w` bits is a `BitVec w`; `Word w` is a reducible synonym, so that all
of the core `BitVec` API applies. The bitwidth `w` is a variable throughout.

This section covers the *unsigned* view `BitVec.toNat` and the double-width primitives that
multi-limb arithmetic is built from. Each primitive returns its result low part first and
is specified by one exact equation over `ℕ` or `ℤ`:

* `Word.addc`: add with carry, `s + 2 ^ w * c' = a + b + c`;
* `Word.subb`: subtract with borrow, `d - 2 ^ w * b' = a - b - c`;
* `Word.mulAdd2`: multiply and add two words, `lo + 2 ^ w * hi = a * b + c + d`.
* `Word.div2by1`: divide two words by one, `q * d + r = hi * 2 ^ w + lo` when `hi < d`.

It also defines the branch-free `Word.select`. -/

namespace Bingcd

/-- A machine word of `w` bits. -/
abbrev Word (w : ℕ) : Type := BitVec w

namespace Word

variable {w : ℕ}

/-! ### Low and high halves of a natural number -/

/-- The word made of the bits `w, …, 2 * w - 1` of a natural number. -/
def highOfNat (w x : ℕ) : Word w := BitVec.ofNat w (x / 2 ^ w)

theorem toNat_ofNat_add_toNat_highOfNat {x : ℕ} (hx : x < 2 ^ w * 2 ^ w) :
    (BitVec.ofNat w x).toNat + 2 ^ w * (highOfNat w x).toNat = x := by
  have h : x / 2 ^ w < 2 ^ w := Nat.div_lt_of_lt_mul hx
  rw [highOfNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_add_div]

/-! ### Addition with carry -/

/-- Add with carry: the sum `a + b + c` as a word and a carry out. -/
def addc (a b : Word w) (c : Bool) : Word w × Bool :=
  let s := a.toNat + b.toNat + c.toNat
  (BitVec.ofNat w s, decide (2 ^ w ≤ s))

theorem addc_spec (a b : Word w) (c : Bool) :
    (addc a b c).1.toNat + 2 ^ w * (addc a b c).2.toNat = a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.toNat_le
  simp only [addc, BitVec.toNat_ofNat]
  by_cases h : 2 ^ w ≤ a.toNat + b.toNat + c.toNat
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    simp only [h, decide_true, Bool.toNat_true]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp [h]

/-! ### Subtraction with borrow -/

/-- Subtract with borrow: the difference `a - b - c` as a word and a borrow out. -/
def subb (a b : Word w) (c : Bool) : Word w × Bool :=
  (BitVec.ofNat w (a.toNat + 2 ^ w - (b.toNat + c.toNat)), decide (a.toNat < b.toNat + c.toNat))

theorem subb_spec (a b : Word w) (c : Bool) :
    ((subb a b c).1.toNat : ℤ) - 2 ^ w * (subb a b c).2.toNat = a.toNat - b.toNat - c.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.toNat_le
  simp only [subb, BitVec.toNat_ofNat]
  by_cases h : a.toNat < b.toNat + c.toNat
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [h, decide_true, Bool.toNat_true]
    push_cast [Nat.cast_sub (show b.toNat + c.toNat ≤ a.toNat + 2 ^ w by omega)]
    ring
  · have h' : a.toNat + 2 ^ w - (b.toNat + c.toNat) = a.toNat - (b.toNat + c.toNat) + 2 ^ w := by
      omega
    rw [h', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp only [h, decide_false, Bool.toNat_false]
    push_cast [Nat.cast_sub (show b.toNat + c.toNat ≤ a.toNat by omega)]
    ring

/-- The borrow out of `subb` is set exactly when the true difference is negative. -/
theorem subb_snd (a b : Word w) (c : Bool) :
    (subb a b c).2 = decide (a.toNat < b.toNat + c.toNat) := rfl

/-! ### Double-width multiplication -/

/-- `a * b + c + d` always fits in two words; this is the inner step of schoolbook and
Montgomery multiplication. The result is `(lo, hi)`. -/
def mulAdd2 (a b c d : Word w) : Word w × Word w :=
  let p := a.toNat * b.toNat + c.toNat + d.toNat
  (BitVec.ofNat w p, highOfNat w p)

theorem mulAdd2_spec (a b c d : Word w) :
    (mulAdd2 a b c d).1.toNat + 2 ^ w * (mulAdd2 a b c d).2.toNat =
      a.toNat * b.toNat + c.toNat + d.toNat := by
  apply toNat_ofNat_add_toNat_highOfNat
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have h : a.toNat * b.toNat ≤ (2 ^ w - 1) * (2 ^ w - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ w = m + 1 := ⟨2 ^ w - 1, by omega⟩
  rw [hm] at ha hb hc hd h ⊢
  simp only [Nat.add_sub_cancel] at h
  nlinarith

/-! ### Double-width division -/

/-- Divide the two-word number `(hi, lo)` by `d`, returning `(quotient, remainder)`. The
quotient fits in a word when `hi < d`; this is the step of single-word long division. -/
def div2by1 (hi lo d : Word w) : Word w × Word w :=
  let x := hi.toNat * 2 ^ w + lo.toNat
  (BitVec.ofNat w (x / d.toNat), BitVec.ofNat w (x % d.toNat))

theorem div2by1_spec {hi d : Word w} (lo : Word w) (h : hi.toNat < d.toNat) :
    (div2by1 hi lo d).1.toNat * d.toNat + (div2by1 hi lo d).2.toNat =
      hi.toNat * 2 ^ w + lo.toNat := by
  have hd := d.isLt
  have hlo := lo.isLt
  have hx : hi.toNat * 2 ^ w + lo.toNat < d.toNat * 2 ^ w := by nlinarith
  simp only [div2by1, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hx),
    Nat.mod_eq_of_lt ((Nat.mod_lt _ (by omega)).trans hd), Nat.div_add_mod']

theorem div2by1_snd_lt {hi d : Word w} (lo : Word w) (h : hi.toNat < d.toNat) :
    (div2by1 hi lo d).2.toNat < d.toNat := by
  simp only [div2by1, BitVec.toNat_ofNat]
  exact (Nat.mod_le _ _).trans_lt (Nat.mod_lt _ (by omega))

/-! ### Constant-time selection -/

/-- The all-ones word if `c`, the zero word otherwise. -/
def mask (w : ℕ) (c : Bool) : Word w := bif c then BitVec.allOnes w else 0

/-- Branch-free selection: `a` if `c`, `b` otherwise. -/
def select (c : Bool) (a b : Word w) : Word w := b ^^^ (mask w c &&& (a ^^^ b))

@[simp] theorem select_true (a b : Word w) : select true a b = a := by
  simp [select, mask, BitVec.xor_comm a b, ← BitVec.xor_assoc]

@[simp] theorem select_false (a b : Word w) : select false a b = b := by
  simp [select, mask]

theorem select_eq (c : Bool) (a b : Word w) : select c a b = bif c then a else b := by
  cases c <;> simp

theorem mask_true_and (x : Word w) : mask w true &&& x = x := BitVec.allOnes_and

theorem mask_false_and (x : Word w) : mask w false &&& x = 0 := BitVec.zero_and

/-- The mask of the parity: `0 - (a &&& 1)` is all ones if `a` is odd, and zero otherwise. -/
theorem zero_sub_and_one (a : Word w) : 0 - (a &&& 1) = mask w (decide (a.toNat % 2 = 1)) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact Subsingleton.elim _ _
  · have h1 : (1 : Word w).toNat = 1 := by
      change (BitVec.ofNat w 1).toNat = 1
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
    have h : (a &&& 1).toNat = a.toNat % 2 := by
      rw [BitVec.toNat_and, h1]
      exact Nat.and_one_is_mod _
    rcases Nat.mod_two_eq_zero_or_one a.toNat with h0 | h0
    · have e : a &&& 1 = 0 := BitVec.eq_of_toNat_eq (by rw [h, h0]; rfl)
      rw [e, h0]
      simp [mask]
    · have e : a &&& 1 = 1 := BitVec.eq_of_toNat_eq (by rw [h, h0, h1])
      rw [e, h0]
      simp [mask, BitVec.neg_one_eq_allOnes]

/-- Swapping by xor: `x ^^^ (x ^^^ y)` is `y`. -/
theorem xor_xor_cancel_left (x y : Word w) : x ^^^ (x ^^^ y) = y := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem xor_xor_cancel_right (x y : Word w) : y ^^^ (x ^^^ y) = x := by
  rw [BitVec.xor_comm x y, xor_xor_cancel_left]

/-- Doubling is a shift by one bit. -/
theorem shiftLeft_one (x : Word w) : x <<< 1 = x + x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_two]

/-! ### The ring of words -/

/-- Mathlib's isomorphism `Fin n ≃+* ZMod n` sends an element to the residue of its value. -/
theorem finEquiv_apply (n : ℕ) [NeZero n] (x : Fin n) :
    ZMod.finEquiv n x = ((x : ℕ) : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => exact (Fin.cast_val_eq_self x).symm

/-- Words of `w` bits are the integers modulo `2 ^ w`, as rings. This is the composition of
Mathlib's `BitVec.equivFin` and `ZMod.finEquiv`. -/
def equivZMod : Word w ≃+* ZMod (2 ^ w) := BitVec.equivFin.trans (ZMod.finEquiv (2 ^ w))

theorem equivZMod_apply (a : Word w) : equivZMod a = (a.toNat : ZMod (2 ^ w)) := by
  rw [equivZMod, RingEquiv.trans_apply, BitVec.equivFin_apply, finEquiv_apply]
  rfl

/-- Reading a word as a residue modulo `2 ^ w`, as a ring homomorphism. -/
def toZMod : Word w →+* ZMod (2 ^ w) := (equivZMod : Word w ≃+* ZMod (2 ^ w))

theorem toZMod_apply (a : Word w) : toZMod a = (a.toNat : ZMod (2 ^ w)) := equivZMod_apply a

theorem toZMod_injective : Function.Injective (toZMod (w := w)) := equivZMod.injective

end Word

end Bingcd

/-! ## Signed words

A signed one-word integer is the same `Word w` read in two's complement through
`BitVec.toInt`, with values in `[-2 ^ (w - 1), 2 ^ (w - 1))`. There is no separate type:
wrapping `+`, `-`, `*` and negation are the same operations for both views.

An integer `x` is representable when `Word.InSRange w x`, i.e. `-2 ^ w ≤ 2 * x < 2 ^ w`;
this form is uniform in `w` (including `w = 0`) and friendly to `omega`. -/

namespace Bingcd.Word

variable {w : ℕ}

/-! ### The signed range -/

/-- `x` is representable as a signed `w`-bit word: `-2 ^ (w - 1) ≤ x < 2 ^ (w - 1)`,
stated without the truncated subtraction. -/
def InSRange (w : ℕ) (x : ℤ) : Prop := -2 ^ w ≤ 2 * x ∧ 2 * x < 2 ^ w

/-- An integer of absolute value at most `2 ^ K` fits in a signed word of `K + 2` bits. -/
theorem inSRange_of_abs_le {K : ℕ} (hw : K + 2 ≤ w) {x : ℤ} (h : |x| ≤ 2 ^ K) :
    InSRange w x := by
  have hp : (2 : ℤ) ^ (K + 2) ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) hw
  rw [pow_succ, pow_succ] at hp
  have := abs_le.mp h
  have hK : (0 : ℤ) < 2 ^ K := by positivity
  exact ⟨by linarith, by linarith⟩

theorem toInt_ofInt_of_inSRange {x : ℤ} (h : InSRange w x) : (BitVec.ofInt w x).toInt = x := by
  rw [BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> linarith [h.1, h.2]

/-! ### Relating the two views -/

theorem toInt_eq_toNat_of_lt {a : Word w} (h : 2 * a.toNat < 2 ^ w) : a.toInt = a.toNat := by
  simp only [BitVec.toInt_eq_toNat_cond, h, ↓reduceIte]

theorem toInt_eq_toNat_sub_of_le {a : Word w} (h : 2 ^ w ≤ 2 * a.toNat) :
    a.toInt = a.toNat - 2 ^ w := by
  simp only [BitVec.toInt_eq_toNat_cond, show ¬2 * a.toNat < 2 ^ w by omega, ↓reduceIte]
  push_cast
  rfl

/-! ### Wrapping operations are exact in range -/

theorem toInt_add_of_inSRange {a b : Word w} (h : InSRange w (a.toInt + b.toInt)) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [BitVec.toInt_add]
  apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> linarith [h.1, h.2]

theorem toInt_sub_of_inSRange {a b : Word w} (h : InSRange w (a.toInt - b.toInt)) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [BitVec.toInt_sub]
  apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> linarith [h.1, h.2]

theorem toInt_neg_of_inSRange {a : Word w} (h : InSRange w (-a.toInt)) :
    (-a).toInt = -a.toInt := by
  rw [BitVec.toInt_neg]
  apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> linarith [h.1, h.2]

theorem toInt_add_self {x : Word w} (h : InSRange w (2 * x.toInt)) :
    (x + x).toInt = 2 * x.toInt := by
  rw [two_mul] at h ⊢
  exact toInt_add_of_inSRange h

end Bingcd.Word

/-! ## The constant of a Montgomery reduction

Montgomery reduction needs the inverse of the (odd) modulus modulo `2 ^ w`.
`Word.invNewton x k` computes it by `k` Newton (Hensel) steps `y ↦ y * (2 - x * y)`, each of
which doubles the number of correct low bits: `1 - x * y'` is the square of `1 - x * y`.

* `Word.mul_inv`: `x * inv x = 1` for odd `x`.
* `Word.negInv_spec`: `x * negInv x + 1` is a multiple of `2 ^ w`. -/

namespace Bingcd.Word

variable {w : ℕ}

/-! ### Inverse modulo `2 ^ w` -/

/-- `k` Newton steps towards the inverse of `x` modulo `2 ^ w`, starting from `1`. -/
def invNewton (x : Word w) : ℕ → Word w
  | 0 => 1
  | k + 1 => invNewton x k * (2 - x * invNewton x k)

/-- Each Newton step squares the error. -/
theorem one_sub_mul_invNewton (x : Word w) (k : ℕ) :
    1 - x * invNewton x k = (1 - x) ^ 2 ^ k := by
  induction k with
  | zero => simp [invNewton]
  | succ k ih =>
    rw [pow_succ, pow_mul, ← ih, invNewton]
    ring

/-- `2 ^ k = 0` in `Word w` as soon as `w ≤ k`. -/
theorem two_pow_eq_zero {k : ℕ} (h : w ≤ k) : (2 : Word w) ^ k = 0 := by
  apply toZMod_injective
  rw [map_pow, map_zero, map_ofNat]
  have : ((2 ^ k : ℕ) : ZMod (2 ^ w)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow 2 h)
  exact_mod_cast this

/-- After enough Newton steps the inverse is exact. -/
theorem mul_invNewton {x : Word w} (hx : x.toNat % 2 = 1) {k : ℕ} (hk : w ≤ 2 ^ k) :
    x * invNewton x k = 1 := by
  -- `1 - x` is even, so its `2 ^ k`-th power vanishes
  have hev : (1 : Word w) - x = 2 * -BitVec.ofNat w (x.toNat / 2) := by
    apply toZMod_injective
    simp only [map_sub, map_one, map_mul, map_neg, map_ofNat, toZMod_apply, BitVec.toNat_ofNat,
      ZMod.natCast_mod]
    have h2 : x.toNat = 2 * (x.toNat / 2) + 1 := by omega
    conv_lhs => rw [h2]
    push_cast
    ring
  have h := one_sub_mul_invNewton x k
  rw [hev, mul_pow, two_pow_eq_zero hk, zero_mul] at h
  exact (sub_eq_zero.mp h).symm

/-- The inverse of an odd word modulo `2 ^ w`. -/
def inv (x : Word w) : Word w := invNewton x (Nat.clog 2 w)

theorem mul_inv {x : Word w} (hx : x.toNat % 2 = 1) : x * inv x = 1 :=
  mul_invNewton hx (Nat.le_pow_clog (by norm_num) w)

/-- The negated inverse of an odd word modulo `2 ^ w`, the constant of unsigned Montgomery
reduction. -/
def negInv (x : Word w) : Word w := -inv x

theorem mul_negInv {x : Word w} (hx : x.toNat % 2 = 1) : x * negInv x = -1 := by
  rw [negInv, mul_neg, mul_inv hx]

theorem negInv_spec {x : Word w} (hx : x.toNat % 2 = 1) :
    (x.toNat * (negInv x).toNat + 1) % 2 ^ w = 0 := by
  have h : toZMod (x * negInv x + 1) = 0 := by rw [mul_negInv hx, neg_add_cancel, map_zero]
  rw [map_add, map_mul, map_one, toZMod_apply, toZMod_apply] at h
  exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp (by exact_mod_cast h))

end Bingcd.Word
