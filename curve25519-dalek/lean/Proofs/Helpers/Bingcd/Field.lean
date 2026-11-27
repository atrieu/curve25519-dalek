module
public import Proofs.Helpers.Bingcd.Cofactors
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Proofs.Curve25519.Prime

/-! # The field modulo `p` on limbs, and inversion in it

`bingcd::invert` and `bingcd::divide` take a field element on five 51-bit limbs to its
canonical form on four 64-bit limbs, and run Pornin's algorithm on it and the modulus, with the
cofactors kept as field elements. This file has the conversion on vectors of words and the
correctness of the run: from the cofactor `u`, it ends on `u * 2 ^ 508 / z` modulo
`p = 2 ^ 255 - 19`, and the factor `2 ^ 508` is cancelled by the constant `scale`. -/

@[expose] public section

/-! ## Unsaturated limbs

In an unsaturated representation the limbs are words of `w` bits but the radix is
`2 ^ k` with `k < w`: the value of `a` is `Limbs.eval (2 ^ k) a`, and the spare `w - k` bits
of each limb absorb carries.

What makes this sound is a bound on the limbs, tracked by `Limbs.Bounded a β`: every limb of
`a` is at most `β`. Each operation states the bound it needs and the bound it guarantees. -/

namespace Bingcd.Limbs

variable {w n : ℕ}

/-! ### Bounds -/

/-- Every limb of `a` is at most `β`. -/
def Bounded (a : Limbs w n) (β : ℕ) : Prop := ∀ (i : ℕ) (h : i < n), a[i].toNat ≤ β

theorem Bounded.pop {a : Limbs w (n + 1)} {β : ℕ} (h : Bounded a β) : Bounded a.pop β :=
  fun i hi => by simpa using h i (by omega)

theorem Bounded.back {a : Limbs w (n + 1)} {β : ℕ} (h : Bounded a β) : a.back.toNat ≤ β := by
  simpa [Vector.back] using h n (by omega)

theorem bounded_empty (a : Limbs w 0) (β : ℕ) : Bounded a β := fun i hi => by omega

theorem Bounded.push {a : Limbs w n} {β : ℕ} (h : Bounded a β) {x : Word w}
    (hx : x.toNat ≤ β) : Bounded (a.push x) β := by
  intro i hi
  rw [Vector.getElem_push]
  split
  · next hlt => exact h i hlt
  · exact hx

theorem eval_eq_pop_add (r : ℕ) (a : Limbs w (n + 1)) :
    eval r a = eval r a.pop + r ^ n * a.back.toNat := by
  conv_lhs => rw [← Vector.push_pop_back a]
  exact eval_push r _ _

/-! ### Carry propagation -/

/-- One carry-propagation pass in radix `2 ^ k`: each limb keeps its `k` low bits and passes
the rest on. Returns the carried limbs and the carry out of the last limb. -/
def carry (k : ℕ) : {n : ℕ} → Limbs w n → Word w → Limbs w n × Word w
  | 0, _, c => (#v[], c)
  | _ + 1, a, c =>
    let r := carry k a.pop c
    let s := a.back + r.2
    (r.1.push (BitVec.ofNat w (s.toNat % 2 ^ k)), s >>> k)

/-- A carry pass preserves the value, brings every limb below `2 ^ k`, and keeps the carry
within `γ`, provided `β + γ` fits in a word and `(β + γ) / 2 ^ k ≤ γ`. -/
theorem carry_spec (k : ℕ) {a : Limbs w n} {c : Word w} {β γ : ℕ} (ha : Bounded a β)
    (hc : c.toNat ≤ γ) (hw : β + γ < 2 ^ w) (hγ : (β + γ) / 2 ^ k ≤ γ) :
    eval (2 ^ k) (carry k a c).1 + (2 ^ k) ^ n * (carry k a c).2.toNat =
        eval (2 ^ k) a + c.toNat ∧
      Bounded (carry k a c).1 (2 ^ k - 1) ∧ (carry k a c).2.toNat ≤ γ := by
  induction n with
  | zero => simp [carry, Vector.eq_empty (xs := a), hc, bounded_empty]
  | succ n ih =>
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih ha.pop
    have hb := ha.back
    have hk := Nat.two_pow_pos k
    have hs : (a.back + (carry k a.pop c).2).toNat =
        a.back.toNat + (carry k a.pop c).2.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hlow : (BitVec.ofNat w ((a.back + (carry k a.pop c).2).toNat % 2 ^ k)).toNat =
        (a.back.toNat + (carry k a.pop c).2.toNat) % 2 ^ k := by
      rw [BitVec.toNat_ofNat, hs, Nat.mod_eq_of_lt]
      exact (Nat.mod_le _ _).trans_lt (by omega)
    have hhigh : ((a.back + (carry k a.pop c).2) >>> k).toNat =
        (a.back.toNat + (carry k a.pop c).2.toNat) / 2 ^ k := by
      rw [BitVec.toNat_ushiftRight, hs, Nat.shiftRight_eq_div_pow]
    have hdm := Nat.div_add_mod (a.back.toNat + (carry k a.pop c).2.toNat) (2 ^ k)
    simp only [carry]
    rw [eval_push, hlow, hhigh, eval_eq_pop_add _ a]
    simp only [Nat.add_one_sub_one]
    refine ⟨?_, ?_, ?_⟩
    · rw [pow_succ]
      linear_combination ih₁ + (2 ^ k) ^ n * hdm
    · refine ih₂.push ?_
      rw [hlow]
      have := Nat.mod_lt (a.back.toNat + (carry k a.pop c).2.toNat) hk
      omega
    · exact (Nat.div_le_div_right (by omega)).trans hγ

end Bingcd.Limbs

/-! ## Five limbs in radix `2 ^ 51` -/

namespace Bingcd.Limbs.Curve25519

/-- The value of a field element in radix `2 ^ 51`. -/
def value (a : Limbs 64 5) : ℕ := eval (2 ^ 51) a

theorem eval_five {w : ℕ} (r : ℕ) (a : Limbs w 5) :
    eval r a = a[0].toNat + r * a[1].toNat + r ^ 2 * a[2].toNat + r ^ 3 * a[3].toNat +
      r ^ 4 * a[4].toNat := by
  have h : a = #v[a[0], a[1], a[2], a[3], a[4]] := by
    ext i hi
    interval_cases i <;> rfl
  rw [h]
  simp [eval, digits, Nat.ofDigits]
  ring

/-- Limbs at most `2 ^ 51 + 2 ^ 23`: the bound that `freeze` asks for. -/
def Tight (a : Limbs 64 5) : Prop := Bounded a (2 ^ 51 + 2 ^ 23)

end Bingcd.Limbs.Curve25519

/-! ## Canonical form

Conversions between the two representations of a field element: five 51-bit limbs, used by
the arithmetic, and four saturated 64-bit limbs, used for the canonical value and by
Pornin's algorithm. -/

namespace Bingcd.Limbs.Curve25519

open curve25519

theorem eval_four {w : ℕ} (r : ℕ) (a : Limbs w 4) :
    eval r a = a[0].toNat + r * a[1].toNat + r ^ 2 * a[2].toNat + r ^ 3 * a[3].toNat := by
  have h : a = #v[a[0], a[1], a[2], a[3]] := by
    ext i hi
    interval_cases i <;> rfl
  rw [h]
  simp [eval, digits, Nat.ofDigits]
  ring

/-! ### Packing -/

/-- Pack five limbs below `2 ^ 51` and a carry bit, of weight `2 ^ 255`, into four 64-bit
limbs. -/
def pack (r : Limbs 64 5) (c : Word 64) : Limbs 64 4 :=
  #v[r[0] + (r[1] <<< 51), (r[1] >>> 13) + (r[2] <<< 38), (r[2] >>> 26) + (r[3] <<< 25),
    (r[3] >>> 39) + (r[4] <<< 12) + (c <<< 63)]

theorem pack_spec {r : Limbs 64 5} {c : Word 64} (hr : Bounded r (2 ^ 51 - 1))
    (hc : c.toNat ≤ 1) : toNat (pack r c) = eval (2 ^ 51) r + 2 ^ 255 * c.toNat := by
  have r0 := hr 0 (by norm_num)
  have r1 := hr 1 (by norm_num)
  have r2 := hr 2 (by norm_num)
  have r3 := hr 3 (by norm_num)
  have r4 := hr 4 (by norm_num)
  rw [toNat, eval_four, eval_five]
  simp only [pack, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem toNat_and_mask51 (x : Word 64) : (x &&& 0x7FFFFFFFFFFFF#64).toNat = x.toNat % 2 ^ 51 := by
  rw [BitVec.toNat_and, show (0x7FFFFFFFFFFFF#64 : Word 64).toNat = 2 ^ 51 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]

/-! ### The canonical representative -/

/-- The modulus `2 ^ 255 - 19` on four 64-bit limbs. -/
def P : Limbs 64 4 :=
  #v[0xFFFFFFFFFFFFFFED#64, 0xFFFFFFFFFFFFFFFF#64, 0xFFFFFFFFFFFFFFFF#64, 0x7FFFFFFFFFFFFFFF#64]

theorem toNat_P : P.toNat = p := by
  rw [toNat, eval_four, p_eq_numeral]
  decide

/-- The canonical representative of a tight element, on four 64-bit limbs: one carry pass,
packing, and one conditional subtraction of the modulus. -/
def freeze (a : Limbs 64 5) : Limbs 64 4 :=
  let r := carry 51 a 0#64
  condSub (pack r.1 r.2) false P

/-- `freeze` returns the value modulo `p`, hence a number below `p`. -/
theorem freeze_spec {a : Limbs 64 5} (ha : Tight a) : toNat (freeze a) = value a % p := by
  have hp := p_add_nineteen
  obtain ⟨h₁, h₂, h₃⟩ := carry_spec 51 (c := 0#64) (γ := 1) ha (by simp) (by norm_num)
    (by norm_num)
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at h₁
  have hp := pack_spec h₂ h₃
  have hv : toNat (pack (carry 51 a 0#64).1 (carry 51 a 0#64).2) = value a := by
    rw [hp, value, ← h₁]
    norm_num
  -- a tight element has value below `2 * p`
  have hlt : value a < 2 * p := by
    have a0 := ha 0 (by norm_num)
    have a1 := ha 1 (by norm_num)
    have a2 := ha 2 (by norm_num)
    have a3 := ha 3 (by norm_num)
    have a4 := ha 4 (by norm_num)
    rw [value, eval_five]
    omega
  rw [freeze, toNat_condSub _ _ _ (by rw [hv, toNat_P]; simpa using hlt), hv, toNat_P]
  simp

end Bingcd.Limbs.Curve25519

/-! ## Inversion and division

`bingcd.rs` brings a field element on five 51-bit limbs to canonical form on four saturated
64-bit limbs, and runs Pornin's binary gcd on it and the modulus, with 31 inner steps per round
and the cofactors in the field. -/

namespace Bingcd.Limbs.Curve25519

open curve25519

theorem size_toNat_P_le : P.toNat.size ≤ 255 :=
  Nat.size_le.mpr (by rw [toNat_P]; exact p_lt_two_pow_255)

/-- The canonical form of a tight element is below the modulus. -/
theorem toNat_freeze_lt {z : Limbs 64 5} (hz : Tight z) : (freeze z).toNat < P.toNat := by
  rw [freeze_spec hz, toNat_P]
  exact Nat.mod_lt _ p_pos

/-- `2 ^ -508` in the field, as a natural number: the value of the constant `SCALE` of
`bingcd.rs`, which the cofactors of an inversion start from. -/
def scale : ℕ := 0x24e016b1490aa31a3cfc744c965683e6788dd408827b63fd29d6deab9cb8606c

/-- `scale` is `2 ^ -508` in the field. -/
theorem scale_mul_two_pow : (scale : ZMod p) * 2 ^ 508 = 1 := by
  have h1 : scale * 2 ^ 254 % p =
      0x5e50d79435e50d79435e50d79435e50d79435e50d79435e50d79435e50d79428 := by
    rw [p_eq_numeral]
    decide +kernel
  have h2 :
      0x5e50d79435e50d79435e50d79435e50d79435e50d79435e50d79435e50d79428 * 2 ^ 254 % p = 1 := by
    rw [p_eq_numeral]
    decide +kernel
  have e1 := congrArg (Nat.cast : ℕ → ZMod p) h1
  have e2 := congrArg (Nat.cast : ℕ → ZMod p) h2
  have h2' : ((2 : ℕ) : ZMod p) = 2 := Nat.cast_ofNat
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, h2'] at e1 e2
  rw [Nat.cast_one] at e2
  rw [show (2 : ZMod p) ^ 508 = 2 ^ 254 * 2 ^ 254 from pow_add 2 254 254, ← mul_assoc, e1, e2]

/-- **The run of `bingcd.rs` on a field element.** For a tight `z`, 15 rounds of 31 steps and
43 last steps on the canonical form of `z` and the modulus, from the cofactor `u`, end on
`u * 2 ^ 508 / z` in the field, which is `0` when `z` is `0`. -/
theorem porninDivR_freeze {z : Limbs 64 5} (hz : Tight z) (u : ZMod p) :
    Pornin.porninDivR 31 15 43 P u (freeze z) = u * 2 ^ 508 / (value z : ZMod p) := by
  have hsize : p.size ≤ 255 := by
    rw [← toNat_P]
    exact size_toNat_P_le
  have h := Pornin.porninDivR_spec (K := 31) (r := 15) (T := 43) (by norm_num) (by norm_num)
    (by norm_num) p_mod_two P toNat_P (freeze z) (by rw [← toNat_P]; exact toNat_freeze_lt hz)
    (by omega) (by omega) u
  rw [h, freeze_spec hz, ZMod.natCast_mod]

end Bingcd.Limbs.Curve25519
