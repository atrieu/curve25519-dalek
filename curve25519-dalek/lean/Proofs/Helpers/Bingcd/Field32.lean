module
public import Proofs.Helpers.Bingcd.Field

/-! # The field modulo `p` on 32-bit limbs, and inversion in it

`backend::serial::u32::bingcd` takes a field element on ten limbs of 26 and 25 bits to its
canonical form on eight 32-bit limbs, and runs Pornin's algorithm on it and the modulus, with 15
inner steps per round and the cofactors kept as field elements. This file has the conversion on
vectors of words and the correctness of the run: from the cofactor `u`, it ends on
`u * 2 ^ 508 / z` modulo `p = 2 ^ 255 - 19`. It is `Proofs/Helpers/Bingcd/Field.lean` for 32-bit
words. -/

@[expose] public section

namespace Bingcd.Limbs.Curve25519

theorem eval_eight {w : ℕ} (r : ℕ) (a : Limbs w 8) :
    eval r a = a[0].toNat + r * a[1].toNat + r ^ 2 * a[2].toNat + r ^ 3 * a[3].toNat +
      r ^ 4 * a[4].toNat + r ^ 5 * a[5].toNat + r ^ 6 * a[6].toNat + r ^ 7 * a[7].toNat := by
  have h : a = #v[a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]] := by
    ext i hi
    interval_cases i <;> rfl
  rw [h]
  simp [eval, digits, Nat.ofDigits]
  ring

theorem eval_nine {w : ℕ} (r : ℕ) (a : Limbs w 9) :
    eval r a = a[0].toNat + r * a[1].toNat + r ^ 2 * a[2].toNat + r ^ 3 * a[3].toNat +
      r ^ 4 * a[4].toNat + r ^ 5 * a[5].toNat + r ^ 6 * a[6].toNat + r ^ 7 * a[7].toNat +
      r ^ 8 * a[8].toNat := by
  have h : a = #v[a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8]] := by
    ext i hi
    interval_cases i <;> rfl
  rw [h]
  simp [eval, digits, Nat.ofDigits]
  ring

end Bingcd.Limbs.Curve25519

/-! ## Ten limbs of 26 and 25 bits -/

namespace Bingcd.Limbs.Curve25519.U32

open curve25519

/-- The value of a field element on ten limbs: limb `i` has weight `2 ^ ⌈51 * i / 2⌉`. -/
def value (a : Limbs 32 10) : ℕ :=
  a[0].toNat + 2 ^ 26 * a[1].toNat + 2 ^ 51 * a[2].toNat + 2 ^ 77 * a[3].toNat +
    2 ^ 102 * a[4].toNat + 2 ^ 128 * a[5].toNat + 2 ^ 153 * a[6].toNat + 2 ^ 179 * a[7].toNat +
    2 ^ 204 * a[8].toNat + 2 ^ 230 * a[9].toNat

/-- Limbs below `2 ^ 26` at even positions and below `2 ^ 25 + 2 ^ 18` at odd ones: the bound
that `freeze` asks for. -/
def Tight (a : Limbs 32 10) : Prop :=
  ∀ (i : ℕ) (h : i < 10), a[i].toNat < 2 ^ (26 - i % 2) + i % 2 * 2 ^ 18

/-- Limbs below `2 ^ 26` at even positions and below `2 ^ 25` at odd ones. -/
def Reduced (a : Limbs 32 10) : Prop := ∀ (i : ℕ) (h : i < 10), a[i].toNat < 2 ^ (26 - i % 2)

theorem reduced_ten {x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : Word 32} (h₀ : x₀.toNat < 2 ^ 26)
    (h₁ : x₁.toNat < 2 ^ 25) (h₂ : x₂.toNat < 2 ^ 26) (h₃ : x₃.toNat < 2 ^ 25)
    (h₄ : x₄.toNat < 2 ^ 26) (h₅ : x₅.toNat < 2 ^ 25) (h₆ : x₆.toNat < 2 ^ 26)
    (h₇ : x₇.toNat < 2 ^ 25) (h₈ : x₈.toNat < 2 ^ 26) (h₉ : x₉.toNat < 2 ^ 25) :
    Reduced (#v[x₀, x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈, x₉] : Limbs 32 10) := by
  intro i hi
  interval_cases i <;> assumption

theorem toNat_and_mask26 (x : Word 32) : (x &&& 0x3FFFFFF#32).toNat = x.toNat % 2 ^ 26 := by
  rw [BitVec.toNat_and, show (0x3FFFFFF#32 : Word 32).toNat = 2 ^ 26 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_and_mask25 (x : Word 32) : (x &&& 0x1FFFFFF#32).toNat = x.toNat % 2 ^ 25 := by
  rw [BitVec.toNat_and, show (0x1FFFFFF#32 : Word 32).toNat = 2 ^ 25 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]

/-! ### The carry pass -/

/-- One carry pass over ten limbs: each limb keeps its 26 or 25 low bits and passes the rest
on. Returns the carried limbs and the carry out of the last limb, of weight `2 ^ 255`. -/
def carry (a : Limbs 32 10) : Limbs 32 10 × Word 32 :=
  let s0 := a[0]
  let s1 := a[1] + s0 >>> 26
  let s2 := a[2] + s1 >>> 25
  let s3 := a[3] + s2 >>> 26
  let s4 := a[4] + s3 >>> 25
  let s5 := a[5] + s4 >>> 26
  let s6 := a[6] + s5 >>> 25
  let s7 := a[7] + s6 >>> 26
  let s8 := a[8] + s7 >>> 25
  let s9 := a[9] + s8 >>> 26
  (#v[s0 &&& 0x3FFFFFF#32, s1 &&& 0x1FFFFFF#32, s2 &&& 0x3FFFFFF#32, s3 &&& 0x1FFFFFF#32,
      s4 &&& 0x3FFFFFF#32, s5 &&& 0x1FFFFFF#32, s6 &&& 0x3FFFFFF#32, s7 &&& 0x1FFFFFF#32,
      s8 &&& 0x3FFFFFF#32, s9 &&& 0x1FFFFFF#32],
    s9 >>> 25)

/-- The carry pass on ten words: `s1`, …, `s9` are the limbs with the carry of the limb below
added. The sums do not wrap, the masked limbs with the last carry have the value of the limbs,
and the last carry is at most `1`. -/
private theorem carry_aux {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 s1 s2 s3 s4 s5 s6 s7 s8 s9 : Word 32}
    (b0 : a0.toNat < 2 ^ 26) (b1 : a1.toNat < 2 ^ 25 + 2 ^ 18) (b2 : a2.toNat < 2 ^ 26)
    (b3 : a3.toNat < 2 ^ 25 + 2 ^ 18) (b4 : a4.toNat < 2 ^ 26) (b5 : a5.toNat < 2 ^ 25 + 2 ^ 18)
    (b6 : a6.toNat < 2 ^ 26) (b7 : a7.toNat < 2 ^ 25 + 2 ^ 18) (b8 : a8.toNat < 2 ^ 26)
    (b9 : a9.toNat < 2 ^ 25 + 2 ^ 18)
    (h1 : s1 = a1 + a0 >>> 26) (h2 : s2 = a2 + s1 >>> 25) (h3 : s3 = a3 + s2 >>> 26)
    (h4 : s4 = a4 + s3 >>> 25) (h5 : s5 = a5 + s4 >>> 26) (h6 : s6 = a6 + s5 >>> 25)
    (h7 : s7 = a7 + s6 >>> 26) (h8 : s8 = a8 + s7 >>> 25) (h9 : s9 = a9 + s8 >>> 26) :
    (a0 &&& 0x3FFFFFF#32).toNat + 2 ^ 26 * (s1 &&& 0x1FFFFFF#32).toNat +
        2 ^ 51 * (s2 &&& 0x3FFFFFF#32).toNat + 2 ^ 77 * (s3 &&& 0x1FFFFFF#32).toNat +
        2 ^ 102 * (s4 &&& 0x3FFFFFF#32).toNat + 2 ^ 128 * (s5 &&& 0x1FFFFFF#32).toNat +
        2 ^ 153 * (s6 &&& 0x3FFFFFF#32).toNat + 2 ^ 179 * (s7 &&& 0x1FFFFFF#32).toNat +
        2 ^ 204 * (s8 &&& 0x3FFFFFF#32).toNat + 2 ^ 230 * (s9 &&& 0x1FFFFFF#32).toNat +
        2 ^ 255 * (s9 >>> 25).toNat =
      a0.toNat + 2 ^ 26 * a1.toNat + 2 ^ 51 * a2.toNat + 2 ^ 77 * a3.toNat + 2 ^ 102 * a4.toNat +
        2 ^ 128 * a5.toNat + 2 ^ 153 * a6.toNat + 2 ^ 179 * a7.toNat + 2 ^ 204 * a8.toNat +
        2 ^ 230 * a9.toNat ∧
      (s9 >>> 25).toNat ≤ 1 := by
  have e1 : s1.toNat = a1.toNat + a0.toNat / 2 ^ 26 := by
    rw [h1, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have e2 : s2.toNat = a2.toNat + s1.toNat / 2 ^ 25 := by
    rw [h2, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have e3 : s3.toNat = a3.toNat + s2.toNat / 2 ^ 26 := by
    rw [h3, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have e4 : s4.toNat = a4.toNat + s3.toNat / 2 ^ 25 := by
    rw [h4, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have e5 : s5.toNat = a5.toNat + s4.toNat / 2 ^ 26 := by
    rw [h5, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have e6 : s6.toNat = a6.toNat + s5.toNat / 2 ^ 25 := by
    rw [h6, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have e7 : s7.toNat = a7.toNat + s6.toNat / 2 ^ 26 := by
    rw [h7, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have e8 : s8.toNat = a8.toNat + s7.toNat / 2 ^ 25 := by
    rw [h8, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have e9 : s9.toNat = a9.toNat + s8.toNat / 2 ^ 26 := by
    rw [h9, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  simp only [toNat_and_mask26, toNat_and_mask25, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  omega

/-- A carry pass on tight limbs preserves the value, reduces every limb, and leaves a carry of
at most `1`. -/
theorem carry_spec {a : Limbs 32 10} (ha : Tight a) :
    value (carry a).1 + 2 ^ 255 * (carry a).2.toNat = value a ∧ Reduced (carry a).1 ∧
      (carry a).2.toNat ≤ 1 := by
  obtain ⟨hv, hc⟩ := carry_aux (a0 := a[0]) (a1 := a[1]) (a2 := a[2]) (a3 := a[3]) (a4 := a[4])
    (a5 := a[5]) (a6 := a[6]) (a7 := a[7]) (a8 := a[8]) (a9 := a[9]) (ha 0 (by norm_num))
    (by simpa using ha 1 (by norm_num)) (ha 2 (by norm_num)) (by simpa using ha 3 (by norm_num))
    (ha 4 (by norm_num)) (by simpa using ha 5 (by norm_num)) (ha 6 (by norm_num))
    (by simpa using ha 7 (by norm_num)) (ha 8 (by norm_num)) (by simpa using ha 9 (by norm_num))
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨?_, ?_, ?_⟩
  · simpa only [carry, value, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] using hv
  · simp only [carry]
    refine reduced_ten ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (first | rw [toNat_and_mask26] | rw [toNat_and_mask25]) <;> omega
  · simpa only [carry] using hc

/-! ### Packing

Conversions between the two representations of a field element: ten limbs of 26 and 25 bits,
used by the arithmetic, and eight saturated 32-bit limbs, used for the canonical value and by
Pornin's algorithm. Limb `5` starts at bit `128`, so each half of the limbs fills four words. -/

/-- Pack ten reduced limbs and a carry bit, of weight `2 ^ 255`, into eight 32-bit limbs. -/
def pack (r : Limbs 32 10) (c : Word 32) : Limbs 32 8 :=
  #v[r[0] + (r[1] <<< 26), (r[1] >>> 6) + (r[2] <<< 19), (r[2] >>> 13) + (r[3] <<< 13),
    (r[3] >>> 19) + (r[4] <<< 6), r[5] + (r[6] <<< 25), (r[6] >>> 7) + (r[7] <<< 19),
    (r[7] >>> 13) + (r[8] <<< 12), (r[8] >>> 20) + (r[9] <<< 6) + (c <<< 31)]

theorem pack_spec {r : Limbs 32 10} {c : Word 32} (hr : Reduced r) (hc : c.toNat ≤ 1) :
    toNat (pack r c) = value r + 2 ^ 255 * c.toNat := by
  have r0 : r[0].toNat < 2 ^ 26 := hr 0 (by norm_num)
  have r1 : r[1].toNat < 2 ^ 25 := hr 1 (by norm_num)
  have r2 : r[2].toNat < 2 ^ 26 := hr 2 (by norm_num)
  have r3 : r[3].toNat < 2 ^ 25 := hr 3 (by norm_num)
  have r4 : r[4].toNat < 2 ^ 26 := hr 4 (by norm_num)
  have r5 : r[5].toNat < 2 ^ 25 := hr 5 (by norm_num)
  have r6 : r[6].toNat < 2 ^ 26 := hr 6 (by norm_num)
  have r7 : r[7].toNat < 2 ^ 25 := hr 7 (by norm_num)
  have r8 : r[8].toNat < 2 ^ 26 := hr 8 (by norm_num)
  have r9 : r[9].toNat < 2 ^ 25 := hr 9 (by norm_num)
  rw [toNat, eval_eight]
  simp only [pack, value, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-! ### The canonical representative -/

/-- The modulus `2 ^ 255 - 19` on eight 32-bit limbs. -/
def P : Limbs 32 8 :=
  #v[0xFFFFFFED#32, 0xFFFFFFFF#32, 0xFFFFFFFF#32, 0xFFFFFFFF#32, 0xFFFFFFFF#32, 0xFFFFFFFF#32,
    0xFFFFFFFF#32, 0x7FFFFFFF#32]

theorem toNat_P : P.toNat = p := by
  rw [toNat, eval_eight, p_eq_numeral]
  decide

/-- The canonical representative of a tight element, on eight 32-bit limbs: one carry pass,
packing, and one conditional subtraction of the modulus. -/
def freeze (a : Limbs 32 10) : Limbs 32 8 :=
  let r := carry a
  condSub (pack r.1 r.2) false P

/-- `freeze` returns the value modulo `p`, hence a number below `p`. -/
theorem freeze_spec {a : Limbs 32 10} (ha : Tight a) : toNat (freeze a) = value a % p := by
  have hp := p_add_nineteen
  obtain ⟨h₁, h₂, h₃⟩ := carry_spec ha
  have hv : toNat (pack (carry a).1 (carry a).2) = value a := by rw [pack_spec h₂ h₃, h₁]
  -- a tight element has value below `2 * p`
  have hlt : value a < 2 * p := by
    have a0 : a[0].toNat < 2 ^ 26 := ha 0 (by norm_num)
    have a1 : a[1].toNat < 2 ^ 25 + 2 ^ 18 := by simpa using ha 1 (by norm_num)
    have a2 : a[2].toNat < 2 ^ 26 := ha 2 (by norm_num)
    have a3 : a[3].toNat < 2 ^ 25 + 2 ^ 18 := by simpa using ha 3 (by norm_num)
    have a4 : a[4].toNat < 2 ^ 26 := ha 4 (by norm_num)
    have a5 : a[5].toNat < 2 ^ 25 + 2 ^ 18 := by simpa using ha 5 (by norm_num)
    have a6 : a[6].toNat < 2 ^ 26 := ha 6 (by norm_num)
    have a7 : a[7].toNat < 2 ^ 25 + 2 ^ 18 := by simpa using ha 7 (by norm_num)
    have a8 : a[8].toNat < 2 ^ 26 := ha 8 (by norm_num)
    have a9 : a[9].toNat < 2 ^ 25 + 2 ^ 18 := by simpa using ha 9 (by norm_num)
    rw [value]
    omega
  rw [freeze, toNat_condSub _ _ _ (by rw [hv, toNat_P]; simpa using hlt), hv, toNat_P]
  simp

end Bingcd.Limbs.Curve25519.U32

/-! ## Inversion and division

`backend/serial/u32/bingcd.rs` brings a field element on ten limbs to canonical form on eight
saturated 32-bit limbs, and runs Pornin's binary gcd on it and the modulus, with 15 inner steps
per round and the cofactors in the field. -/

namespace Bingcd.Limbs.Curve25519.U32

open curve25519

theorem size_toNat_P_le : P.toNat.size ≤ 255 :=
  Nat.size_le.mpr (by rw [toNat_P]; exact p_lt_two_pow_255)

/-- The canonical form of a tight element is below the modulus. -/
theorem toNat_freeze_lt {z : Limbs 32 10} (hz : Tight z) : (freeze z).toNat < P.toNat := by
  rw [freeze_spec hz, toNat_P]
  exact Nat.mod_lt _ p_pos

/-- **The run of `backend/serial/u32/bingcd.rs` on a field element.** For a tight `z`, 32 rounds
of 15 steps and 28 last steps on the canonical form of `z` and the modulus, from the cofactor
`u`, end on `u * 2 ^ 508 / z` in the field, which is `0` when `z` is `0`. -/
theorem porninDivR_freeze {z : Limbs 32 10} (hz : Tight z) (u : ZMod p) :
    Pornin.porninDivR 15 32 28 P u (freeze z) = u * 2 ^ 508 / (value z : ZMod p) := by
  have hsize : p.size ≤ 255 := by
    rw [← toNat_P]
    exact size_toNat_P_le
  have h := Pornin.porninDivR_spec (K := 15) (r := 32) (T := 28) (by norm_num) (by norm_num)
    (by norm_num) p_mod_two P toNat_P (freeze z) (by rw [← toNat_P]; exact toNat_freeze_lt hz)
    (by omega) (by omega) u
  rw [h, freeze_spec hz, ZMod.natCast_mod]

end Bingcd.Limbs.Curve25519.U32
