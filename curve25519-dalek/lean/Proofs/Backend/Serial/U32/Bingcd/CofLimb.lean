module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- A limb of a row stays in the range that `reduce` accepts. -/
private theorem limb_range {c a b : ℕ} {F G : ℤ} (hc0 : 2 ^ 55 ≤ c) (hc1 : c < 2 ^ 57)
    (ha : a < 2 ^ 26) (hb : b < 2 ^ 26) (hF : |F| ≤ 2 ^ 28) (hG : |G| ≤ 2 ^ 28) :
    0 ≤ (c : ℤ) + a * F + b * G ∧ (c : ℤ) + a * F + b * G < 2 ^ 58 := by
  have h1 : |(a : ℤ) * F| ≤ 2 ^ 26 * 2 ^ 28 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ a)]
    exact mul_le_mul (by exact_mod_cast ha.le) hF (abs_nonneg _) (by positivity)
  have h2 : |(b : ℤ) * G| ≤ 2 ^ 26 * 2 ^ 28 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ b)]
    exact mul_le_mul (by exact_mod_cast hb.le) hG (abs_nonneg _) (by positivity)
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  obtain ⟨h2l, h2u⟩ := abs_le.mp h2
  have hc0' : (2 : ℤ) ^ 55 ≤ c := by exact_mod_cast hc0
  have hc1' : (c : ℤ) < 2 ^ 57 := by exact_mod_cast hc1
  constructor <;> linarith

/-- A limb of a row of cofactors: `c + a * f + b * g` for signed words `f` and `g` of at most
`2^28` in absolute value, limbs `a` and `b` below `2^26`, and `c` a limb of `2^31 * p`. The
result is exact, and below `2^58`. -/
@[step]
theorem cof_limb_spec (c : U64) (a b f g : U32) (hc0 : 2 ^ 55 ≤ c.val) (hc1 : c.val < 2 ^ 57)
    (ha : a.val < 2 ^ 26) (hb : b.val < 2 ^ 26) (hf : |f.bv.toInt| ≤ 2 ^ 28)
    (hg : |g.bv.toInt| ≤ 2 ^ 28) :
    cof_limb c a b f g ⦃ r =>
      (r.val : ℤ) = c.val + a.val * f.bv.toInt + b.val * g.bv.toInt ∧ r.val < 2 ^ 58 ⦄ := by
  obtain ⟨h0, h1⟩ := limb_range hc0 hc1 ha hb hf hg
  unfold cof_limb
  step*
  have hbv : (core.num.U64.wrapping_add i5 i10).bv =
      c.bv + a.bv.setWidth 64 * f.bv.signExtend 64 + b.bv.setWidth 64 * g.bv.signExtend 64 := by
    simp [*]
  have key := Pornin.toNat_add_mul_signExtend (v := 64) (by norm_num) c.bv a.bv b.bv f.bv g.bv
    (by simpa using h0) (by simpa using h1.trans (by norm_num))
  rw [← hbv] at key
  have hval : ((core.num.U64.wrapping_add i5 i10).val : ℤ) =
      c.val + a.val * f.bv.toInt + b.val * g.bv.toInt := by
    simpa [U64.size, U64.numBits] using key
  exact ⟨hval, by omega⟩

end Curve25519Dalek.backend.serial.u32.bingcd
