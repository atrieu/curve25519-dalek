module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- A limb of a row stays in the range of the carry chain. -/
private theorem limb_range {c a b : ℕ} {F G : ℤ} (hc0 : 2 ^ 96 ≤ c) (hc1 : c < 2 ^ 97)
    (ha : a < 2 ^ 52) (hb : b < 2 ^ 52) (hF : |F| ≤ 2 ^ 43) (hG : |G| ≤ 2 ^ 43) :
    0 ≤ (c : ℤ) + a * F + b * G ∧ (c : ℤ) + a * F + b * G < 2 ^ 98 := by
  have h1 : |(a : ℤ) * F| ≤ 2 ^ 52 * 2 ^ 43 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ a)]
    exact mul_le_mul (by exact_mod_cast ha.le) hF (abs_nonneg _) (by positivity)
  have h2 : |(b : ℤ) * G| ≤ 2 ^ 52 * 2 ^ 43 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ b)]
    exact mul_le_mul (by exact_mod_cast hb.le) hG (abs_nonneg _) (by positivity)
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  obtain ⟨h2l, h2u⟩ := abs_le.mp h2
  have hc0' : (2 : ℤ) ^ 96 ≤ c := by exact_mod_cast hc0
  have hc1' : (c : ℤ) < 2 ^ 97 := by exact_mod_cast hc1
  constructor <;> linarith

/-- A limb of a row of cofactors: `c + a * f + b * g` for signed words `f` and `g` of at most
`2^43` in absolute value, limbs `a` and `b` below `2^52`, and `c` a limb of `2^46 * p`. The
result is exact, and below `2^98`. -/
@[step]
theorem cof_limb_spec (c : U128) (a b f g : U64) (hc0 : 2 ^ 96 ≤ c.val) (hc1 : c.val < 2 ^ 97)
    (ha : a.val < 2 ^ 52) (hb : b.val < 2 ^ 52) (hf : |f.bv.toInt| ≤ 2 ^ 43)
    (hg : |g.bv.toInt| ≤ 2 ^ 43) :
    cof_limb c a b f g ⦃ r =>
      (r.val : ℤ) = c.val + a.val * f.bv.toInt + b.val * g.bv.toInt ∧ r.val < 2 ^ 98 ⦄ := by
  obtain ⟨h0, h1⟩ := limb_range hc0 hc1 ha hb hf hg
  unfold cof_limb
  step*
  have hbv : (core.num.U128.wrapping_add i5 i10).bv =
      c.bv + a.bv.setWidth 128 * f.bv.signExtend 128 +
        b.bv.setWidth 128 * g.bv.signExtend 128 := by
    simp [*]
  have key := Pornin.toNat_add_mul_signExtend (v := 128) (by norm_num) c.bv a.bv b.bv f.bv g.bv
    (by simpa using h0) (by simpa using h1.trans (by norm_num))
  rw [← hbv] at key
  have hval : ((core.num.U128.wrapping_add i5 i10).val : ℤ) =
      c.val + a.val * f.bv.toInt + b.val * g.bv.toInt := by
    simpa [U128.size, U128.numBits] using key
  exact ⟨hval, by omega⟩

end Curve25519Dalek.backend.serial.u64.bingcd
