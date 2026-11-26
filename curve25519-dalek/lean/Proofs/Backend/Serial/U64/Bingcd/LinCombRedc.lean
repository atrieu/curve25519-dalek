module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.LinComb
import Proofs.Backend.Serial.U64.Bingcd.MulAddRow
import Proofs.Backend.Serial.U64.Bingcd.RedcTail
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- The Montgomery reduction of a linear combination, by `2 ^ S` for any `0 < S < 64`. -/
@[step]
theorem lin_comb_redc_spec (S : U32) (u v : Array U64 4#usize) (f g : U64)
    (m : Array U64 4#usize) (ninv : U64) (hS0 : 0 < S.val) (hS : S.val < 64) :
    lin_comb_redc S u v f g m ninv ⦃ x =>
      L4 x = Limbs.linCombRedc (L4 u) (L4 v) f.bv g.bv (L4 m) ninv.bv S.val ⦄ := by
  unfold lin_comb_redc
  have hpow : 2 ^ S.val < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hS
  have hsh : 1 <<< S.val % U64.size = 2 ^ S.val := by
    rw [Nat.one_shiftLeft, Nat.mod_eq_of_lt]
    simpa [U64.size, U64.numBits] using hpow
  step*
  · -- the mask `2 ^ S - 1`: the subtraction needs `1 ≤ 2 ^ S`
    have h1 : 1 ≤ 2 ^ S.val := Nat.one_le_two_pow
    rw [i2_post, hsh]
    exact h1
  · have h2 : i2.val = 2 ^ S.val := by rw [i2_post, hsh]
    have h3 : i3.bv = BitVec.ofNat 64 (2 ^ S.val - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [U64.bv_toNat, i3_post, h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hq : q.bv = ((L4 r)[0] * ninv.bv) &&& BitVec.ofNat 64 (2 ^ S.val - 1) := by
      simp only [q_post1, h3, i1_post, core.num.U64.wrapping_mul_bv_eq, i_post, L4_getElem_zero,
        U64.bv]
    have h4 : i4.bv = hi.bv + c.bv := by
      simp only [i4_post, core.num.U64.wrapping_add_bv_eq, U64.bv]
    have h0 : UScalar.bv 0#u64 = 0#64 := rfl
    simp only [x_post, h4, s_post, s_post1, hq, r_post1, r_post, Limbs.linCombRedc, U64.bv, h0]

end Curve25519Dalek.backend.serial.u64.bingcd
