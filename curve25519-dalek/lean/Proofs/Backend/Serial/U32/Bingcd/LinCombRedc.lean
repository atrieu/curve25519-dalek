module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.LinComb
import Proofs.Backend.Serial.U32.Bingcd.MulAddRow
import Proofs.Backend.Serial.U32.Bingcd.RedcTail
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- The Montgomery reduction of a linear combination, by `2 ^ S` for any `0 < S < 32`. -/
@[step]
theorem lin_comb_redc_spec (S : U32) (u v : Array U32 8#usize) (f g : U32)
    (m : Array U32 8#usize) (ninv : U32) (hS0 : 0 < S.val) (hS : S.val < 32) :
    lin_comb_redc S u v f g m ninv ⦃ x =>
      L8 x = Limbs.linCombRedc (L8 u) (L8 v) f.bv g.bv (L8 m) ninv.bv S.val ⦄ := by
  unfold lin_comb_redc
  have hpow : 2 ^ S.val < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) hS
  have hsh : 1 <<< S.val % U32.size = 2 ^ S.val := by
    rw [Nat.one_shiftLeft, Nat.mod_eq_of_lt]
    simpa [U32.size, U32.numBits] using hpow
  step*
  · -- the mask `2 ^ S - 1`: the subtraction needs `1 ≤ 2 ^ S`
    have h1 : 1 ≤ 2 ^ S.val := Nat.one_le_two_pow
    rw [i2_post, hsh]
    exact h1
  · have h2 : i2.val = 2 ^ S.val := by rw [i2_post, hsh]
    have h3 : i3.bv = BitVec.ofNat 32 (2 ^ S.val - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [U32.bv_toNat, i3_post, h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hq : q.bv = ((L8 r)[0] * ninv.bv) &&& BitVec.ofNat 32 (2 ^ S.val - 1) := by
      simp only [q_post1, h3, i1_post, core.num.U32.wrapping_mul_bv_eq, i_post, L8_getElem_zero,
        U32.bv]
    have h4 : i4.bv = hi.bv + c.bv := by
      simp only [i4_post, core.num.U32.wrapping_add_bv_eq, U32.bv]
    have h0 : UScalar.bv 0#u32 = 0#32 := rfl
    simp only [x_post, h4, s_post, s_post1, hq, r_post1, r_post, Limbs.linCombRedc, U32.bv, h0]

end Curve25519Dalek.backend.serial.u32.bingcd
