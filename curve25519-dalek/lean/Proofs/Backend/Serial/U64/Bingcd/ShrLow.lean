module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Helpers.AsNat
import Proofs.Helpers.Bitwise
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

private theorem toNat_five (x0 x1 x2 x3 x4 : Word 64) :
    Limbs.toNat (#v[x0, x1, x2, x3, x4] : Limbs 64 5) =
      x0.toNat + 2 ^ 64 * x1.toNat + 2 ^ 128 * x2.toNat + 2 ^ 192 * x3.toNat +
        2 ^ 256 * x4.toNat := by
  rw [Limbs.toNat, Limbs.Curve25519.eval_five]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  norm_num

/-- `Limbs.shr` is a division by `2 ^ k`. On five 64-bit limbs and for `0 < k < 64`, each limb
of the quotient is a combination of two shifts, as in the code: the two forms have the same
value. -/
private theorem shr_five (r0 r1 r2 r3 c : Word 64) {k : ℕ} (hk : k < 64) :
    (Limbs.shr #v[r0, r1, r2, r3, c] k).1 =
      #v[(r0 >>> k) ||| (r1 <<< (64 - k)), (r1 >>> k) ||| (r2 <<< (64 - k)),
        (r2 >>> k) ||| (r3 <<< (64 - k)), (r3 >>> k) ||| (c <<< (64 - k)), c >>> k] := by
  apply Limbs.toNat_injective
  have hW : (2 : ℕ) ^ 64 = 2 ^ k * 2 ^ (64 - k) := by rw [← pow_add]; congr 1; omega
  have e2 : (2 : ℕ) ^ 128 = (2 ^ 64) ^ 2 := by norm_num
  have e3 : (2 : ℕ) ^ 192 = (2 ^ 64) ^ 3 := by norm_num
  have e4 : (2 : ℕ) ^ 256 = (2 ^ 64) ^ 4 := by norm_num
  rw [Limbs.toNat_shr_fst _ hk, toNat_five, toNat_five]
  simp only [BitVec.toNat_ushiftRight_or_shiftLeft _ _ hk, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [e2, e3, e4]
  exact Nat.div_five_digits (Nat.two_pow_pos k) hW _ _ _ _ _

/-- The low four limbs of a five-limb value shifted right by `k` bits. -/
private theorem shr_push_pop (r0 r1 r2 r3 c : Word 64) {k : ℕ} (hk : k < 64) :
    (Limbs.shr ((#v[r0, r1, r2, r3] : Limbs 64 4).push c) k).1.pop =
      #v[(r0 >>> k) ||| (r1 <<< (64 - k)), (r1 >>> k) ||| (r2 <<< (64 - k)),
        (r2 >>> k) ||| (r3 <<< (64 - k)), (r3 >>> k) ||| (c <<< (64 - k))] := by
  have h : (#v[r0, r1, r2, r3] : Limbs 64 4).push c = #v[r0, r1, r2, r3, c] := rfl
  rw [h, shr_five _ _ _ _ _ hk]
  rfl

/-- The shift of a five-limb value, for any amount `0 < S < 64`. -/
@[step]
theorem shr_low_spec (S : U32) (r : Array U64 4#usize) (c : U64) (hS0 : 0 < S.val)
    (hS : S.val < 64) :
    shr_low S r c ⦃ x => L4 x = (Limbs.shr ((L4 r).push c.bv) S.val).1.pop ⦄ := by
  unfold shr_low
  step*
  have h3 : i3.val = 64 - S.val := by scalar_tac
  simp only [L4_make]
  rw [L4, shr_push_pop _ _ _ _ _ hS]
  simp [*]

end Curve25519Dalek.backend.serial.u64.bingcd
