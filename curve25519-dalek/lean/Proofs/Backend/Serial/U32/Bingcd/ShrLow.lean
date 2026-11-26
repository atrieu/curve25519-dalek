module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Helpers.AsNat
import Proofs.Helpers.Bitwise
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

private theorem toNat_nine (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Word 32) :
    Limbs.toNat (#v[x0, x1, x2, x3, x4, x5, x6, x7, x8] : Limbs 32 9) =
      x0.toNat + 2 ^ 32 * x1.toNat + 2 ^ 64 * x2.toNat + 2 ^ 96 * x3.toNat + 2 ^ 128 * x4.toNat +
        2 ^ 160 * x5.toNat + 2 ^ 192 * x6.toNat + 2 ^ 224 * x7.toNat + 2 ^ 256 * x8.toNat := by
  rw [Limbs.toNat, Limbs.Curve25519.eval_nine]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  norm_num

/-- `Limbs.shr` is a division by `2 ^ k`. On nine 32-bit limbs and for `k < 32`, each limb of
the quotient is a combination of two shifts, as in the code: the two forms have the same
value. -/
private theorem shr_nine (r0 r1 r2 r3 r4 r5 r6 r7 c : Word 32) {k : ℕ} (hk : k < 32) :
    (Limbs.shr #v[r0, r1, r2, r3, r4, r5, r6, r7, c] k).1 =
      #v[(r0 >>> k) ||| (r1 <<< (32 - k)), (r1 >>> k) ||| (r2 <<< (32 - k)),
        (r2 >>> k) ||| (r3 <<< (32 - k)), (r3 >>> k) ||| (r4 <<< (32 - k)),
        (r4 >>> k) ||| (r5 <<< (32 - k)), (r5 >>> k) ||| (r6 <<< (32 - k)),
        (r6 >>> k) ||| (r7 <<< (32 - k)), (r7 >>> k) ||| (c <<< (32 - k)), c >>> k] := by
  apply Limbs.toNat_injective
  have hW : (2 : ℕ) ^ 32 = 2 ^ k * 2 ^ (32 - k) := by rw [← pow_add]; congr 1; omega
  have e2 : (2 : ℕ) ^ 64 = (2 ^ 32) ^ 2 := by norm_num
  have e3 : (2 : ℕ) ^ 96 = (2 ^ 32) ^ 3 := by norm_num
  have e4 : (2 : ℕ) ^ 128 = (2 ^ 32) ^ 4 := by norm_num
  have e5 : (2 : ℕ) ^ 160 = (2 ^ 32) ^ 5 := by norm_num
  have e6 : (2 : ℕ) ^ 192 = (2 ^ 32) ^ 6 := by norm_num
  have e7 : (2 : ℕ) ^ 224 = (2 ^ 32) ^ 7 := by norm_num
  have e8 : (2 : ℕ) ^ 256 = (2 ^ 32) ^ 8 := by norm_num
  rw [Limbs.toNat_shr_fst _ hk, toNat_nine, toNat_nine]
  simp only [BitVec.toNat_ushiftRight_or_shiftLeft _ _ hk, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [e2, e3, e4, e5, e6, e7, e8]
  exact Nat.div_nine_digits (Nat.two_pow_pos k) hW _ _ _ _ _ _ _ _ _

/-- The low eight limbs of a nine-limb value shifted right by `k` bits. -/
private theorem shr_push_pop (r0 r1 r2 r3 r4 r5 r6 r7 c : Word 32) {k : ℕ} (hk : k < 32) :
    (Limbs.shr ((#v[r0, r1, r2, r3, r4, r5, r6, r7] : Limbs 32 8).push c) k).1.pop =
      #v[(r0 >>> k) ||| (r1 <<< (32 - k)), (r1 >>> k) ||| (r2 <<< (32 - k)),
        (r2 >>> k) ||| (r3 <<< (32 - k)), (r3 >>> k) ||| (r4 <<< (32 - k)),
        (r4 >>> k) ||| (r5 <<< (32 - k)), (r5 >>> k) ||| (r6 <<< (32 - k)),
        (r6 >>> k) ||| (r7 <<< (32 - k)), (r7 >>> k) ||| (c <<< (32 - k))] := by
  have h : (#v[r0, r1, r2, r3, r4, r5, r6, r7] : Limbs 32 8).push c =
      #v[r0, r1, r2, r3, r4, r5, r6, r7, c] := rfl
  rw [h, shr_nine _ _ _ _ _ _ _ _ _ hk]
  rfl

/-- The top limb of a nine-limb value shifted right by `k` bits. -/
theorem shr_push_back (r0 r1 r2 r3 r4 r5 r6 r7 c : Word 32) {k : ℕ} (hk : k < 32) :
    (Limbs.shr ((#v[r0, r1, r2, r3, r4, r5, r6, r7] : Limbs 32 8).push c) k).1.back = c >>> k := by
  have h : (#v[r0, r1, r2, r3, r4, r5, r6, r7] : Limbs 32 8).push c =
      #v[r0, r1, r2, r3, r4, r5, r6, r7, c] := rfl
  rw [h, shr_nine _ _ _ _ _ _ _ _ _ hk]
  rfl

/-- The shift of a nine-limb value, for any amount `0 < S < 32`. -/
@[step]
theorem shr_low_spec (S : U32) (r : Array U32 8#usize) (c : U32) (hS0 : 0 < S.val)
    (hS : S.val < 32) :
    shr_low S r c ⦃ x => L8 x = (Limbs.shr ((L8 r).push c.bv) S.val).1.pop ⦄ := by
  unfold shr_low
  step*
  have h3 : i3.val = 32 - S.val := by scalar_tac
  simp only [L8_make]
  rw [L8, shr_push_pop _ _ _ _ _ _ _ _ _ hS]
  simp [*]

end Curve25519Dalek.backend.serial.u32.bingcd
