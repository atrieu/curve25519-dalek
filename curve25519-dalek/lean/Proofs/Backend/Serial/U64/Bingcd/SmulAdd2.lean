module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Helpers.Bitwise
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- The signed multiply-add `Word.smulAdd2`, as a computation on 128-bit vectors with wrapping
operations: sign extensions of `f`, `g`, `c`, and zero extensions of `a`, `b`. -/
private theorem smulAdd2_eq (a b f g c : Word 64) :
    Word.smulAdd2 a b f g c =
      ((a.setWidth 128 * f.signExtend 128 + b.setWidth 128 * g.signExtend 128 +
          c.signExtend 128).setWidth 64,
        ((a.setWidth 128 * f.signExtend 128 + b.setWidth 128 * g.signExtend 128 +
          c.signExtend 128) >>> 64).setWidth 64) := by
  have hZ : a.setWidth 128 * f.signExtend 128 + b.setWidth 128 * g.signExtend 128 +
      c.signExtend 128 =
      BitVec.ofInt 128 ((a.toNat : ℤ) * f.toInt + (b.toNat : ℤ) * g.toInt + c.toInt) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_mul,
      ← BitVec.setWidth_eq_ofInt_toNat (w := 64) (by norm_num),
      ← BitVec.setWidth_eq_ofInt_toNat (w := 64) (by norm_num)]
    rfl
  rw [hZ]
  unfold Word.smulAdd2
  generalize (a.toNat : ℤ) * f.toInt + (b.toNat : ℤ) * g.toInt + c.toInt = z
  refine Prod.ext ?_ ?_
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    omega

@[step]
theorem smul_add2_spec (a b f g c : U64) :
    smul_add2 a b f g c ⦃ (lo : U64) (hi : U64) =>
      lo.bv = (Word.smulAdd2 a.bv b.bv f.bv g.bv c.bv).1 ∧
        hi.bv = (Word.smulAdd2 a.bv b.bv f.bv g.bv c.bv).2 ⦄ := by
  unfold smul_add2
  step*
  rw [smulAdd2_eq]
  simp [*]

end Curve25519Dalek.backend.serial.u64.bingcd
