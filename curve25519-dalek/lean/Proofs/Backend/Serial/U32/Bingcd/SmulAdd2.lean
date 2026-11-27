module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Helpers.Bitwise
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- The signed multiply-add `Word.smulAdd2`, as a computation on 64-bit vectors with wrapping
operations: sign extensions of `f`, `g`, `c`, and zero extensions of `a`, `b`. -/
private theorem smulAdd2_eq (a b f g c : Word 32) :
    Word.smulAdd2 a b f g c =
      ((a.setWidth 64 * f.signExtend 64 + b.setWidth 64 * g.signExtend 64 +
          c.signExtend 64).setWidth 32,
        ((a.setWidth 64 * f.signExtend 64 + b.setWidth 64 * g.signExtend 64 +
          c.signExtend 64) >>> 32).setWidth 32) := by
  have hZ : a.setWidth 64 * f.signExtend 64 + b.setWidth 64 * g.signExtend 64 +
      c.signExtend 64 =
      BitVec.ofInt 64 ((a.toNat : ℤ) * f.toInt + (b.toNat : ℤ) * g.toInt + c.toInt) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_mul,
      ← BitVec.setWidth_eq_ofInt_toNat (w := 32) (by norm_num),
      ← BitVec.setWidth_eq_ofInt_toNat (w := 32) (by norm_num)]
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
theorem smul_add2_spec (a b f g c : U32) :
    smul_add2 a b f g c ⦃ (lo : U32) (hi : U32) =>
      lo.bv = (Word.smulAdd2 a.bv b.bv f.bv g.bv c.bv).1 ∧
        hi.bv = (Word.smulAdd2 a.bv b.bv f.bv g.bv c.bv).2 ⦄ := by
  unfold smul_add2
  step*
  rw [smulAdd2_eq]
  simp [*]

end Curve25519Dalek.backend.serial.u32.bingcd
