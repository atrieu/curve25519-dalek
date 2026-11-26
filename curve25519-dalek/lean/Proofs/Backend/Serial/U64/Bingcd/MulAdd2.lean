module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

@[step]
theorem mul_add2_spec (a b c d : U64) :
    mul_add2 a b c d ⦃ (lo : U64) (hi : U64) =>
      lo.bv = (Word.mulAdd2 a.bv b.bv c.bv d.bv).1 ∧
        hi.bv = (Word.mulAdd2 a.bv b.bv c.bv d.bv).2 ⦄ := by
  unfold mul_add2
  step*
  have hp : p.val = a.val * b.val + c.val + d.val := by simp [*]
  have hlt : p.val < 2 ^ 64 * 2 ^ 64 := by
    have := p.hBounds
    scalar_tac
  have h6 : i6.bv = BitVec.ofNat 64 (a.val * b.val + c.val + d.val) := by
    apply BitVec.eq_of_toNat_eq
    simp [i6_post, hp]
  have h8 : i8.bv = Word.highOfNat 64 (a.val * b.val + c.val + d.val) := by
    apply BitVec.eq_of_toNat_eq
    simp [i8_post, i7_post, hp, Word.highOfNat, Nat.shiftRight_eq_div_pow]
  simp only [Word.mulAdd2, U64.bv_toNat, h6, h8, and_self]

end Curve25519Dalek.backend.serial.u64.bingcd
