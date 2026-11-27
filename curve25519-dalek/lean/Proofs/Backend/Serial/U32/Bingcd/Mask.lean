module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

@[step]
theorem mask_spec (c : Bool) : mask c ⦃ r => r.bv = Word.mask 32 c ⦄ := by
  unfold mask
  step*
  have hi : i.bv = BitVec.ofNat 32 c.toNat := by
    apply BitVec.eq_of_toNat_eq
    cases c <;> simp_all
  rw [core.num.U32.wrapping_sub_bv_eq, hi]
  cases c <;> decide

end Curve25519Dalek.backend.serial.u32.bingcd
