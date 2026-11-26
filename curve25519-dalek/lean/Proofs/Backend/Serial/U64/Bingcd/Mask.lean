module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

@[step]
theorem mask_spec (c : Bool) : mask c ⦃ r => r.bv = Word.mask 64 c ⦄ := by
  unfold mask
  step*
  have hi : i.bv = BitVec.ofNat 64 c.toNat := by
    apply BitVec.eq_of_toNat_eq
    cases c <;> simp_all
  rw [core.num.U64.wrapping_sub_bv_eq, hi]
  cases c <;> decide

end Curve25519Dalek.backend.serial.u64.bingcd
