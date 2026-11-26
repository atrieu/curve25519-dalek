module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Select4
import Proofs.Backend.Serial.U64.Bingcd.ShrLow
import Proofs.Backend.Serial.U64.Bingcd.Sub4
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

@[step]
theorem shr_abs_spec (r : Array U64 4#usize) (c : U64) :
    shr_abs r c ⦃ (x : Array U64 4#usize) (neg : Bool) =>
      L4 x = (Limbs.shrAbs (L4 r) c.bv 31).1 ∧ neg = (Limbs.shrAbs (L4 r) c.bv 31).2 ⦄ := by
  unfold shr_abs
  step*
  have hmsb := msb_of_shr63 c i i_post
  rw [a1_post, n_post, L4_repeat_zero, low_post, hmsb]
  simp only [Limbs.shrAbs, Limbs.sub, ofNat_four_zero, and_self]

end Curve25519Dalek.backend.serial.u64.bingcd
