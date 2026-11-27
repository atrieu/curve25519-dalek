module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.Select8
import Proofs.Backend.Serial.U32.Bingcd.ShrLow
import Proofs.Backend.Serial.U32.Bingcd.Sub8
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

@[step]
theorem shr_abs_spec (r : Array U32 8#usize) (c : U32) :
    shr_abs r c ⦃ (x : Array U32 8#usize) (neg : Bool) =>
      L8 x = (Limbs.shrAbs (L8 r) c.bv 15).1 ∧ neg = (Limbs.shrAbs (L8 r) c.bv 15).2 ⦄ := by
  unfold shr_abs
  step*
  have hmsb := msb_of_shr31 c i i_post
  rw [a1_post, n_post, L8_repeat_zero, low_post, hmsb]
  simp only [Limbs.shrAbs, Limbs.sub, ofNat_eight_zero, and_self]

end Curve25519Dalek.backend.serial.u32.bingcd
