module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.Select8
import Proofs.Backend.Serial.U32.Bingcd.Sub8
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

@[step]
theorem cond_sub_spec (a : Array U32 8#usize) (c : Bool) (p : Array U32 8#usize) :
    cond_sub a c p ⦃ r => L8 r = Limbs.condSub (L8 a) c (L8 p) ⦄ := by
  unfold cond_sub
  step*
  simp [Limbs.condSub, *]

end Curve25519Dalek.backend.serial.u32.bingcd
