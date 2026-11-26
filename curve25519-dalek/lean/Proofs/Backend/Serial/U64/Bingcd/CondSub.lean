module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Select4
import Proofs.Backend.Serial.U64.Bingcd.Sub4
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

@[step]
theorem cond_sub_spec (a : Array U64 4#usize) (c : Bool) (p : Array U64 4#usize) :
    cond_sub a c p ⦃ r => L4 r = Limbs.condSub (L4 a) c (L4 p) ⦄ := by
  unfold cond_sub
  step*
  simp [Limbs.condSub, *]

end Curve25519Dalek.backend.serial.u64.bingcd
