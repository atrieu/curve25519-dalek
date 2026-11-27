module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.Mask
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

@[step]
theorem select_spec (c : Bool) (a b : U32) :
    select c a b ⦃ r => r.bv = Word.select c a.bv b.bv ⦄ := by
  unfold select
  step*
  simp [Word.select, *]

end Curve25519Dalek.backend.serial.u32.bingcd
