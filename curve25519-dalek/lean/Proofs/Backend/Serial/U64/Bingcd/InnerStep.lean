module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Mask
import Proofs.Backend.Serial.U64.Bingcd.Subb
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

@[step]
theorem inner_step_spec (s : Inner) :
    inner_step s ⦃ r => r.toP = Pornin.InnerP.step s.toP ⦄ := by
  unfold inner_step
  step*
  simp [Inner.toP, Pornin.InnerP.step, *]

end Curve25519Dalek.backend.serial.u64.bingcd
