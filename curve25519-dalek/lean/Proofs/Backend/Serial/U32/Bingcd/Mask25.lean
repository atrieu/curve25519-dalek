module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

@[step]
theorem MASK25_spec : MASK25 ⦃ r => UScalar.bv r = 0x1FFFFFF#32 ⦄ := by
  unfold MASK25
  step*

end Curve25519Dalek.backend.serial.u32.bingcd
