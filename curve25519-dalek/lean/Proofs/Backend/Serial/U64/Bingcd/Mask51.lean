module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

@[step]
theorem MASK51_spec : MASK51 ⦃ r => UScalar.bv r = 0x7FFFFFFFFFFFF#64 ⦄ := by
  unfold MASK51
  step*

end Curve25519Dalek.backend.serial.u64.bingcd
