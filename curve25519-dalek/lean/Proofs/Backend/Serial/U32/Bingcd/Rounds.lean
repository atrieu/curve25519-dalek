module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

theorem ROUNDS_val : ROUNDS.val = 32 := by
  unfold ROUNDS
  rfl

end Curve25519Dalek.backend.serial.u32.bingcd
