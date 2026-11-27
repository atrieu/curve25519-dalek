module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

theorem ROUNDS_val : ROUNDS.val = 15 := by
  unfold ROUNDS
  rfl

end Curve25519Dalek.backend.serial.u64.bingcd
