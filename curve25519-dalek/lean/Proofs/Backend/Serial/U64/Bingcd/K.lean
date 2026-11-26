module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

@[simp, scalar_tac_simps, grind =, agrind =]
theorem K_val : K.val = 31 := by simp [K]

end Curve25519Dalek.backend.serial.u64.bingcd
