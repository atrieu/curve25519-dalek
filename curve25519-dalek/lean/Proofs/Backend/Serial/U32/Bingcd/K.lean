module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

@[simp, scalar_tac_simps, grind =, agrind =]
theorem K_val : K.val = 15 := by simp [K]

end Curve25519Dalek.backend.serial.u32.bingcd
