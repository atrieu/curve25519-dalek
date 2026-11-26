module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- `Limbs.or` on four limbs, unfolded. -/
private theorem or_four (a0 a1 a2 a3 b0 b1 b2 b3 : Word 64) :
    Limbs.or #v[a0, a1, a2, a3] #v[b0, b1, b2, b3] =
      #v[a0 ||| b0, a1 ||| b1, a2 ||| b2, a3 ||| b3] := by
  ext i hi : 1
  interval_cases i <;> simp [Limbs.or]

@[step]
theorem or4_spec (a b : Array U64 4#usize) :
    or4 a b ⦃ r => L4 r = Limbs.or (L4 a) (L4 b) ⦄ := by
  unfold or4
  step*
  simp only [L4_make]
  simp [L4, or_four, *]

end Curve25519Dalek.backend.serial.u64.bingcd
