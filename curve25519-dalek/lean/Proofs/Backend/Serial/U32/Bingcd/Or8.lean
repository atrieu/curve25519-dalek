module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- `Limbs.or` on eight limbs, unfolded. -/
private theorem or_eight (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Word 32) :
    Limbs.or #v[a0, a1, a2, a3, a4, a5, a6, a7] #v[b0, b1, b2, b3, b4, b5, b6, b7] =
      #v[a0 ||| b0, a1 ||| b1, a2 ||| b2, a3 ||| b3, a4 ||| b4, a5 ||| b5, a6 ||| b6,
        a7 ||| b7] := by
  ext i hi : 1
  interval_cases i <;> simp [Limbs.or]

@[step]
theorem or8_spec (a b : Array U32 8#usize) :
    or8 a b ⦃ r => L8 r = Limbs.or (L8 a) (L8 b) ⦄ := by
  unfold or8
  step*
  simp only [L8_make]
  simp [L8, or_eight, *]

end Curve25519Dalek.backend.serial.u32.bingcd
