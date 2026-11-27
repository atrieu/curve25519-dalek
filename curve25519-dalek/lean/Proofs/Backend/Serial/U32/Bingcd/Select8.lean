module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.Select
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- `Limbs.select` on eight limbs, unfolded. -/
private theorem select_eight (c : Bool)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Word 32) :
    Limbs.select c #v[a0, a1, a2, a3, a4, a5, a6, a7] #v[b0, b1, b2, b3, b4, b5, b6, b7] =
      #v[Word.select c a0 b0, Word.select c a1 b1, Word.select c a2 b2, Word.select c a3 b3,
        Word.select c a4 b4, Word.select c a5 b5, Word.select c a6 b6, Word.select c a7 b7] := by
  ext i hi : 1
  interval_cases i <;> simp [Limbs.select]

@[step]
theorem select8_spec (c : Bool) (a b : Array U32 8#usize) :
    select8 c a b ⦃ r => L8 r = Limbs.select c (L8 a) (L8 b) ⦄ := by
  unfold select8
  step*
  simp only [L8_make]
  simp [L8, select_eight, *]

end Curve25519Dalek.backend.serial.u32.bingcd
