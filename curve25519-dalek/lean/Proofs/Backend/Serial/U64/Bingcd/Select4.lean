module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Select
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- `Limbs.select` on four limbs, unfolded. -/
private theorem select_four (c : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word 64) :
    Limbs.select c #v[a0, a1, a2, a3] #v[b0, b1, b2, b3] =
      #v[Word.select c a0 b0, Word.select c a1 b1, Word.select c a2 b2, Word.select c a3 b3] := by
  ext i hi : 1
  interval_cases i <;> simp [Limbs.select]

@[step]
theorem select4_spec (c : Bool) (a b : Array U64 4#usize) :
    select4 c a b ⦃ r => L4 r = Limbs.select c (L4 a) (L4 b) ⦄ := by
  unfold select4
  step*
  simp only [L4_make]
  simp [L4, select_four, *]

end Curve25519Dalek.backend.serial.u64.bingcd
