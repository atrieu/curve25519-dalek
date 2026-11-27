module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- `Pornin.unpack 15` with its constants written out: add `2 ^ 15 - 1` to both halves, split
the word, and subtract `2 ^ 15 - 1` from each half. -/
private theorem pornin_unpack_eq (fg : Word 32) :
    Pornin.unpack 15 fg =
      (((fg + 0x7FFF7FFF#32) &&& 0xFFFF#32) - 0x7FFF#32,
        ((fg + 0x7FFF7FFF#32) >>> 16) - 0x7FFF#32) := by
  have h1 : Pornin.pack 15 (0x7FFF#32 : Word 32) 0x7FFF#32 = 0x7FFF7FFF#32 := by decide
  have h2 : Pornin.bias 32 15 = 0x7FFF#32 := by decide
  have h3 : BitVec.ofNat 32 (2 ^ (15 + 1) - 1) = 0xFFFF#32 := by decide
  simp only [Pornin.unpack, h2, h1, h3, Nat.reduceAdd]

@[step]
theorem unpack_row_spec (fg : U32) :
    unpack_row fg ⦃ (f : U32) (g : U32) =>
      f.bv = (Pornin.unpack 15 fg.bv).1 ∧ g.bv = (Pornin.unpack 15 fg.bv).2 ⦄ := by
  unfold unpack_row
  step*
  simp [pornin_unpack_eq, *]

end Curve25519Dalek.backend.serial.u32.bingcd
