module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- `Pornin.unpack 31` with its constants written out: add `2 ^ 31 - 1` to both halves, split
the word, and subtract `2 ^ 31 - 1` from each half. -/
private theorem pornin_unpack_eq (fg : Word 64) :
    Pornin.unpack 31 fg =
      (((fg + 0x7FFFFFFF7FFFFFFF#64) &&& 0xFFFFFFFF#64) - 0x7FFFFFFF#64,
        ((fg + 0x7FFFFFFF7FFFFFFF#64) >>> 32) - 0x7FFFFFFF#64) := by
  have h1 : Pornin.pack 31 (0x7FFFFFFF#64 : Word 64) 0x7FFFFFFF#64 = 0x7FFFFFFF7FFFFFFF#64 := by
    decide
  have h2 : Pornin.bias 64 31 = 0x7FFFFFFF#64 := by decide
  have h3 : BitVec.ofNat 64 (2 ^ (31 + 1) - 1) = 0xFFFFFFFF#64 := by decide
  simp only [Pornin.unpack, h2, h1, h3, Nat.reduceAdd]

@[step]
theorem unpack_row_spec (fg : U64) :
    unpack_row fg ⦃ (f : U64) (g : U64) =>
      f.bv = (Pornin.unpack 31 fg.bv).1 ∧ g.bv = (Pornin.unpack 31 fg.bv).2 ⦄ := by
  unfold unpack_row
  step*
  simp [pornin_unpack_eq, *]

end Curve25519Dalek.backend.serial.u64.bingcd
