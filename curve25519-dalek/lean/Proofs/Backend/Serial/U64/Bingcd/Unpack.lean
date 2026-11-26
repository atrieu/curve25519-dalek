module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Mask51
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- `Limbs.Curve25519.unpack` on four limbs, unfolded. -/
private theorem unpack_four (y0 y1 y2 y3 : Word 64) :
    Limbs.Curve25519.unpack #v[y0, y1, y2, y3] =
      #v[y0 &&& 0x7FFFFFFFFFFFF#64,
        ((y0 >>> 51) + (y1 <<< 13)) &&& 0x7FFFFFFFFFFFF#64,
        ((y1 >>> 38) + (y2 <<< 26)) &&& 0x7FFFFFFFFFFFF#64,
        ((y2 >>> 25) + (y3 <<< 39)) &&& 0x7FFFFFFFFFFFF#64,
        (y3 >>> 12) &&& 0x7FFFFFFFFFFFF#64] := rfl

@[step]
theorem unpack_spec (y : Array U64 4#usize) :
    unpack y ⦃ r => L5 r = Limbs.Curve25519.unpack (L4 y) ⦄ := by
  unfold unpack
  step*
  subst i_post i4_post i9_post i14_post
  subst i6_post i11_post i16_post
  simp only [L5_make, L4, unpack_four, core.num.U64.wrapping_add_bv_eq, i1_post,
    i2_post1, i3_post1, i5_post1, i7_post1, i8_post1, i10_post1, i12_post1, i13_post1,
    i15_post1, i17_post1, i18_post1, i19_post1, U64.bv]

end Curve25519Dalek.backend.serial.u64.bingcd
