module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.Mask25
import Proofs.Backend.Serial.U32.Bingcd.Mask26
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- `Limbs.Curve25519.U32.unpack` on eight limbs, unfolded. -/
private theorem unpack_eight (y0 y1 y2 y3 y4 y5 y6 y7 : Word 32) :
    Limbs.Curve25519.U32.unpack #v[y0, y1, y2, y3, y4, y5, y6, y7] =
      #v[y0 &&& 0x3FFFFFF#32,
        ((y0 >>> 26) + (y1 <<< 6)) &&& 0x1FFFFFF#32,
        ((y1 >>> 19) + (y2 <<< 13)) &&& 0x3FFFFFF#32,
        ((y2 >>> 13) + (y3 <<< 19)) &&& 0x1FFFFFF#32,
        y3 >>> 6,
        y4 &&& 0x1FFFFFF#32,
        ((y4 >>> 25) + (y5 <<< 7)) &&& 0x3FFFFFF#32,
        ((y5 >>> 19) + (y6 <<< 13)) &&& 0x1FFFFFF#32,
        ((y6 >>> 12) + (y7 <<< 20)) &&& 0x3FFFFFF#32,
        (y7 >>> 6) &&& 0x1FFFFFF#32] := rfl

@[step]
theorem unpack_spec (y : Array U32 8#usize) :
    unpack y ⦃ r => L10 r = Limbs.Curve25519.U32.unpack (L8 y) ⦄ := by
  unfold unpack
  step*
  subst i_post i4_post i10_post i15_post i20_post i23_post i28_post i33_post
  subst i6_post i12_post i17_post i25_post i30_post i35_post
  simp only [L10_make, L8, unpack_eight, core.num.U32.wrapping_add_bv_eq, i1_post, i7_post,
    i2_post1, i3_post1, i5_post1, i8_post1, i9_post1, i11_post1, i13_post1, i14_post1,
    i16_post1, i18_post1, i19_post1, i21_post1, i22_post1, i24_post1, i26_post1, i27_post1,
    i29_post1, i31_post1, i32_post1, i34_post1, i36_post1, i37_post1, i38_post1, U32.bv]

end Curve25519Dalek.backend.serial.u32.bingcd
