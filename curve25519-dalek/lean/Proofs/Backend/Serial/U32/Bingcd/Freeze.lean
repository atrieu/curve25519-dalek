module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.CondSub
import Proofs.Backend.Serial.U32.Bingcd.Mask25
import Proofs.Backend.Serial.U32.Bingcd.Mask26
import Proofs.Backend.Serial.U32.Bingcd.P
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

@[step]
theorem freeze_spec (a : Array U32 10#usize) :
    freeze a ⦃ r => L8 r = Limbs.Curve25519.U32.freeze (L10 a) ⦄ := by
  unfold freeze
  step*
  subst s0_post i_post i2_post i4_post i6_post i8_post i10_post i12_post i14_post i16_post
  subst s1_post s2_post s3_post s4_post s5_post s6_post s7_post s8_post s9_post
  subst i21_post i24_post i27_post i30_post i32_post i35_post i38_post i41_post i43_post
  simp only [r_post, L8_make, L8_P, L10, Limbs.Curve25519.U32.freeze,
    Limbs.Curve25519.U32.carry, Limbs.Curve25519.U32.pack, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    core.num.U32.wrapping_add_bv_eq, i1_post1, i3_post1, i5_post1, i7_post1, i9_post1,
    i11_post1, i13_post1, i15_post1, i17_post1, i18_post, i19_post, r0_post1, r1_post1,
    r2_post1, r3_post1, r4_post1, r5_post1, r6_post1, r7_post1, r8_post1, r9_post1, c_post1,
    i20_post1, i22_post1, i23_post1, i25_post1, i26_post1, i28_post1, i29_post1, i31_post1,
    i33_post1, i34_post1, i36_post1, i37_post1, i39_post1, i40_post1, i42_post1, U32.bv]

end Curve25519Dalek.backend.serial.u32.bingcd
