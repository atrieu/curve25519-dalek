module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.CondSub
import Proofs.Backend.Serial.U64.Bingcd.Mask51
import Proofs.Backend.Serial.U64.Bingcd.P
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

private theorem ofNat_mod_eq_and (s : Word 64) :
    BitVec.ofNat 64 (s.toNat % 2 ^ 51) = s &&& 0x7FFFFFFFFFFFF#64 := by
  apply BitVec.eq_of_toNat_eq
  have h := s.isLt
  rw [Limbs.Curve25519.toNat_and_mask51, BitVec.toNat_ofNat]
  omega

/-- `Limbs.carry 51` on five limbs, unfolded. -/
private theorem carry_five (a0 a1 a2 a3 a4 : Word 64) :
    Limbs.carry 51 (#v[a0, a1, a2, a3, a4] : Limbs 64 5) 0#64 =
      (#v[BitVec.ofNat 64 ((a0 + 0#64).toNat % 2 ^ 51),
          BitVec.ofNat 64 ((a1 + (a0 + 0#64) >>> 51).toNat % 2 ^ 51),
          BitVec.ofNat 64 ((a2 + (a1 + (a0 + 0#64) >>> 51) >>> 51).toNat % 2 ^ 51),
          BitVec.ofNat 64 ((a3 + (a2 + (a1 + (a0 + 0#64) >>> 51) >>> 51) >>> 51).toNat % 2 ^ 51),
          BitVec.ofNat 64
            ((a4 + (a3 + (a2 + (a1 + (a0 + 0#64) >>> 51) >>> 51) >>> 51) >>> 51).toNat % 2 ^ 51)],
        (a4 + (a3 + (a2 + (a1 + (a0 + 0#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51) := rfl

/-- `Limbs.Curve25519.freeze` on five limbs, unfolded: a carry pass with shifts and masks, a
packing and a conditional subtraction. -/
private theorem freeze_five (a0 a1 a2 a3 a4 : Word 64) :
    Limbs.Curve25519.freeze #v[a0, a1, a2, a3, a4] =
      Limbs.condSub
        #v[(a0 &&& 0x7FFFFFFFFFFFF#64) + (((a1 + a0 >>> 51) &&& 0x7FFFFFFFFFFFF#64) <<< 51),
          (((a1 + a0 >>> 51) &&& 0x7FFFFFFFFFFFF#64) >>> 13) +
            (((a2 + (a1 + a0 >>> 51) >>> 51) &&& 0x7FFFFFFFFFFFF#64) <<< 38),
          (((a2 + (a1 + a0 >>> 51) >>> 51) &&& 0x7FFFFFFFFFFFF#64) >>> 26) +
            (((a3 + (a2 + (a1 + a0 >>> 51) >>> 51) >>> 51) &&& 0x7FFFFFFFFFFFF#64) <<< 25),
          (((a3 + (a2 + (a1 + a0 >>> 51) >>> 51) >>> 51) &&& 0x7FFFFFFFFFFFF#64) >>> 39) +
            (((a4 + (a3 + (a2 + (a1 + a0 >>> 51) >>> 51) >>> 51) >>> 51) &&&
              0x7FFFFFFFFFFFF#64) <<< 12) +
            (((a4 + (a3 + (a2 + (a1 + a0 >>> 51) >>> 51) >>> 51) >>> 51) >>> 51) <<< 63)]
        false Limbs.Curve25519.P := by
  unfold Limbs.Curve25519.freeze
  simp only [carry_five, BitVec.add_zero, ofNat_mod_eq_and, Limbs.Curve25519.pack,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]

@[step]
theorem freeze_spec (a : Array U64 5#usize) :
    freeze a ⦃ r => L4 r = Limbs.Curve25519.freeze (L5 a) ⦄ := by
  unfold freeze
  step*
  subst s0_post i_post i2_post i4_post i6_post
  subst s1_post s2_post s3_post s4_post i10_post i13_post i16_post i19_post i21_post
  simp only [r_post, L4_make, L4_P, L5, freeze_five, core.num.U64.wrapping_add_bv_eq,
    i1_post1, i3_post1, i5_post1, i7_post1, i8_post, r0_post1, r1_post1, r2_post1, r3_post1,
    r4_post1, c_post1, i9_post1, i11_post1, i12_post1, i14_post1, i15_post1, i17_post1,
    i18_post1, i20_post1, U64.bv]

end Curve25519Dalek.backend.serial.u64.bingcd
