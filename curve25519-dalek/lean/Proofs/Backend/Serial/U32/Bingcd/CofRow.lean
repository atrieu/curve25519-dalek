module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.LinCombRedc
import Proofs.Backend.Serial.U32.Bingcd.Select
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

@[step]
theorem cof_row_spec (u v : Array U32 8#usize) (f g : U32) (neg : Bool)
    (m : Array U32 8#usize) (ninv : U32) :
    cof_row u v f g neg m ninv ⦃ x =>
      L8 x = Pornin.cofRow (L8 u) (L8 v) f.bv g.bv neg (L8 m) ninv.bv 15 ⦄ := by
  unfold cof_row
  step*
  have h0 : UScalar.bv 0#u32 = 0#32 := rfl
  have hi : i.bv = -f.bv := by
    simp only [i_post, core.num.U32.wrapping_sub_bv_eq, h0, U32.bv, BitVec.zero_sub]
  have hi2 : i2.bv = -g.bv := by
    simp only [i2_post, core.num.U32.wrapping_sub_bv_eq, h0, U32.bv, BitVec.zero_sub]
  simp only [x_post, i1_post, i3_post, hi, hi2, Pornin.cofRow, U32.bv]

end Curve25519Dalek.backend.serial.u32.bingcd
