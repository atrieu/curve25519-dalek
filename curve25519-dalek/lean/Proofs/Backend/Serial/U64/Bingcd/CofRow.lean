module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.LinCombRedc
import Proofs.Backend.Serial.U64.Bingcd.Select
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

@[step]
theorem cof_row_spec (u v : Array U64 4#usize) (f g : U64) (neg : Bool)
    (m : Array U64 4#usize) (ninv : U64) :
    cof_row u v f g neg m ninv ⦃ x =>
      L4 x = Pornin.cofRow (L4 u) (L4 v) f.bv g.bv neg (L4 m) ninv.bv 31 ⦄ := by
  unfold cof_row
  step*
  have h0 : UScalar.bv 0#u64 = 0#64 := rfl
  have hi : i.bv = -f.bv := by
    simp only [i_post, core.num.U64.wrapping_sub_bv_eq, h0, U64.bv, BitVec.zero_sub]
  have hi2 : i2.bv = -g.bv := by
    simp only [i2_post, core.num.U64.wrapping_sub_bv_eq, h0, U64.bv, BitVec.zero_sub]
  simp only [x_post, i1_post, i3_post, hi, hi2, Pornin.cofRow, U64.bv]

end Curve25519Dalek.backend.serial.u64.bingcd
