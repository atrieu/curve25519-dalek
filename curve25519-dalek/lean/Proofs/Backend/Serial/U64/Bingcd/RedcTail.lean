module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Add4
import Proofs.Backend.Serial.U64.Bingcd.CondSub
import Proofs.Backend.Serial.U64.Bingcd.Select4
import Proofs.Backend.Serial.U64.Bingcd.ShrLow
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

@[step]
theorem redc_tail_spec (S : U32) (r : Array U64 4#usize) (c : U64) (m : Array U64 4#usize)
    (hS0 : 0 < S.val) (hS : S.val < 64) :
    redc_tail S r c m ⦃ x => L4 x = Limbs.redcTail (L4 r) c.bv (L4 m) S.val ⦄ := by
  unfold redc_tail
  step*
  have hmsb := msb_of_shr63 c i i_post
  have hback : (Limbs.shr ((L4 r).push c.bv) S.val).1.back = c.bv >>> S.val := by
    rw [L4, shr_push_back _ _ _ _ _ hS]
  have htop : (top != 0#u64) = decide ((c.bv >>> S.val).toNat ≠ 0) := by
    have hiff : top = 0#u64 ↔ top.val = 0 :=
      ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq h⟩
    rw [bne, Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq, hiff, top_post,
      BitVec.toNat_ushiftRight, U64.bv_toNat]
  rw [x_post, a_post, a1_post, low_post, hmsb, htop, ← hback]
  rfl

end Curve25519Dalek.backend.serial.u64.bingcd
