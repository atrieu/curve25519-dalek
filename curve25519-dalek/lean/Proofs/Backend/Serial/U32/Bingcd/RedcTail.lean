module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.Add8
import Proofs.Backend.Serial.U32.Bingcd.CondSub
import Proofs.Backend.Serial.U32.Bingcd.Select8
import Proofs.Backend.Serial.U32.Bingcd.ShrLow
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

@[step]
theorem redc_tail_spec (S : U32) (r : Array U32 8#usize) (c : U32) (m : Array U32 8#usize)
    (hS0 : 0 < S.val) (hS : S.val < 32) :
    redc_tail S r c m ⦃ x => L8 x = Limbs.redcTail (L8 r) c.bv (L8 m) S.val ⦄ := by
  unfold redc_tail
  step*
  have hmsb := msb_of_shr31 c i i_post
  have hback : (Limbs.shr ((L8 r).push c.bv) S.val).1.back = c.bv >>> S.val := by
    rw [L8, shr_push_back _ _ _ _ _ _ _ _ _ hS]
  have htop : (top != 0#u32) = decide ((c.bv >>> S.val).toNat ≠ 0) := by
    have hiff : top = 0#u32 ↔ top.val = 0 :=
      ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq h⟩
    rw [bne, Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq, hiff, top_post,
      BitVec.toNat_ushiftRight, U32.bv_toNat]
  rw [x_post, a_post, a1_post, low_post, hmsb, htop, ← hback]
  rfl

end Curve25519Dalek.backend.serial.u32.bingcd
