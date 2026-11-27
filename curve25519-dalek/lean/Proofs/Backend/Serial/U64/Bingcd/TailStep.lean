module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.Mask
import Proofs.Backend.Serial.U64.Bingcd.Subb
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- One step of the inner loop on words, with the two decisions as masks: the shape of the code
of `tail_step`. -/
private def maskedStep (s : Pornin.InnerW 64) : Pornin.InnerW 64 :=
  let aodd : Word 64 := 0 - (s.abar &&& 1)
  let swap := aodd &&& Word.mask 64 (Word.subb s.abar s.bbar false).2
  let t1 := swap &&& (s.abar ^^^ s.bbar)
  let xa := s.abar ^^^ t1
  let xb := s.bbar ^^^ t1
  let t2 := swap &&& (s.f0 ^^^ s.f1)
  let f0 := s.f0 ^^^ t2
  let f1 := s.f1 ^^^ t2
  let t3 := swap &&& (s.g0 ^^^ s.g1)
  let g0 := s.g0 ^^^ t3
  let g1 := s.g1 ^^^ t3
  ⟨(xa - (aodd &&& xb)) >>> 1, xb, f0 - (aodd &&& f1), g0 - (aodd &&& g1), f1 <<< 1, g1 <<< 1⟩

/-- A step with masks is a step of the inner loop on words. -/
private theorem maskedStep_eq (s : Pornin.InnerW 64) : maskedStep s = s.step := by
  obtain ⟨a, b, f0, g0, f1, g1⟩ := s
  simp only [maskedStep, Pornin.InnerW.step, Word.zero_sub_and_one]
  generalize decide (a.toNat % 2 = 1) = odd
  generalize (Word.subb a b false).2 = lt
  cases odd <;> cases lt <;>
    simp [Word.mask_true_and, Word.mask_false_and, Word.xor_xor_cancel_left,
      Word.xor_xor_cancel_right, Word.shiftLeft_one]

@[step]
theorem tail_step_spec (s : Tail) :
    tail_step s ⦃ r => r.toW = Pornin.InnerW.step s.toW ⦄ := by
  unfold tail_step
  step*
  rw [← maskedStep_eq]
  simp [Tail.toW, maskedStep, *]

end Curve25519Dalek.backend.serial.u64.bingcd
