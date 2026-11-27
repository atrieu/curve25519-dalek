module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.ApplyRow
import Proofs.Backend.Serial.U32.Bingcd.ApproxTop
import Proofs.Backend.Serial.U32.Bingcd.CofRow
import Proofs.Backend.Serial.U32.Bingcd.Inner
import Proofs.Backend.Serial.U32.Bingcd.Or8
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- **A round is `Pornin.roundR`.** The Rust code reads the approximations from the limbs at
the top of `a | b`; they are those of `roundR` by `Pornin.approxL_eq_approxTop`. The cofactors
keep limbs below `2^26`. -/
@[step]
theorem round_spec (s : State) (hu : s.u.LimbsLt 26) (hv : s.v.LimbsLt 26) :
    round s ⦃ r => r.toR = Pornin.roundR 15 s.toR ∧ r.u.LimbsLt 26 ∧ r.v.LimbsLt 26 ⦄ := by
  unfold round
  step as ⟨ab, hab⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨t, ht0, ht1, ht2, ht3⟩
  step as ⟨a1, na, ha1, hna⟩
  step as ⟨b1, nb, hb1, hnb⟩
  -- the entries of the matrix are at most `2^15` in absolute value
  obtain ⟨hm0, hm1⟩ := Pornin.innerW_matBound (t := 15) (by norm_num) i.bv i1.bv
  rw [← ht0, ← ht1] at hm0
  rw [← ht2, ← ht3] at hm1
  have hf0 : |t.f0.bv.toInt| ≤ 2 ^ 28 := by linarith [abs_nonneg t.g0.bv.toInt]
  have hg0 : |t.g0.bv.toInt| ≤ 2 ^ 28 := by linarith [abs_nonneg t.f0.bv.toInt]
  have hf1 : |t.f1.bv.toInt| ≤ 2 ^ 28 := by linarith [abs_nonneg t.g1.bv.toInt]
  have hg1 : |t.g1.bv.toInt| ≤ 2 ^ 28 := by linarith [abs_nonneg t.f1.bv.toInt]
  step with cof_row_spec s.u s.v t.f0 t.g0 na hu hv hf0 hg0 as ⟨u1, hu1, hu1b⟩
  step with cof_row_spec s.u s.v t.f1 t.g1 nb hu hv hf1 hg1 as ⟨v1, hv1, hv1b⟩
  refine ⟨?_, hu1b, hv1b⟩
  obtain ⟨ha, hb⟩ := Pornin.approxL_eq_approxTop (w := 32) (K := 15) rfl (L8 s.a) (L8 s.b)
  rw [hab, ← ha] at hi
  rw [hab, ← hb] at hi1
  simp only [State.toR, Pornin.roundR, ha1, hna, hb1, hnb, hu1, hv1, ht0, ht1, ht2, ht3, hi, hi1,
    U32.bv]

end Curve25519Dalek.backend.serial.u32.bingcd
