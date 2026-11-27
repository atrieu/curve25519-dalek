module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.CofRow
import Proofs.Backend.Serial.U32.Bingcd.Freeze
import Proofs.Backend.Serial.U32.Bingcd.P
import Proofs.Backend.Serial.U32.Bingcd.Round
import Proofs.Backend.Serial.U32.Bingcd.Rounds
import Proofs.Backend.Serial.U32.Bingcd.Tail
import Proofs.Backend.Serial.U32.Field.Zero
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- The loop of `scaled_div`: the rounds that remain, as iterations of `Pornin.roundR`. -/
@[local step]
private theorem scaled_div_loop_spec (s : State) (i : U32) (hi : i.val ≤ 32)
    (hu : s.u.LimbsLt 26) (hv : s.v.LimbsLt 26) :
    scaled_div_loop s i ⦃ r =>
      r.toR = (Pornin.roundR 15)^[32 - i.val] s.toR ∧ r.u.LimbsLt 26 ∧ r.v.LimbsLt 26 ⦄ := by
  have hR := ROUNDS_val
  unfold scaled_div_loop
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.val)
    (inv := fun x => x.2.val ≤ 32 ∧ x.1.u.LimbsLt 26 ∧ x.1.v.LimbsLt 26 ∧
      (Pornin.roundR 15)^[32 - x.2.val] x.1.toR = (Pornin.roundR 15)^[32 - i.val] s.toR)
  · rintro ⟨s', i'⟩ ⟨hi', hu', hv', hinv⟩
    simp only at hi' hu' hv' hinv ⊢
    unfold scaled_div_loop.body
    by_cases h : i' < ROUNDS
    · simp only [h, ↓reduceIte]
      step as ⟨s1, hs1, hs1u, hs1v⟩
      step as ⟨i1, hi1⟩
      have hk : 32 - i'.val = (32 - i1.val) + 1 := by scalar_tac
      refine ⟨by scalar_tac, hs1u, hs1v, ?_, by scalar_tac⟩
      rw [← hinv, hk, Function.iterate_succ_apply, hs1]
    · simp only [h, ↓reduceIte, WP.spec_ok]
      have hk : 32 - i'.val = 0 := by scalar_tac
      refine ⟨?_, hu', hv'⟩
      rw [← hinv, hk]
      rfl
  · exact ⟨hi, hu, hv, rfl⟩

/-- **The translated run is `Pornin.porninDivR`**, with the cofactors in the field: 32 rounds and
28 last steps on the canonical form of `z` and the modulus, from the cofactor `u`. -/
@[step]
theorem scaled_div_spec (u : field.FieldElement2625) (z : Array U32 10#usize)
    (hu : u.LimbsLt 26) :
    scaled_div u z ⦃ (r : field.FieldElement2625) =>
      r.toField = Pornin.porninDivR 15 32 28 Limbs.Curve25519.U32.P u.toField
        (Limbs.Curve25519.U32.freeze (L10 z)) ∧ r.LimbsLt 26 ⦄ := by
  unfold scaled_div
  step as ⟨a, ha⟩
  step as ⟨fe, hfe, hfeb⟩
  step with scaled_div_loop_spec { a := a, u := u, b := P, v := fe } 0#u32 (by scalar_tac) hu
    hfeb as ⟨s, hs, hsu, hsv⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨t, ht⟩
  -- the entries of the matrix of the last steps are at most `2^28` in absolute value
  obtain ⟨-, hm1⟩ := Pornin.innerW_matBound (t := 28) (by norm_num) i.bv i1.bv
  have ht' : t.toW = Pornin.InnerW.step^[28] ⟨i.bv, i1.bv, 1, 0, 0, 1⟩ := ht
  have hf1 : t.f1.bv = (Pornin.InnerW.step^[28] ⟨i.bv, i1.bv, 1, 0, 0, 1⟩).f1 :=
    congrArg Pornin.InnerW.f1 ht'
  have hg1 : t.g1.bv = (Pornin.InnerW.step^[28] ⟨i.bv, i1.bv, 1, 0, 0, 1⟩).g1 :=
    congrArg Pornin.InnerW.g1 ht'
  rw [← hf1, ← hg1] at hm1
  step with cof_row_spec s.u s.v t.f1 t.g1 false hsu hsv
    (by linarith [abs_nonneg t.g1.bv.toInt]) (by linarith [abs_nonneg t.f1.bv.toInt])
    as ⟨r, hr, hrb⟩
  refine ⟨?_, hrb⟩
  have hfe0 : fe.toField = 0 := by
    rw [field.FieldElement2625.toField_def, hfe]
    exact Nat.cast_zero
  have hinit : ({ a := a, u := u, b := P, v := fe } : State).toR =
      (Limbs.Curve25519.U32.freeze (L10 z), u.toField, Limbs.Curve25519.U32.P, 0) := by
    simp only [State.toR, ha, L8_P, hfe0]
  rw [Nat.sub_zero, hinit] at hs
  have hi' : i.bv = (L8 s.a)[0] := by
    rw [hi]
    rfl
  have hi1' : i1.bv = (L8 s.b)[0] := by
    rw [hi1]
    rfl
  rw [hr, Pornin.porninDivR, ← hs, Pornin.tailR, hf1, hg1, hi', hi1']
  rfl

end Curve25519Dalek.backend.serial.u32.bingcd
