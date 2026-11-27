module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.CofRow
import Proofs.Backend.Serial.U64.Bingcd.Freeze
import Proofs.Backend.Serial.U64.Bingcd.P
import Proofs.Backend.Serial.U64.Bingcd.Round
import Proofs.Backend.Serial.U64.Bingcd.Rounds
import Proofs.Backend.Serial.U64.Bingcd.Tail
import Proofs.Backend.Serial.U64.Field.Zero
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- The loop of `scaled_div`: the rounds that remain, as iterations of `Pornin.roundR`. -/
@[local step]
private theorem scaled_div_loop_spec (s : State) (i : U32) (hi : i.val ≤ 15)
    (hu : s.u.LimbsLt 52) (hv : s.v.LimbsLt 52) :
    scaled_div_loop s i ⦃ r =>
      r.toR = (Pornin.roundR 31)^[15 - i.val] s.toR ∧ r.u.LimbsLt 52 ∧ r.v.LimbsLt 52 ⦄ := by
  have hR := ROUNDS_val
  unfold scaled_div_loop
  apply loop.spec_decr_nat (measure := fun x => 15 - x.2.val)
    (inv := fun x => x.2.val ≤ 15 ∧ x.1.u.LimbsLt 52 ∧ x.1.v.LimbsLt 52 ∧
      (Pornin.roundR 31)^[15 - x.2.val] x.1.toR = (Pornin.roundR 31)^[15 - i.val] s.toR)
  · rintro ⟨s', i'⟩ ⟨hi', hu', hv', hinv⟩
    simp only at hi' hu' hv' hinv ⊢
    unfold scaled_div_loop.body
    by_cases h : i' < ROUNDS
    · simp only [h, ↓reduceIte]
      step as ⟨s1, hs1, hs1u, hs1v⟩
      step as ⟨i1, hi1⟩
      have hk : 15 - i'.val = (15 - i1.val) + 1 := by scalar_tac
      refine ⟨by scalar_tac, hs1u, hs1v, ?_, by scalar_tac⟩
      rw [← hinv, hk, Function.iterate_succ_apply, hs1]
    · simp only [h, ↓reduceIte, WP.spec_ok]
      have hk : 15 - i'.val = 0 := by scalar_tac
      refine ⟨?_, hu', hv'⟩
      rw [← hinv, hk]
      rfl
  · exact ⟨hi, hu, hv, rfl⟩

/-- **The translated run is `Pornin.porninDivR`**, with the cofactors in the field: 15 rounds and
43 last steps on the canonical form of `z` and the modulus, from the cofactor `u`. -/
@[step]
theorem scaled_div_spec (u : field.FieldElement51) (z : Array U64 5#usize)
    (hu : u.LimbsLt 52) :
    scaled_div u z ⦃ (r : field.FieldElement51) =>
      r.toField = Pornin.porninDivR 31 15 43 Limbs.Curve25519.P u.toField
        (Limbs.Curve25519.freeze (L5 z)) ∧ r.LimbsLt 52 ⦄ := by
  unfold scaled_div
  step as ⟨a, ha⟩
  step as ⟨fe, hfe, hfeb⟩
  have hfeb' : fe.LimbsLt 52 := fun j hj => lt_trans (hfeb j hj) (by norm_num)
  step with scaled_div_loop_spec { a := a, u := u, b := P, v := fe } 0#u32 (by scalar_tac) hu
    hfeb' as ⟨s, hs, hsu, hsv⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨t, ht⟩
  -- the entries of the matrix of the last steps are at most `2^43` in absolute value
  obtain ⟨-, hm1⟩ := Pornin.innerW_matBound (t := 43) (by norm_num) i.bv i1.bv
  have ht' : t.toW = Pornin.InnerW.step^[43] ⟨i.bv, i1.bv, 1, 0, 0, 1⟩ := ht
  have hf1 : t.f1.bv = (Pornin.InnerW.step^[43] ⟨i.bv, i1.bv, 1, 0, 0, 1⟩).f1 :=
    congrArg Pornin.InnerW.f1 ht'
  have hg1 : t.g1.bv = (Pornin.InnerW.step^[43] ⟨i.bv, i1.bv, 1, 0, 0, 1⟩).g1 :=
    congrArg Pornin.InnerW.g1 ht'
  rw [← hf1, ← hg1] at hm1
  step with cof_row_spec s.u s.v t.f1 t.g1 false hsu hsv
    (by linarith [abs_nonneg t.g1.bv.toInt]) (by linarith [abs_nonneg t.f1.bv.toInt])
    as ⟨r, hr, hrb⟩
  refine ⟨?_, hrb⟩
  have hfe0 : fe.toField = 0 := by
    rw [field.FieldElement51.toField_def, hfe]
    exact Nat.cast_zero
  have hinit : ({ a := a, u := u, b := P, v := fe } : State).toR =
      (Limbs.Curve25519.freeze (L5 z), u.toField, Limbs.Curve25519.P, 0) := by
    simp only [State.toR, ha, L4_P, hfe0]
  rw [Nat.sub_zero, hinit] at hs
  have hi' : i.bv = (L4 s.a)[0] := by
    rw [hi]
    rfl
  have hi1' : i1.bv = (L4 s.b)[0] := by
    rw [hi1]
    rfl
  rw [hr, Pornin.porninDivR, ← hs, Pornin.tailR, hf1, hg1, hi', hi1']
  rfl

end Curve25519Dalek.backend.serial.u64.bingcd
