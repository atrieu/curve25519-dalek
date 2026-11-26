module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.InnerStep
import Proofs.Backend.Serial.U64.Bingcd.K
import Proofs.Backend.Serial.U64.Bingcd.UnpackRow
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- The loop of `inner`: the steps that remain, on the state with packed rows. -/
@[local step]
private theorem inner_loop_spec (s : Inner) (i : U32) (hi : i.val ≤ 31) :
    inner_loop s i ⦃ r => r.toP = Pornin.InnerP.step^[31 - i.val] s.toP ⦄ := by
  unfold inner_loop
  apply loop.spec_decr_nat (measure := fun x => 31 - x.2.val)
    (inv := fun x => x.2.val ≤ 31 ∧
      Pornin.InnerP.step^[31 - x.2.val] x.1.toP = Pornin.InnerP.step^[31 - i.val] s.toP)
  · rintro ⟨s', i'⟩ ⟨hi', hinv⟩
    simp only at hi' hinv ⊢
    unfold inner_loop.body
    by_cases h : i' < K
    · simp only [h, ↓reduceIte]
      step*
      have hk : 31 - i'.val = (31 - i1.val) + 1 := by scalar_tac
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [← hinv, hk, Function.iterate_succ_apply, s1_post]
    · simp only [h, ↓reduceIte, WP.spec_ok]
      have hk : 31 - i'.val = 0 := by scalar_tac
      rw [← hinv, hk]
      rfl
  · exact ⟨hi, rfl⟩

/-- **The inner loop computes the transition matrix**: the entries are those of 31 steps of
`Pornin.InnerW.step` from the approximations and the identity matrix. The rows are packed, each
in one word as `f + 2 ^ 32 * g`, and unpacked at the end (`Pornin.innerP_spec`). -/
@[step]
theorem inner_spec (abar bbar : U64) :
    inner abar bbar ⦃ r =>
      r.f0.bv = (Pornin.InnerW.step^[31] ⟨abar.bv, bbar.bv, 1, 0, 0, 1⟩).f0 ∧
        r.g0.bv = (Pornin.InnerW.step^[31] ⟨abar.bv, bbar.bv, 1, 0, 0, 1⟩).g0 ∧
        r.f1.bv = (Pornin.InnerW.step^[31] ⟨abar.bv, bbar.bv, 1, 0, 0, 1⟩).f1 ∧
        r.g1.bv = (Pornin.InnerW.step^[31] ⟨abar.bv, bbar.bv, 1, 0, 0, 1⟩).g1 ⦄ := by
  unfold inner
  step*
  have hinit : ({ abar := abar, bbar := bbar, fg0 := 1#u64, fg1 := 4294967296#u64 } : Inner).toP =
      ⟨abar.bv, bbar.bv, Pornin.pack 31 1 0, Pornin.pack 31 0 1⟩ := by
    have h1 : Pornin.pack 31 (1 : Word 64) 0 = 1#64 := by decide
    have h2 : Pornin.pack 31 (0 : Word 64) 1 = 4294967296#64 := by decide
    rw [h1, h2]
    rfl
  obtain ⟨h0, h1⟩ := Pornin.innerP_spec (w := 64) (K := 31) (by norm_num) abar.bv bbar.bv
  rw [Nat.sub_zero, hinit] at s_post
  have e0 : UScalar.bv s.fg0 =
      (Pornin.InnerP.step^[31] ⟨abar.bv, bbar.bv, Pornin.pack 31 1 0, Pornin.pack 31 0 1⟩).fg0 :=
    congrArg Pornin.InnerP.fg0 s_post
  have e1 : UScalar.bv s.fg1 =
      (Pornin.InnerP.step^[31] ⟨abar.bv, bbar.bv, Pornin.pack 31 1 0, Pornin.pack 31 0 1⟩).fg1 :=
    congrArg Pornin.InnerP.fg1 s_post
  simp only [f0_post, f0_post1, f1_post, f1_post1, U64.bv, e0, e1, h0, h1, and_self]

end Curve25519Dalek.backend.serial.u64.bingcd
