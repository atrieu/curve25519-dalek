module
public import Proofs.Helpers.Bingcd.Inversion

/-! # Pornin's optimized binary gcd: cofactors divided by `2 ^ K` at every round

In `round`, the cofactors pick up a factor `2 ^ K` per round, removed by one final
correction. Implementations instead divide the cofactors by `2 ^ K` modulo `m` at every
round, with a Montgomery reduction, so that no final correction is needed. This file defines
that variant over the integers and shows that it computes the same inverse. -/

@[expose] public section

namespace Bingcd.Pornin

/-- One round with the cofactors divided by `2 ^ K` modulo `m`. -/
def roundM (m K : ℕ) (s : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let p := max (max s.1.size s.2.2.1.size) (2 * K + 2) - K - 2
  let t := Inner.step^[K] ⟨approx K p s.1, approx K p s.2.2.1, 1, 0, 0, 1⟩
  let a' : ℤ := (s.1 * t.f0 + s.2.2.1 * t.g0) / 2 ^ K
  let b' : ℤ := (s.1 * t.f1 + s.2.2.1 * t.g1) / 2 ^ K
  let u' : ℤ := s.2.1 * t.f0 + s.2.2.2 * t.g0
  let v' : ℤ := s.2.1 * t.f1 + s.2.2.2 * t.g1
  (a'.natAbs, ((if a' < 0 then -u' else u') * (((m + 1) / 2 : ℕ) : ℤ) ^ K % m).toNat,
    b'.natAbs, ((if b' < 0 then -v' else v') * (((m + 1) / 2 : ℕ) : ℤ) ^ K % m).toNat)

/-- The states of `round` and `roundM` after `i` rounds. -/
def Sim (m K i : ℕ) (s s' : ℕ × ℕ × ℕ × ℕ) : Prop :=
  s'.1 = s.1 ∧ s'.2.2.1 = s.2.2.1 ∧
    (s'.2.1 : ℤ) = s.2.1 * (((m + 1) / 2 : ℕ) : ℤ) ^ (K * i) % m ∧
    (s'.2.2.2 : ℤ) = s.2.2.2 * (((m + 1) / 2 : ℕ) : ℤ) ^ (K * i) % m

theorem cofactor_sim {m u v u' v' f g c H : ℤ} (hu : u' = u * c % m) (hv : v' = v * c % m)
    (P : Prop) [Decidable P] :
    (if P then -(u' * f + v' * g) else u' * f + v' * g) * H % m =
      (if P then -(u * f + v * g) else u * f + v * g) % m * (c * H) % m := by
  have hu' : u' ≡ u * c [ZMOD m] := by rw [hu]; exact Int.mod_modEq _ _
  have hv' : v' ≡ v * c [ZMOD m] := by rw [hv]; exact Int.mod_modEq _ _
  have key : u' * f + v' * g ≡ (u * f + v * g) * c [ZMOD m] := by
    have := (hu'.mul_right f).add (hv'.mul_right g)
    rwa [show u * c * f + v * c * g = (u * f + v * g) * c by ring] at this
  change _ ≡ _ [ZMOD m]
  split_ifs
  · calc -(u' * f + v' * g) * H ≡ -((u * f + v * g) * c) * H [ZMOD m] := key.neg.mul_right H
      _ = -(u * f + v * g) * (c * H) := by ring
      _ ≡ -(u * f + v * g) % m * (c * H) [ZMOD m] := (Int.mod_modEq _ _).symm.mul_right _
  · calc (u' * f + v' * g) * H ≡ (u * f + v * g) * c * H [ZMOD m] := key.mul_right H
      _ = (u * f + v * g) * (c * H) := by ring
      _ ≡ (u * f + v * g) % m * (c * H) [ZMOD m] := (Int.mod_modEq _ _).symm.mul_right _

theorem sim_round {m K i : ℕ} (hm : 0 < m) {s s' : ℕ × ℕ × ℕ × ℕ} (h : Sim m K i s s') :
    Sim m K (i + 1) (round m K s) (roundM m K s') := by
  obtain ⟨a, u, b, v⟩ := s
  obtain ⟨a', u', b', v'⟩ := s'
  obtain ⟨rfl, rfl, hu, hv⟩ := h
  dsimp only at hu hv
  have hm' : (m : ℤ) ≠ 0 := by omega
  unfold Sim round roundM
  dsimp only
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm'), Int.toNat_of_nonneg (Int.emod_nonneg _ hm'),
      Nat.mul_succ, pow_add]
    exact cofactor_sim hu hv _
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm'), Int.toNat_of_nonneg (Int.emod_nonneg _ hm'),
      Nat.mul_succ, pow_add]
    exact cofactor_sim hu hv _

theorem sim_iterate {m K : ℕ} (hm : 1 < m) (y i : ℕ) :
    Sim m K i ((round m K)^[i] (y, 1, m, 0)) ((roundM m K)^[i] (y, 1, m, 0)) := by
  induction i with
  | zero =>
    refine ⟨rfl, rfl, ?_, by simp⟩
    simp only [Function.iterate_zero, id, Nat.mul_zero, pow_zero, Nat.cast_one, mul_one]
    exact (Int.emod_eq_of_lt (by norm_num) (by omega)).symm
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact sim_round (by omega) ih

/-- The cofactors of `roundM` are reduced. -/
theorem roundM_lt {m K : ℕ} (hm : 0 < m) (s : ℕ × ℕ × ℕ × ℕ) :
    (roundM m K s).2.1 < m ∧ (roundM m K s).2.2.2 < m := by
  have hm' : (m : ℤ) ≠ 0 := by omega
  unfold roundM
  dsimp only
  constructor
  · zify
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm')]
    exact Int.emod_lt_of_pos _ (by omega)
  · zify
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm')]
    exact Int.emod_lt_of_pos _ (by omega)

/-- Pornin's modular inversion with the cofactors divided by `2 ^ K` at every round. There
is no final correction. -/
def porninInvM (y m K : ℕ) : ℕ :=
  let s := (roundM m K)^[rounds m K] (y, 1, m, 0)
  if s.2.2.1 = 1 then s.2.2.2 else 0

theorem porninInvM_eq {y m K : ℕ} (hm : 1 < m) : porninInvM y m K = porninInv y m K := by
  obtain ⟨-, hb, -, hv⟩ := sim_iterate (K := K) hm y (rounds m K)
  unfold porninInvM porninInv
  dsimp only
  rw [hb]
  split_ifs
  · have h1 := (powMod_modEq m ((m + 1) / 2) (K * rounds m K)).mul_left
      ((round m K)^[rounds m K] (y, 1, m, 0)).2.2.2
    rw [h1]
    exact_mod_cast hv
  · rfl

end Bingcd.Pornin
