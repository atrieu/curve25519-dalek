module
public import Proofs.Helpers.Bingcd.BitReduction
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Init
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.ZMod.Basic

/-! # Pornin's optimized binary gcd: modular inversion

Modular inversion modulo an odd `m` by Pornin's algorithm (*Optimized Binary GCD for Modular
Inversion*, 2020), following Listing 2 of Mahboubi, Melquiond, Strub and Vallejos Parada,
*Functional Correctness of an Optimized Modular Inversion Algorithm* (ITP 2026).

Each round approximates `a` and `b` by their top `K + 2` and bottom `K` bits, runs `K` steps
of the extended binary gcd on the approximations to build a transition matrix, then applies
the matrix to `a`, `b` and to the cofactors `u`, `v`. The matrix is `2 ^ K` times the true
one, so the cofactors pick up a factor `2 ^ K` per round, removed at the end.
`⌈(2 * ℓ(m) - 1) / K⌉` rounds suffice.

The parameter `K` is the number of inner steps; it is `k - 1` in the papers. -/

@[expose] public section

/-! ## Binary exponentiation

Left-to-right binary exponentiation, for an arbitrary multiplication: the final correction
of the algorithm is a power of `(m + 1) / 2`, the inverse of `2` modulo `m`.

`powBin mul one x e` is defined by recursion on the exponent: the result for `e` is the
square of the result for `e / 2`, multiplied by `x` when `e` is odd. -/

namespace Bingcd

variable {α M : Type*}

/-- Left-to-right binary exponentiation: `x ^ e`, with one squaring per bit of `e` and one
multiplication per nonzero bit. -/
def powBin (mul : α → α → α) (one x : α) (e : ℕ) : α :=
  if e = 0 then one
  else
    let h := powBin mul one x (e / 2)
    let s := mul h h
    if e % 2 = 1 then mul s x else s
termination_by e
decreasing_by omega

/-- Binary exponentiation through a representation. Let `φ` map `α` to a monoid, and let `P`
be an invariant preserved by `mul`, on which `φ` is multiplicative. Then binary
exponentiation in `α` computes the power in the monoid, and preserves the invariant. -/
theorem powBin_spec [Monoid M] {mul : α → α → α} {one x : α} (φ : α → M) (P : α → Prop)
    (hmul : ∀ a b, P a → P b → P (mul a b) ∧ φ (mul a b) = φ a * φ b) (hone : P one)
    (hφone : φ one = 1) (hx : P x) (e : ℕ) :
    P (powBin mul one x e) ∧ φ (powBin mul one x e) = φ x ^ e := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    rw [powBin]
    split
    · next h => exact ⟨hone, by rw [hφone, h, pow_zero]⟩
    · next h =>
      obtain ⟨hP, hφ⟩ := ih (e / 2) (by omega)
      obtain ⟨hP₂, hφ₂⟩ := hmul _ _ hP hP
      have he := Nat.div_add_mod e 2
      simp only
      split
      · next hodd =>
        obtain ⟨hP₃, hφ₃⟩ := hmul _ _ hP₂ hx
        refine ⟨hP₃, ?_⟩
        rw [hφ₃, hφ₂, hφ, ← pow_add, ← pow_succ]
        congr 1
        omega
      · next heven =>
        refine ⟨hP₂, ?_⟩
        rw [hφ₂, hφ, ← pow_add]
        congr 1
        omega

/-- `b ^ e` modulo `m`, by binary exponentiation with a reduction after every product. -/
def powMod (m b e : ℕ) : ℕ := powBin (fun x y => x * y % m) (1 % m) (b % m) e

theorem powMod_modEq (m b e : ℕ) : powMod m b e ≡ b ^ e [MOD m] := by
  have h := (powBin_spec (mul := fun x y => x * y % m) (one := 1 % m) (x := b % m)
    (fun a : ℕ => (a : ZMod m)) (fun _ => True)
    (fun a b _ _ => ⟨trivial, by simp⟩) trivial (by simp) trivial e).2
  rw [← ZMod.natCast_eq_natCast_iff]
  simpa [powMod] using h

end Bingcd

namespace Bingcd.Pornin

/-! ### Approximations -/

/-- The approximation of `a`: the bits of `a` from position `p` upwards, followed by the `K`
low bits of `a`. -/
def approx (K p a : ℕ) : ℕ := 2 ^ K * (a / 2 ^ p) + a % 2 ^ K

theorem approx_self (K a : ℕ) : approx K K a = a := Nat.div_add_mod a (2 ^ K)

theorem approx_dvd (K p a : ℕ) : (2 : ℤ) ^ K ∣ (a : ℤ) - approx K p a := by
  have h : (a : ℤ) = 2 ^ K * (a / 2 ^ K : ℕ) + (a % 2 ^ K : ℕ) := by
    exact_mod_cast (Nat.div_add_mod a (2 ^ K)).symm
  refine ⟨(a / 2 ^ K : ℕ) - (a / 2 ^ p : ℕ), ?_⟩
  unfold approx
  push_cast at h ⊢
  linear_combination h

theorem approx_mod_two {K : ℕ} (hK : 1 ≤ K) (p a : ℕ) : approx K p a % 2 = a % 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, K = j + 1 := ⟨K - 1, by omega⟩
  have h := Nat.div_add_mod a (2 ^ (j + 1))
  unfold approx
  rw [pow_succ] at h ⊢
  generalize a / (2 ^ j * 2) = q₁ at *
  generalize a / 2 ^ p = q₂ at *
  generalize a % (2 ^ j * 2) = r at *
  have e1 : 2 ^ j * 2 * q₁ = 2 * (2 ^ j * q₁) := by ring
  have e2 : 2 ^ j * 2 * q₂ = 2 * (2 ^ j * q₂) := by ring
  omega

/-- The approximation, scaled back, is within `2 ^ p` of the operand. -/
theorem approx_err {K p : ℕ} (hKp : K ≤ p) (a : ℕ) :
    -(2 : ℤ) ^ p ≤ a - 2 ^ (p - K) * approx K p a ∧
      (a : ℤ) - 2 ^ (p - K) * approx K p a ≤ 2 ^ p := by
  have h : (a : ℤ) = 2 ^ p * (a / 2 ^ p : ℕ) + (a % 2 ^ p : ℕ) := by
    exact_mod_cast (Nat.div_add_mod a (2 ^ p)).symm
  have hr1 : ((a % 2 ^ p : ℕ) : ℤ) < 2 ^ p := by
    exact_mod_cast Nat.mod_lt a (by positivity)
  have hr2 : ((a % 2 ^ K : ℕ) : ℤ) < 2 ^ K := by
    exact_mod_cast Nat.mod_lt a (by positivity)
  have hpow : (2 : ℤ) ^ (p - K) * 2 ^ K = 2 ^ p := by rw [← pow_add]; congr 1; omega
  have he : (0 : ℤ) < 2 ^ (p - K) := by positivity
  have hmul : (2 : ℤ) ^ (p - K) * (a % 2 ^ K : ℕ) < 2 ^ p := by
    rw [← hpow]
    exact mul_lt_mul_of_pos_left hr2 he
  have h0 : (0 : ℤ) ≤ 2 ^ (p - K) * (a % 2 ^ K : ℕ) := by positivity
  have h1 : (0 : ℤ) ≤ (a % 2 ^ p : ℕ) := by positivity
  have key : (a : ℤ) - 2 ^ (p - K) * approx K p a =
      (a % 2 ^ p : ℕ) - 2 ^ (p - K) * (a % 2 ^ K : ℕ) := by
    unfold approx
    push_cast at h ⊢
    linear_combination h - (a / 2 ^ p : ℤ) * hpow
  rw [key]
  constructor <;> linarith

theorem approx_ge {K p a : ℕ} (h : 2 ^ (p + K + 1) ≤ a) : 2 ^ (2 * K + 1) ≤ approx K p a := by
  have hq : 2 ^ (K + 1) ≤ a / 2 ^ p := by
    rw [Nat.le_div_iff_mul_le (by positivity), ← pow_add]
    exact le_trans (le_of_eq (by congr 1; omega)) h
  calc 2 ^ (2 * K + 1) = 2 ^ K * 2 ^ (K + 1) := by rw [← pow_add]; congr 1; omega
    _ ≤ 2 ^ K * (a / 2 ^ p) := Nat.mul_le_mul_left _ hq
    _ ≤ approx K p a := Nat.le_add_right _ _

theorem approx_lt {K p a : ℕ} (h : a < 2 ^ (p + 1)) : approx K p a < 2 ^ (K + 1) := by
  have hq : a / 2 ^ p < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [pow_succ, mul_comm] at h
    exact h
  have hr := Nat.mod_lt a (by positivity : 0 < 2 ^ K)
  have : 2 ^ K * (a / 2 ^ p) ≤ 2 ^ K * 1 := Nat.mul_le_mul_left _ (by omega)
  unfold approx
  rw [pow_succ]
  omega

theorem len_natCast (a : ℕ) : len (a : ℤ) = a.size := rfl

/-! ### One round removes `K` bits -/

/-- The start of the ghost run satisfies the structural invariant. -/
theorem base_zero {K p : ℕ} (hK : 1 ≤ K) (hKp : K ≤ p) (a : ℕ) {b : ℕ} (hb : b % 2 = 1) :
    Base K p a b 0 (((a : ℤ), (b : ℤ)), ⟨approx K p a, approx K p b, 1, 0, 0, 1⟩) := by
  have hbb := approx_mod_two hK p b
  refine ⟨approx_dvd K p a, approx_dvd K p b, by dsimp only; omega, by dsimp only; omega,
    (approx_err hKp a).1, (approx_err hKp a).2, (approx_err hKp b).1, (approx_err hKp b).2,
    by simp, by simp⟩

/-- **Bit reduction of one round** (Theorem 20): after `K` inner steps decided on the
approximations, the true value `A` is `0` or `ℓ(A) + ℓ(B) + K ≤ ℓ(a) + ℓ(b)`. -/
theorem bitReduction {K : ℕ} (hK : 1 ≤ K) (a : ℕ) {b : ℕ} (hb : b % 2 = 1) {p : ℕ}
    (hp : p = max (max a.size b.size) (2 * K + 2) - K - 2) :
    (gstep^[K] (((a : ℤ), (b : ℤ)), ⟨approx K p a, approx K p b, 1, 0, 0, 1⟩)).1.1 = 0 ∨
      len (gstep^[K] (((a : ℤ), (b : ℤ)), ⟨approx K p a, approx K p b, 1, 0, 0, 1⟩)).1.1 +
        len (gstep^[K] (((a : ℤ), (b : ℤ)), ⟨approx K p a, approx K p b, 1, 0, 0, 1⟩)).1.2 +
          K ≤ a.size + b.size := by
  have hKp : K ≤ p := by omega
  have hbase := base_zero hK hKp a hb
  have ha0 : (0 : ℤ) ≤ a := by positivity
  have hb0 : (0 : ℤ) < b := by omega
  have hy0 : (0 : ℤ) < approx K p b := by have := approx_mod_two hK p b; omega
  rw [← len_natCast a, ← len_natCast b]
  by_cases hsmall : max a.size b.size ≤ 2 * K + 2
  · -- the approximations are exact
    obtain rfl : p = K := by omega
    simp only [approx_self] at hbase ⊢
    exact bitReduction_exact ha0 hb0 hbase
  · have hn : p + K + 2 = max a.size b.size := by omega
    by_cases hclose : 2 * p + 4 + K ≤ a.size + b.size
    · refine bitReduction_close ha0 hb0 hclose ?_ hbase
      have hmin : len (min (a : ℤ) (b : ℤ)) = min a.size b.size := by
        rcases le_total a b with h | h
        · rw [min_eq_left (by exact_mod_cast h), len_natCast, min_eq_left (Nat.size_le_size h)]
        · rw [min_eq_right (by exact_mod_cast h), len_natCast,
            min_eq_right (Nat.size_le_size h)]
      rw [hmin, len_natCast, len_natCast]
      omega
    · by_cases hab : b.size ≤ a.size
      · -- `a` dominates
        have ha1 : 2 ^ (p + K + 1) ≤ a := Nat.lt_size.mp (by omega)
        have hb1 : b < 2 ^ (p + 1) := Nat.size_le.mp (by omega)
        have hx := approx_ge ha1
        have hy := approx_lt (K := K) hb1
        have e1 : 2 ^ (p + K + 1) = 2 ^ K * 2 ^ (p + 1) := by rw [← pow_add]; congr 1; omega
        have e2 : 2 ^ (2 * K + 1) = 2 ^ K * 2 ^ (K + 1) := by rw [← pow_add]; congr 1; omega
        have h1 : 2 ^ K * b < a + b :=
          lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hb1 (by positivity)) (by omega)
        have h2 : 2 ^ K * approx K p b < approx K p a + approx K p b :=
          lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hy (by positivity)) (by omega)
        exact Or.inr (bitReduction_distA hb0 hy0 (by exact_mod_cast h1) (by exact_mod_cast h2)
          hbase)
      · -- `b` dominates
        have hb1 : 2 ^ (p + K + 1) ≤ b := Nat.lt_size.mp (by omega)
        have ha1 : a < 2 ^ (p + 1) := Nat.size_le.mp (by omega)
        have hy := approx_ge hb1
        have hx := approx_lt (K := K) ha1
        have e1 : 2 ^ (p + K + 1) = 2 ^ K * 2 ^ (p + 1) := by rw [← pow_add]; congr 1; omega
        have e2 : 2 ^ (2 * K + 1) = 2 ^ K * 2 ^ (K + 1) := by rw [← pow_add]; congr 1; omega
        have h1 : 2 ^ K * a < b :=
          lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left ha1 (by positivity)) (by omega)
        have h2 : 2 ^ K * approx K p a < approx K p b :=
          lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hx (by positivity)) (by omega)
        exact bitReduction_distB ha0 (by positivity) (by exact_mod_cast h1)
          (by exact_mod_cast h2) hbase

/-! ### The ghost run preserves the gcd, and stays at zero -/

theorem gcd_iterate {K p : ℕ} {a b : ℤ} {s₀ : (ℤ × ℤ) × Inner} (hbase : Base K p a b 0 s₀) :
    Int.gcd (gstep^[K] s₀).1.1 (gstep^[K] s₀).1.2 = Int.gcd s₀.1.1 s₀.1.2 := by
  refine phase_iterate hbase (fun _ s => Int.gcd s.1.1 s.1.2 = Int.gcd s₀.1.1 s₀.1.2) rfl ?_
  intro t s ht hB h
  have hpar := hB.parity ht
  obtain ⟨⟨A, B⟩, ⟨x, y, f0, g0, f1, g1⟩⟩ := s
  obtain ⟨-, -, hy, hBo, -⟩ := hB
  dsimp only at hpar hy hBo h ⊢
  rw [← h]
  obtain ⟨A', x', hs | hs | hs⟩ := gstep_spec f0 g0 f1 g1 hpar hBo hy
  · obtain ⟨-, rfl, heq⟩ := hs
    rw [heq]
    dsimp only
    have := gcd_half hBo (b := 2 * A') (by omega)
    rw [Int.mul_ediv_cancel_left _ two_ne_zero] at this
    rw [Int.gcd_comm, this, Int.gcd_comm]
  · obtain ⟨hx1, -, -, hA, heq⟩ := hs
    rw [heq]
    dsimp only
    have := gcd_half (a := A) (b := 2 * A') (by omega) (by omega)
    rw [Int.mul_ediv_cancel_left _ two_ne_zero] at this
    rw [Int.gcd_comm, this, ← hA, Int.gcd_sub_self_right]
  · obtain ⟨-, -, -, hA, heq⟩ := hs
    rw [heq]
    dsimp only
    have := gcd_half hBo (b := 2 * A') (by omega)
    rw [Int.mul_ediv_cancel_left _ two_ne_zero] at this
    rw [Int.gcd_comm, this, ← hA, Int.gcd_sub_self_right, Int.gcd_comm]

theorem zero_iterate {K p : ℕ} {a b : ℤ} {s₀ : (ℤ × ℤ) × Inner} (hbase : Base K p a b 0 s₀)
    (h0 : s₀.1.1 = 0) : (gstep^[K] s₀).1.1 = 0 := by
  refine phase_iterate hbase (fun _ s => s.1.1 = 0) h0 ?_
  intro t s ht hB h
  have hpar := hB.parity ht
  obtain ⟨⟨A, B⟩, ⟨x, y, f0, g0, f1, g1⟩⟩ := s
  obtain ⟨-, -, hy, hBo, -⟩ := hB
  dsimp only at hpar hy hBo h ⊢
  obtain ⟨A', x', hs | hs | hs⟩ := gstep_spec f0 g0 f1 g1 hpar hBo hy
  · obtain ⟨-, hA, heq⟩ := hs
    rw [heq]
    dsimp only
    omega
  · omega
  · omega

/-! ### One round -/

/-- One round on `(a, u, b, v)`: `K` inner steps on the approximations, then the transition
matrix is applied to `a`, `b` (with an exact division by `2 ^ K`) and to `u`, `v` modulo
`m`, with signs fixed so that `a` and `b` stay nonnegative. -/
def round (m K : ℕ) (s : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let p := max (max s.1.size s.2.2.1.size) (2 * K + 2) - K - 2
  let t := Inner.step^[K] ⟨approx K p s.1, approx K p s.2.2.1, 1, 0, 0, 1⟩
  let a' : ℤ := (s.1 * t.f0 + s.2.2.1 * t.g0) / 2 ^ K
  let b' : ℤ := (s.1 * t.f1 + s.2.2.1 * t.g1) / 2 ^ K
  let u' : ℤ := s.2.1 * t.f0 + s.2.2.2 * t.g0
  let v' : ℤ := s.2.1 * t.f1 + s.2.2.2 * t.g1
  (a'.natAbs, ((if a' < 0 then -u' else u') % m).toNat,
    b'.natAbs, ((if b' < 0 then -v' else v') % m).toNat)

/-- The invariant after `i` rounds from `(y, 1, m, 0)`. The cofactors carry a factor
`2 ^ (K * i)`. -/
def RInv (y m K i : ℕ) (s : ℕ × ℕ × ℕ × ℕ) : Prop :=
  s.2.2.1 % 2 = 1 ∧ Nat.gcd s.1 s.2.2.1 = Nat.gcd y m ∧ s.2.1 < m ∧ s.2.2.2 < m ∧
    (s.2.1 : ℤ) * y ≡ 2 ^ (K * i) * s.1 [ZMOD m] ∧
    (s.2.2.2 : ℤ) * y ≡ 2 ^ (K * i) * s.2.2.1 [ZMOD m] ∧
    (s.1 = 0 ∨ s.1.size + s.2.2.1.size + K * i ≤ y.size + m.size)

/-- The cofactor update of a round, for either sign. -/
theorem cofactor_modEq {m y u v a b f g A c P : ℤ} (hu : u * y ≡ c * a [ZMOD m])
    (hv : v * y ≡ c * b [ZMOD m]) (hA : P * A = a * f + b * g) (σ : ℤ) :
    σ * (u * f + v * g) % m * y ≡ c * P * (σ * A) [ZMOD m] := by
  calc σ * (u * f + v * g) % m * y ≡ σ * (u * f + v * g) * y [ZMOD m] :=
        (Int.mod_modEq _ _).mul_right _
    _ = σ * (u * y * f + v * y * g) := by ring
    _ ≡ σ * (c * a * f + c * b * g) [ZMOD m] :=
        ((hu.mul_right f).add (hv.mul_right g)).mul_left σ
    _ = c * P * (σ * A) := by linear_combination (-(σ * c)) * hA

theorem rinv_round {y m K i : ℕ} (hK : 1 ≤ K) (hm : 0 < m) {s : ℕ × ℕ × ℕ × ℕ}
    (hs : RInv y m K i s) : RInv y m K (i + 1) (round m K s) := by
  obtain ⟨a, u, b, v⟩ := s
  obtain ⟨hb, hg, hu, hv, hau, hbv, hpot⟩ := hs
  dsimp only at hb hg hu hv hau hbv hpot
  obtain ⟨p, hp⟩ : ∃ p, p = max (max a.size b.size) (2 * K + 2) - K - 2 := ⟨_, rfl⟩
  have hbase := base_zero hK (by omega : K ≤ p) a hb
  have hred := bitReduction hK a hb hp
  have hgcd := gcd_iterate hbase
  have hzero := zero_iterate hbase
  have hfin := base_iterate hbase (le_refl K)
  have hsnd := gstep_iterate_snd K
    (((a : ℤ), (b : ℤ)), (⟨approx K p a, approx K p b, 1, 0, 0, 1⟩ : Inner))
  dsimp only at hsnd hgcd hzero
  unfold round
  dsimp only
  rw [← hp, ← hsnd]
  generalize gstep^[K] (((a : ℤ), (b : ℤ)), ⟨approx K p a, approx K p b, 1, 0, 0, 1⟩) = G at *
  obtain ⟨⟨A, B⟩, ⟨x, y', f0, g0, f1, g1⟩⟩ := G
  obtain ⟨-, -, -, hBo, -, -, -, -, hl1, hl2⟩ := hfin
  dsimp only at hred hgcd hzero hBo hl1 hl2 ⊢
  have h2K : (2 : ℤ) ^ K ≠ 0 := by positivity
  rw [← hl1, ← hl2, Int.mul_ediv_cancel_left _ h2K, Int.mul_ediv_cancel_left _ h2K]
  have hm' : (m : ℤ) ≠ 0 := by omega
  have hpow : (2 : ℤ) ^ (K * (i + 1)) = 2 ^ (K * i) * 2 ^ K := by rw [← pow_add]; ring_nf
  unfold RInv
  dsimp only
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hg, ← Int.gcd_natCast_natCast a b, ← hgcd]
    rfl
  · have := Int.emod_lt_of_pos (if A < 0 then -((u : ℤ) * f0 + v * g0) else u * f0 + v * g0)
      (by omega : (0 : ℤ) < m)
    have := Int.emod_nonneg (if A < 0 then -((u : ℤ) * f0 + v * g0) else u * f0 + v * g0) hm'
    omega
  · have := Int.emod_lt_of_pos (if B < 0 then -((u : ℤ) * f1 + v * g1) else u * f1 + v * g1)
      (by omega : (0 : ℤ) < m)
    have := Int.emod_nonneg (if B < 0 then -((u : ℤ) * f1 + v * g1) else u * f1 + v * g1) hm'
    omega
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm'), hpow]
    split_ifs with hneg
    · have := cofactor_modEq hau hbv hl1 (-1)
      rw [show ((A.natAbs : ℕ) : ℤ) = -1 * A by omega]
      simpa using this
    · have := cofactor_modEq hau hbv hl1 1
      rw [show ((A.natAbs : ℕ) : ℤ) = 1 * A by omega]
      simpa using this
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm'), hpow]
    split_ifs with hneg
    · have := cofactor_modEq hau hbv hl2 (-1)
      rw [show ((B.natAbs : ℕ) : ℤ) = -1 * B by omega]
      simpa using this
    · have := cofactor_modEq hau hbv hl2 1
      rw [show ((B.natAbs : ℕ) : ℤ) = 1 * B by omega]
      simpa using this
  · rcases hpot with ha0 | hpot
    · exact Or.inl (by have := hzero (by exact_mod_cast ha0); omega)
    · rcases hred with hA0 | hred
      · exact Or.inl (by omega)
      · unfold len at hred
        have : K * (i + 1) = K * i + K := by ring
        exact Or.inr (by omega)

theorem rinv_iterate {y m K : ℕ} (hK : 1 ≤ K) (hm1 : 1 < m) (hm : m % 2 = 1) (i : ℕ) :
    RInv y m K i ((round m K)^[i] (y, 1, m, 0)) := by
  induction i with
  | zero =>
    refine ⟨hm, rfl, hm1, (by omega : 0 < m), by simp, ?_, Or.inr (by simp)⟩
    simpa using (Int.modEq_zero_iff_dvd.mpr (dvd_refl (m : ℤ))).symm
  | succ i ih => rw [Function.iterate_succ_apply']; exact rinv_round hK (by omega) ih

/-! ### Modular inversion -/

/-- The number of rounds: `⌈(2 * ℓ(m) - 1) / K⌉`. -/
def rounds (m K : ℕ) : ℕ := (2 * m.size - 1 + (K - 1)) / K

theorem le_mul_rounds {K : ℕ} (hK : 1 ≤ K) (m : ℕ) : 2 * m.size - 1 ≤ K * rounds m K := by
  have h1 := Nat.div_add_mod (2 * m.size - 1 + (K - 1)) K
  have h2 := Nat.mod_lt (2 * m.size - 1 + (K - 1)) (by omega : 0 < K)
  unfold rounds
  generalize K * ((2 * m.size - 1 + (K - 1)) / K) = X at *
  omega

/-- After all rounds, `a = 0` and `b` is the gcd. -/
theorem round_iterate {y m K : ℕ} (hK : 1 ≤ K) (hm1 : 1 < m) (hm : m % 2 = 1) (hy : y < m) :
    ((round m K)^[rounds m K] (y, 1, m, 0)).1 = 0 ∧
      ((round m K)^[rounds m K] (y, 1, m, 0)).2.2.1 = Nat.gcd y m := by
  obtain ⟨hb, hg, -, -, -, -, hpot⟩ := rinv_iterate (y := y) hK hm1 hm (rounds m K)
  have hr := le_mul_rounds hK m
  generalize (round m K)^[rounds m K] (y, 1, m, 0) = s at *
  obtain ⟨a, u, b, v⟩ := s
  dsimp only at hb hg hpot ⊢
  have ha : a = 0 := by
    rcases hpot with h | h
    · exact h
    · have h1 := Nat.size_le_size hy.le
      have h2 := Nat.size_pos.mpr (by omega : 0 < b)
      have h3 := Nat.size_pos.mpr (by omega : 0 < m)
      exact Nat.size_eq_zero.mp (by omega)
  subst ha
  exact ⟨rfl, by simpa using hg⟩

/-- The inverse of `y` modulo an odd `m` by Pornin's algorithm with `K` inner steps per
round. It is `0` when `y` is not invertible. -/
def porninInv (y m K : ℕ) : ℕ :=
  let s := (round m K)^[rounds m K] (y, 1, m, 0)
  if s.2.2.1 = 1 then
    s.2.2.2 * powMod m ((m + 1) / 2) (K * rounds m K) % m
  else 0

/-- The final correction: modulo an odd `m`, if `v * y ≡ 2 ^ N` then `v * ((m + 1) / 2) ^ N`
is an inverse of `y`. -/
theorem mul_half_pow_modEq {m v y N : ℕ} (hodd : m % 2 = 1) (h : v * y ≡ 2 ^ N [MOD m]) :
    y * (v * powMod m ((m + 1) / 2) N % m) ≡ 1 [MOD m] := by
  have h2 : 2 * ((m + 1) / 2) = m + 1 := by omega
  calc y * (v * powMod m ((m + 1) / 2) N % m)
      ≡ y * (v * powMod m ((m + 1) / 2) N) [MOD m] := (Nat.mod_modEq _ _).mul_left _
    _ ≡ y * (v * ((m + 1) / 2) ^ N) [MOD m] := ((powMod_modEq _ _ _).mul_left _).mul_left _
    _ = v * y * ((m + 1) / 2) ^ N := by ring
    _ ≡ 2 ^ N * ((m + 1) / 2) ^ N [MOD m] := h.mul_right _
    _ = (m + 1) ^ N := by rw [← mul_pow, h2]
    _ ≡ 1 [MOD m] := by
        have h1 : m + 1 ≡ 1 [MOD m] := by simp [Nat.ModEq]
        simpa using h1.pow N

/-- **Correctness of Pornin's modular inversion.** For `K ≥ 1`, `m > 1` odd and `y < m`
coprime to `m`, `porninInv y m K` is the inverse of `y` modulo `m`, in `[0, m)`. -/
theorem porninInv_spec {y m K : ℕ} (hK : 1 ≤ K) (hm : 1 < m) (hodd : m % 2 = 1) (hy : y < m)
    (hc : Nat.Coprime y m) : porninInv y m K < m ∧ y * porninInv y m K % m = 1 := by
  obtain ⟨-, hb⟩ := round_iterate hK hm hodd hy
  obtain ⟨-, -, -, -, -, hbv, -⟩ := rinv_iterate (y := y) hK hm hodd (rounds m K)
  rw [hc] at hb
  simp only [porninInv, hb, ite_true]
  rw [hb] at hbv
  generalize ((round m K)^[rounds m K] (y, 1, m, 0)).2.2.2 = v at *
  generalize K * rounds m K = N at *
  refine ⟨Nat.mod_lt _ (by omega), ?_⟩
  have hbv' : v * y ≡ 2 ^ N [MOD m] := Int.natCast_modEq_iff.mp (by simpa using hbv)
  rw [mul_half_pow_modEq hodd hbv', Nat.mod_eq_of_lt hm]

/-- When `y` is not invertible modulo `m`, the result is `0`. -/
theorem porninInv_eq_zero {y m K : ℕ} (hK : 1 ≤ K) (hm : 1 < m) (hodd : m % 2 = 1) (hy : y < m)
    (hc : Nat.gcd y m ≠ 1) : porninInv y m K = 0 := by
  obtain ⟨-, hb⟩ := round_iterate hK hm hodd hy
  simp [porninInv, hb, hc]

theorem porninInv_lt {y m K : ℕ} (hK : 1 ≤ K) (hm : 1 < m) (hodd : m % 2 = 1) (hy : y < m) :
    porninInv y m K < m := by
  by_cases hc : Nat.gcd y m = 1
  · exact (porninInv_spec hK hm hodd hy hc).1
  · rw [porninInv_eq_zero hK hm hodd hy hc]
    omega

/-- Modulo an odd prime `p`, `porninInv` computes the inverse in `ZMod p`, with the usual
convention that the inverse of `0` is `0`. -/
theorem natCast_porninInv {y p K : ℕ} [hp : Fact p.Prime] (hK : 1 ≤ K) (hodd : p % 2 = 1)
    (hy : y < p) : ((porninInv y p K : ℕ) : ZMod p) = (y : ZMod p)⁻¹ := by
  have hp1 := hp.out.one_lt
  by_cases hy0 : y = 0
  · subst hy0
    rw [porninInv_eq_zero hK hp1 hodd hy (by rw [Nat.gcd_zero_left]; omega)]
    simp
  · have hc : Nat.Coprime y p :=
      ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h =>
        absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hy0) h) (by omega)).symm
    have h := (porninInv_spec hK hp1 hodd hy hc).2
    have hmul : (y : ZMod p) * ((porninInv y p K : ℕ) : ZMod p) = 1 := by
      rw [← Nat.cast_mul, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', h,
        Nat.mod_eq_of_lt hp1]
    exact eq_inv_of_mul_eq_one_right hmul

end Bingcd.Pornin
