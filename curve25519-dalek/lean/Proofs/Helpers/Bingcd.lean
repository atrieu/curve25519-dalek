module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd.Field
public import Proofs.Helpers.Bingcd.Packed
public import Proofs.Representation.FieldElement51
import Proofs.Helpers.AsNat
import Proofs.Helpers.Limbs

/-! # The data of `bingcd.rs` as vectors of words

The functions of `bingcd.rs` are specified in two steps. Functions on vectors of words, for any
bitwidth and any number of limbs, are defined and proved correct in the files of
`Proofs/Helpers/Bingcd/`. The specs in `Proofs/Backend/Serial/U64/Bingcd/` then state that each
translated function computes one of them, at 64 bits and four limbs.

This file has the maps through which the arrays and the structures of the Rust code are read:
`L4` for the four limbs of an operand, `L5` for the five limbs of a field element, whose value
in radix `2 ^ 51` is `FieldElement51.asNat`, `Inner.toP` and `Tail.toW` for the states of the
inner loop and of the last steps, and `State.toR` for the state of the algorithm. It also has
the lemmas on machine integers that several of these specs use. -/

@[expose] public section

open Aeneas Aeneas.Std Result
open Bingcd
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-! ### Four limbs -/

/-- Four limbs, as a vector of 64-bit words. -/
def L4 (x : Array U64 4#usize) : Limbs 64 4 :=
  #v[(x.val[0]'(by scalar_tac)).bv, (x.val[1]'(by scalar_tac)).bv,
    (x.val[2]'(by scalar_tac)).bv, (x.val[3]'(by scalar_tac)).bv]

@[simp]
theorem L4_make (r0 r1 r2 r3 : U64) (h) :
    L4 (Array.make 4#usize [r0, r1, r2, r3] h) = #v[r0.bv, r1.bv, r2.bv, r3.bv] := rfl

@[simp]
theorem L4_repeat_zero : L4 (Array.repeat 4#usize 0#u64) = #v[0, 0, 0, 0] := rfl

theorem ofNat_four_zero : (Limbs.ofNat 4 0 : Limbs 64 4) = #v[0, 0, 0, 0] := by decide

/-! ### Five limbs -/

/-- Five limbs, as a vector of 64-bit words. -/
def L5 (x : Array U64 5#usize) : Limbs 64 5 :=
  #v[(x.val[0]'(by scalar_tac)).bv, (x.val[1]'(by scalar_tac)).bv,
    (x.val[2]'(by scalar_tac)).bv, (x.val[3]'(by scalar_tac)).bv,
    (x.val[4]'(by scalar_tac)).bv]

/-- The limbs of `L5 x` are those of `x`. -/
theorem toNat_L5_getElem (x : FieldElement51) (i : ℕ) (hi : i < 5) :
    (L5 x)[i].toNat = x[i]!.val := by
  rw [Array.getElem!_Nat_eq, getElem!_pos x.val i (by scalar_tac)]
  interval_cases i <;> rfl

/-- The value of `L5 x` in radix `2 ^ 51` is `asNat`. -/
theorem value_L5 (x : FieldElement51) : Limbs.Curve25519.value (L5 x) = x.asNat := by
  rw [Limbs.Curve25519.value, Limbs.Curve25519.eval_five, field.FieldElement51.asNat_eq,
    toNat_L5_getElem x 0 (by norm_num), toNat_L5_getElem x 1 (by norm_num),
    toNat_L5_getElem x 2 (by norm_num), toNat_L5_getElem x 3 (by norm_num),
    toNat_L5_getElem x 4 (by norm_num)]
  norm_num

/-- Limbs of at most `2 ^ 51 + 2 ^ 23` are tight. -/
theorem tight_L5 {x : FieldElement51} (h : ∀ i : ℕ, i < 5 → x[i]!.val ≤ 2 ^ 51 + 2 ^ 23) :
    Limbs.Curve25519.Tight (L5 x) := by
  intro i hi
  rw [toNat_L5_getElem x i hi]
  exact h i hi

/-! ### States -/

/-- The state of the inner loop, as a state with packed rows. -/
def Inner.toP (s : Inner) : Pornin.InnerP 64 :=
  ⟨s.abar.bv, s.bbar.bv, s.fg0.bv, s.fg1.bv⟩

/-- The state of the last steps, as a state of the inner loop on words. -/
def Tail.toW (s : Tail) : Pornin.InnerW 64 :=
  ⟨s.a.bv, s.b.bv, s.f0.bv, s.g0.bv, s.f1.bv, s.g1.bv⟩

/-- The state of the algorithm, as the quadruple `(a, u, b, v)`: the operands on limbs, the
cofactors in the field. -/
noncomputable def State.toR (s : State) :
    Limbs 64 4 × ZMod curve25519.p × Limbs 64 4 × ZMod curve25519.p :=
  (L4 s.a, s.u.toField, L4 s.b, s.v.toField)

/-! ### Machine integers -/

theorem U128.eq_zero_iff_val (x : U128) : x = 0#u128 ↔ x.val = 0 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    exact UScalar.eq_of_val_eq h

theorem U64.eq_zero_iff_val (x : U64) : x = 0#u64 ↔ x.val = 0 :=
  ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq h⟩

theorem U64.bv_beq_zero (x : U64) : (UScalar.bv x == 0) = decide (x.val = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    rw [← U64.bv_toNat, U64.bv, h]
    rfl
  · intro h
    exact BitVec.eq_of_toNat_eq (by simpa using h)

theorem U64.decide_eq_zero (x : U64) : decide (x = 0#u64) = (UScalar.bv x == 0) := by
  rw [U64.bv_beq_zero, decide_eq_decide]
  exact U64.eq_zero_iff_val x

/-- The sign bit of a word, as the Rust code reads it. -/
theorem msb_of_shr63 (c i : U64) (hi : i.val = c.val >>> 63) :
    decide (i = 1#u64) = c.bv.msb := by
  have hi' : i.val = c.val / 2 ^ 63 := by rw [hi, Nat.shiftRight_eq_div_pow]
  have hiff : i = 1#u64 ↔ i.val = 1 :=
    ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq h⟩
  have hc : c.val < 2 ^ 64 := by scalar_tac
  rw [BitVec.msb_eq_decide, decide_eq_decide, hiff, hi', U64.bv_toNat]
  omega

end Curve25519Dalek.backend.serial.u64.bingcd
