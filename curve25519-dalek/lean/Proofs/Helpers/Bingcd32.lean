module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd.Field32
public import Proofs.Helpers.Bingcd.Packed
public import Proofs.Helpers.FieldElement2625
public import Proofs.Representation.Array
public import Proofs.Representation.FieldElement2625
import Proofs.Helpers.AsNat

/-! # The data of `backend/serial/u32/bingcd.rs` as vectors of words

The functions of `backend/serial/u32/bingcd.rs` are specified like those of the 64-bit backend
(`Proofs/Helpers/Bingcd.lean`): the specs in `Proofs/Backend/Serial/U32/Bingcd/` state that each
translated function computes one of the functions on vectors of words of
`Proofs/Helpers/Bingcd/`, at 32 bits and eight limbs.

This file has the maps through which the arrays and the structures of the Rust code are read:
`L8` for the eight limbs of an operand, `L10` for the ten limbs of a field element, whose value
is `FieldElement2625.asNat`, `Inner.toP` and `Tail.toW` for the states of the inner loop and of
the last steps, and `State.toR` for the state of the algorithm. It also has the lemmas on
machine integers that several of these specs use. -/

@[expose] public section

open Aeneas Aeneas.Std Result
open Bingcd
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-! ### Eight limbs -/

/-- Eight limbs, as a vector of 32-bit words. -/
def L8 (x : Array U32 8#usize) : Limbs 32 8 :=
  #v[(x.val[0]'(by scalar_tac)).bv, (x.val[1]'(by scalar_tac)).bv,
    (x.val[2]'(by scalar_tac)).bv, (x.val[3]'(by scalar_tac)).bv,
    (x.val[4]'(by scalar_tac)).bv, (x.val[5]'(by scalar_tac)).bv,
    (x.val[6]'(by scalar_tac)).bv, (x.val[7]'(by scalar_tac)).bv]

@[simp]
theorem L8_make (r0 r1 r2 r3 r4 r5 r6 r7 : U32) (h) :
    L8 (Array.make 8#usize [r0, r1, r2, r3, r4, r5, r6, r7] h) =
      #v[r0.bv, r1.bv, r2.bv, r3.bv, r4.bv, r5.bv, r6.bv, r7.bv] := rfl

@[simp]
theorem L8_repeat_zero : L8 (Array.repeat 8#usize 0#u32) = #v[0, 0, 0, 0, 0, 0, 0, 0] := rfl

theorem ofNat_eight_zero : (Limbs.ofNat 8 0 : Limbs 32 8) = #v[0, 0, 0, 0, 0, 0, 0, 0] := by
  decide

/-! ### Ten limbs -/

/-- Ten limbs, as a vector of 32-bit words. -/
def L10 (x : Array U32 10#usize) : Limbs 32 10 :=
  #v[(x.val[0]'(by scalar_tac)).bv, (x.val[1]'(by scalar_tac)).bv,
    (x.val[2]'(by scalar_tac)).bv, (x.val[3]'(by scalar_tac)).bv,
    (x.val[4]'(by scalar_tac)).bv, (x.val[5]'(by scalar_tac)).bv,
    (x.val[6]'(by scalar_tac)).bv, (x.val[7]'(by scalar_tac)).bv,
    (x.val[8]'(by scalar_tac)).bv, (x.val[9]'(by scalar_tac)).bv]

/-- The limbs of `L10 x` are those of `x`. -/
theorem toNat_L10_getElem (x : FieldElement2625) (i : ℕ) (hi : i < 10) :
    (L10 x)[i].toNat = x[i]!.val := by
  rw [Array.getElem!_Nat_eq, getElem!_pos x.val i (by scalar_tac)]
  interval_cases i <;> rfl

/-- The value of `L10 x` is `asNat`. -/
theorem value_L10 (x : FieldElement2625) : Limbs.Curve25519.U32.value (L10 x) = x.asNat := by
  rw [Limbs.Curve25519.U32.value, field.FieldElement2625.asNat_expand,
    toNat_L10_getElem x 0 (by norm_num), toNat_L10_getElem x 1 (by norm_num),
    toNat_L10_getElem x 2 (by norm_num), toNat_L10_getElem x 3 (by norm_num),
    toNat_L10_getElem x 4 (by norm_num), toNat_L10_getElem x 5 (by norm_num),
    toNat_L10_getElem x 6 (by norm_num), toNat_L10_getElem x 7 (by norm_num),
    toNat_L10_getElem x 8 (by norm_num), toNat_L10_getElem x 9 (by norm_num)]

/-- Limbs within the bounds of the weak reduction are tight. -/
theorem tight_L10 {x : FieldElement2625}
    (h : ∀ i : ℕ, i < 10 → x[i]!.val < field.FieldElement2625.limbRadix i + i % 2 * 2 ^ 18) :
    Limbs.Curve25519.U32.Tight (L10 x) := by
  intro i hi
  rw [toNat_L10_getElem x i hi]
  exact h i hi

/-! ### States -/

/-- The state of the inner loop, as a state with packed rows. -/
def Inner.toP (s : Inner) : Pornin.InnerP 32 :=
  ⟨s.abar.bv, s.bbar.bv, s.fg0.bv, s.fg1.bv⟩

/-- The state of the last steps, as a state of the inner loop on words. -/
def Tail.toW (s : Tail) : Pornin.InnerW 32 :=
  ⟨s.a.bv, s.b.bv, s.f0.bv, s.g0.bv, s.f1.bv, s.g1.bv⟩

/-- The state of the algorithm, as the quadruple `(a, u, b, v)`: the operands on limbs, the
cofactors in the field. -/
noncomputable def State.toR (s : State) :
    Limbs 32 8 × ZMod curve25519.p × Limbs 32 8 × ZMod curve25519.p :=
  (L8 s.a, s.u.toField, L8 s.b, s.v.toField)

/-! ### Machine integers -/

theorem U64.eq_zero_iff_val (x : U64) : x = 0#u64 ↔ x.val = 0 :=
  ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq h⟩

theorem U32.eq_zero_iff_val (x : U32) : x = 0#u32 ↔ x.val = 0 :=
  ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq h⟩

theorem U32.bv_beq_zero (x : U32) : (UScalar.bv x == 0) = decide (x.val = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    rw [← U32.bv_toNat, U32.bv, h]
    rfl
  · intro h
    exact BitVec.eq_of_toNat_eq (by simpa using h)

theorem U32.decide_eq_zero (x : U32) : decide (x = 0#u32) = (UScalar.bv x == 0) := by
  rw [U32.bv_beq_zero, decide_eq_decide]
  exact U32.eq_zero_iff_val x

/-- The sign bit of a word, as the Rust code reads it. -/
theorem msb_of_shr31 (c i : U32) (hi : i.val = c.val >>> 31) :
    decide (i = 1#u32) = c.bv.msb := by
  have hi' : i.val = c.val / 2 ^ 31 := by rw [hi, Nat.shiftRight_eq_div_pow]
  have hiff : i = 1#u32 ↔ i.val = 1 :=
    ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq h⟩
  have hc : c.val < 2 ^ 32 := by scalar_tac
  rw [BitVec.msb_eq_decide, decide_eq_decide, hiff, hi', U32.bv_toNat]
  omega

end Curve25519Dalek.backend.serial.u32.bingcd
