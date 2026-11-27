module
public import Proofs.Helpers.Bingcd.OnLimbs

/-! # Pornin's inner loop with packed rows

During the `K` steps of the inner loop the entries of the transition matrix stay in
`(-2 ^ K, 2 ^ K]` (`entry_range_iterate`). A row `(f, g)` then fits in one word of
`2 * K + 2` bits, as `f + 2 ^ (K + 1) * g` modulo `2 ^ w`. The packing is linear, so swapping,
subtracting and doubling packed rows acts on both entries at once: a step updates two words
of the matrix instead of four. This is how implementations run the inner loop.

The step on packed rows is written the way implementations write it, with the two decisions
of a step as masks rather than selections. It is the step of `InnerW` on the packed state for
every word size and every `K`; only unpacking at the end needs words of `2 * K + 2` bits and
the bound on the entries. -/

@[expose] public section

namespace Bingcd.Pornin

/-! ### Packed rows -/

/-- A row `(f, g)` of the transition matrix in one word: `f + 2 ^ (K + 1) * g` modulo
`2 ^ w`. -/
def pack {w : ℕ} (K : ℕ) (f g : Word w) : Word w := f + g <<< (K + 1)

theorem pack_add {w : ℕ} (K : ℕ) (f g f' g' : Word w) :
    pack K f g + pack K f' g' = pack K (f + f') (g + g') := by
  simp only [pack, BitVec.shiftLeft_eq_mul_twoPow]
  ring

theorem pack_sub {w : ℕ} (K : ℕ) (f g f' g' : Word w) :
    pack K f g - pack K f' g' = pack K (f - f') (g - g') := by
  simp only [pack, BitVec.shiftLeft_eq_mul_twoPow]
  ring

theorem pack_shiftLeft_one {w : ℕ} (K : ℕ) (f g : Word w) :
    pack K f g <<< 1 = pack K (f + f) (g + g) := by
  rw [Word.shiftLeft_one, pack_add]

/-! ### The inner loop on packed rows -/

/-- The state of the inner loop with packed rows. -/
structure InnerP (w : ℕ) where
  /-- The approximation of `a`. -/
  abar : Word w
  /-- The approximation of `b`. -/
  bbar : Word w
  /-- The first row of the transition matrix, packed. -/
  fg0 : Word w
  /-- The second row of the transition matrix, packed. -/
  fg1 : Word w

/-- One step on packed rows, with the two decisions as masks. `aodd` is all ones when `ā` is
odd, and `swap` when moreover `ā < b̄`. The operands and the rows are swapped by xoring a
masked difference into both, the second operand and row are subtracted from the first under
`aodd`, then `ā` is halved and the second row doubled. -/
def InnerP.step {w : ℕ} (s : InnerP w) : InnerP w :=
  let aodd : Word w := 0 - (s.abar &&& 1)
  let swap := aodd &&& Word.mask w (Word.subb s.abar s.bbar false).2
  let t1 := swap &&& (s.abar ^^^ s.bbar)
  let xa := s.abar ^^^ t1
  let xb := s.bbar ^^^ t1
  let t2 := swap &&& (s.fg0 ^^^ s.fg1)
  let r0 := s.fg0 ^^^ t2
  let r1 := s.fg1 ^^^ t2
  ⟨(xa - (aodd &&& xb)) >>> 1, xb, r0 - (aodd &&& r1), r1 <<< 1⟩

/-- The packed form of a state of the inner loop on words. -/
def InnerP.ofW {w : ℕ} (K : ℕ) (s : InnerW w) : InnerP w :=
  ⟨s.abar, s.bbar, pack K s.f0 s.g0, pack K s.f1 s.g1⟩

/-- **A step on packed rows is the step on words**, for every word size and every `K`. -/
theorem InnerP.ofW_step {w : ℕ} (K : ℕ) (s : InnerW w) :
    (InnerP.ofW K s).step = InnerP.ofW K s.step := by
  obtain ⟨a, b, f0, g0, f1, g1⟩ := s
  simp only [InnerP.ofW, InnerP.step, InnerW.step, Word.zero_sub_and_one]
  generalize decide (a.toNat % 2 = 1) = odd
  generalize (Word.subb a b false).2 = lt
  cases odd <;> cases lt <;>
    simp [Word.mask_true_and, Word.mask_false_and, Word.xor_xor_cancel_left,
      Word.xor_xor_cancel_right, pack_sub, pack_shiftLeft_one]

theorem InnerP.ofW_iterate {w : ℕ} (K : ℕ) (s : InnerW w) (t : ℕ) :
    InnerP.step^[t] (InnerP.ofW K s) = InnerP.ofW K (InnerW.step^[t] s) := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ofW_step, ih]

/-! ### Unpacking -/

/-- The word `2 ^ K - 1`. Added to an entry in `(-2 ^ K, 2 ^ K]`, it gives a value in
`[0, 2 ^ (K + 1))`. -/
def bias (w K : ℕ) : Word w := BitVec.ofNat w (2 ^ K - 1)

/-- The two entries of a packed row: `2 ^ K - 1` is added to both halves, which makes them
nonnegative, the word is split, and `2 ^ K - 1` is subtracted from each half. -/
def unpack {w : ℕ} (K : ℕ) (fg : Word w) : Word w × Word w :=
  let t := fg + pack K (bias w K) (bias w K)
  ((t &&& BitVec.ofNat w (2 ^ (K + 1) - 1)) - bias w K, (t >>> (K + 1)) - bias w K)

/-- An entry in `(-2 ^ K, 2 ^ K]`, once `2 ^ K - 1` is added, fits in `K + 1` bits. -/
theorem toNat_add_bias_lt {w K : ℕ} (hw : K + 2 ≤ w) {x : Word w}
    (h : -2 ^ K < x.toInt ∧ x.toInt ≤ 2 ^ K) : (x + bias w K).toNat < 2 ^ (K + 1) := by
  have hx := x.isLt
  have hA : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hW : 2 ^ (K + 2) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hcast : ((2 ^ K : ℕ) : ℤ) = 2 ^ K := by push_cast; rfl
  rw [pow_succ, pow_succ] at hW
  have hb : (bias w K).toNat = 2 ^ K - 1 := by
    rw [bias, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toInt_eq_toNat_cond, ← hcast] at h
  rw [BitVec.toNat_add, hb, pow_succ]
  generalize 2 ^ K = A at *
  generalize 2 ^ w = W at *
  rcases Nat.lt_or_ge (x.toNat + (A - 1)) W with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]
    split_ifs at h <;> omega
  · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The low half of a packed row is its first entry, when it fits in `K + 1` bits. -/
theorem pack_and_mask {w K : ℕ} (hw : w = 2 * K + 2) {F : Word w} (G : Word w)
    (hF : F.toNat < 2 ^ (K + 1)) : pack K F G &&& BitVec.ofNat w (2 ^ (K + 1) - 1) = F := by
  have hH : 2 ^ (K + 1) ∣ 2 ^ w := pow_dvd_pow 2 (by omega)
  have hlt : 2 ^ (K + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < 2 ^ (K + 1) := by positivity
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod, pack, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ hH, Nat.add_mod, Nat.mod_mod_of_dvd _ hH,
    Nat.mul_mod_left, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hF]

/-- The high half of a packed row is its second entry, when both fit in `K + 1` bits. -/
theorem pack_shiftRight {w K : ℕ} (hw : w = 2 * K + 2) {F G : Word w}
    (hF : F.toNat < 2 ^ (K + 1)) (hG : G.toNat < 2 ^ (K + 1)) : pack K F G >>> (K + 1) = G := by
  have hW : 2 ^ w = 2 ^ (K + 1) * 2 ^ (K + 1) := by rw [← pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ (K + 1) := by positivity
  have hmul := Nat.mul_le_mul_right (2 ^ (K + 1)) (Nat.succ_le_of_lt hG)
  rw [Nat.succ_mul] at hmul
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, pack, BitVec.toNat_add,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hW,
    Nat.mod_eq_of_lt (by omega : G.toNat * 2 ^ (K + 1) < 2 ^ (K + 1) * 2 ^ (K + 1)),
    Nat.mod_eq_of_lt (by omega), Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hF,
    Nat.zero_add]

/-- **Unpacking recovers the entries**, when they are in `(-2 ^ K, 2 ^ K]`, on words of
`2 * K + 2` bits. -/
theorem unpack_pack {w K : ℕ} (hw : w = 2 * K + 2) {f g : Word w}
    (hf : -2 ^ K < f.toInt ∧ f.toInt ≤ 2 ^ K) (hg : -2 ^ K < g.toInt ∧ g.toInt ≤ 2 ^ K) :
    unpack K (pack K f g) = (f, g) := by
  have hF := toNat_add_bias_lt (by omega : K + 2 ≤ w) hf
  have hG := toNat_add_bias_lt (by omega : K + 2 ≤ w) hg
  unfold unpack
  dsimp only
  rw [pack_add, pack_and_mask hw _ hF, pack_shiftRight hw hF hG, add_sub_cancel_right,
    add_sub_cancel_right]

/-! ### The matrix of the inner loop -/

/-- The entries of the matrix computed by `K` steps of the inner loop on words are in
`(-2 ^ K, 2 ^ K]`, whatever the two words it starts from. -/
theorem innerW_entry_range {w K : ℕ} (hw : K + 2 ≤ w) (x y : Word w) :
    (-2 ^ K < (InnerW.step^[K] ⟨x, y, 1, 0, 0, 1⟩).f0.toInt ∧
        (InnerW.step^[K] ⟨x, y, 1, 0, 0, 1⟩).f0.toInt ≤ 2 ^ K) ∧
      (-2 ^ K < (InnerW.step^[K] ⟨x, y, 1, 0, 0, 1⟩).g0.toInt ∧
        (InnerW.step^[K] ⟨x, y, 1, 0, 0, 1⟩).g0.toInt ≤ 2 ^ K) ∧
      (-2 ^ K < (InnerW.step^[K] ⟨x, y, 1, 0, 0, 1⟩).f1.toInt ∧
        (InnerW.step^[K] ⟨x, y, 1, 0, 0, 1⟩).f1.toInt ≤ 2 ^ K) ∧
      (-2 ^ K < (InnerW.step^[K] ⟨x, y, 1, 0, 0, 1⟩).g1.toInt ∧
        (InnerW.step^[K] ⟨x, y, 1, 0, 0, 1⟩).g1.toInt ≤ 2 ^ K) := by
  obtain ⟨-, -, e0, e1, e2, e3⟩ :=
    refines_iterate hw (refines_identity (by omega) x y) (le_refl K)
  rw [e0, e1, e2, e3]
  exact entry_range_iterate _ _ K

/-- **The inner loop on packed rows computes the transition matrix.** On words of
`2 * K + 2` bits, `K` steps on packed rows from the identity matrix, unpacked, give the
entries computed by `K` steps of the inner loop on words. -/
theorem innerP_spec {w K : ℕ} (hw : w = 2 * K + 2) (x y : Word w) :
    unpack K (InnerP.step^[K] ⟨x, y, pack K 1 0, pack K 0 1⟩).fg0 =
        ((InnerW.step^[K] ⟨x, y, 1, 0, 0, 1⟩).f0, (InnerW.step^[K] ⟨x, y, 1, 0, 0, 1⟩).g0) ∧
      unpack K (InnerP.step^[K] ⟨x, y, pack K 1 0, pack K 0 1⟩).fg1 =
        ((InnerW.step^[K] ⟨x, y, 1, 0, 0, 1⟩).f1, (InnerW.step^[K] ⟨x, y, 1, 0, 0, 1⟩).g1) := by
  have hinit : (⟨x, y, pack K 1 0, pack K 0 1⟩ : InnerP w) = InnerP.ofW K ⟨x, y, 1, 0, 0, 1⟩ :=
    rfl
  obtain ⟨hf0, hg0, hf1, hg1⟩ := innerW_entry_range (by omega : K + 2 ≤ w) x y
  rw [hinit, InnerP.ofW_iterate]
  exact ⟨unpack_pack hw hf0 hg0, unpack_pack hw hf1 hg1⟩

end Bingcd.Pornin
