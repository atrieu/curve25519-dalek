//! Pornin's optimized binary GCD (<https://eprint.iacr.org/2020/972>) for inversion and
//! division in the field of integers modulo `2^255 - 19`: the operands of the GCD are eight 32-bit
//! limbs, with 15 inner iterations per round, and the cofactors are field elements.
//!
//! This is `backend::serial::u64::bingcd` on 32-bit words, with 64-bit intermediate values
//! only: the words are half as long, so a round has half as many steps and the operands
//! twice as many limbs.
//!
//! The rounds are followed by a last run of steps on single words: once the operands are
//! short, the steps need no approximation, and only one cofactor is updated after them.
//! In a round, the approximations of both operands are read from the limbs at the top of
//! `a | b`, and the two entries of a row of the transition matrix share one word.
//!
//! The cofactors only matter modulo `p`. A round applies a row of the transition matrix to
//! them limb by limb, with no division by `2^K`: over the 508 steps they pick up a factor
//! `2^508`, which is removed by starting from the constant `2^-508`. A quotient `x / y` costs
//! one multiplication more than an inverse: the cofactors only go through linear combinations,
//! so starting from `x * 2^-508` instead of `2^-508` multiplies the result by `x`.
//!
//! The code follows the Lean definition of `Bingcd.Pornin.porninDivR` in
//! `lean/Proofs/Helpers/Bingcd/`, function by function, at 32-bit words: its extraction by
//! Aeneas is proved equal to it.
//!
//! There is no branch on the operands: decisions are turned into masks and selections, and
//! the loops have fixed lengths.

use super::field::FieldElement2625;

/// The number of inner iterations per round.
pub const K: u32 = 15;

// ---------------------------------------------------------------------------
// Words
// ---------------------------------------------------------------------------

/// All ones if `c`, zero otherwise.
#[inline(always)]
pub fn mask(c: bool) -> u32 {
    0u32.wrapping_sub(c as u32)
}

/// `a` if `c`, `b` otherwise, without branching.
#[inline(always)]
pub fn select(c: bool, a: u32, b: u32) -> u32 {
    b ^ (mask(c) & (a ^ b))
}

/// `a - b - c`, as a word and a borrow: the top bit of the difference computed on 64 bits.
#[inline(always)]
pub fn subb(a: u32, b: u32, c: bool) -> (u32, bool) {
    let z = (a as u64).wrapping_sub(b as u64).wrapping_sub(c as u64);
    (z as u32, (z >> 63) != 0)
}

/// `a * f + b * g + c` for unsigned `a`, `b` and signed `f`, `g`, `c` (in two's complement),
/// as a low word and a signed high word.
#[inline(always)]
pub fn smul_add2(a: u32, b: u32, f: u32, g: u32, c: u32) -> (u32, u32) {
    let fz = f as i32 as i64 as u64;
    let gz = g as i32 as i64 as u64;
    let cz = c as i32 as i64 as u64;
    let z = (a as u64)
        .wrapping_mul(fz)
        .wrapping_add((b as u64).wrapping_mul(gz))
        .wrapping_add(cz);
    (z as u32, (z >> 32) as u32)
}

// ---------------------------------------------------------------------------
// The inner loop, on words
// ---------------------------------------------------------------------------

/// The state of the inner loop: the approximations of the operands, and the two rows of the
/// transition matrix. The entries of a row are signed and at most `2^15` in absolute value;
/// a row `(f, g)` is packed in one word as `f + 2^16 * g`, modulo `2^32`.
#[derive(Clone, Copy)]
pub struct Inner {
    pub abar: u32,
    pub bbar: u32,
    pub fg0: u32,
    pub fg1: u32,
}

/// The transition matrix of a round: four signed words.
#[derive(Clone, Copy)]
pub struct Matrix {
    pub f0: u32,
    pub g0: u32,
    pub f1: u32,
    pub g1: u32,
}

/// One step of the inner loop: if `abar` is odd and below `bbar`, the operands and the rows
/// are swapped; if `abar` is odd, the second operand and row are subtracted from the first;
/// then `abar` is halved and the second row doubled. The two decisions are masks, and the
/// packing is linear, so that subtracting and doubling packed rows acts on their entries.
#[inline(always)]
pub fn inner_step(s: Inner) -> Inner {
    let a_odd = 0u32.wrapping_sub(s.abar & 1);
    let (_, lt) = subb(s.abar, s.bbar, false);
    let swap = a_odd & mask(lt);
    let t1 = swap & (s.abar ^ s.bbar);
    let xa = s.abar ^ t1;
    let xb = s.bbar ^ t1;
    let t2 = swap & (s.fg0 ^ s.fg1);
    let r0 = s.fg0 ^ t2;
    let r1 = s.fg1 ^ t2;
    Inner {
        abar: xa.wrapping_sub(a_odd & xb) >> 1,
        bbar: xb,
        fg0: r0.wrapping_sub(a_odd & r1),
        fg1: r1 << 1,
    }
}

/// The two entries of a packed row, as signed words. After the `K` steps of the inner loop
/// they are in `(-2^15, 2^15]`: adding `2^15 - 1` to each makes both halves nonnegative.
#[inline(always)]
pub fn unpack_row(fg: u32) -> (u32, u32) {
    let t = fg.wrapping_add(0x7FFF7FFF);
    (
        (t & 0xFFFF).wrapping_sub(0x7FFF),
        (t >> 16).wrapping_sub(0x7FFF),
    )
}

/// The inner loop: `K` steps from the approximations and the identity matrix.
pub fn inner(abar: u32, bbar: u32) -> Matrix {
    let mut s = Inner {
        abar,
        bbar,
        fg0: 1,
        fg1: 0x1_0000,
    };
    let mut i = 0u32;
    while i < K {
        s = inner_step(s);
        i += 1;
    }
    let (f0, g0) = unpack_row(s.fg0);
    let (f1, g1) = unpack_row(s.fg1);
    Matrix { f0, g0, f1, g1 }
}

/// The state of the last steps: the least significant words of the operands, and the
/// transition matrix with one signed word per entry. The entries grow to `2^T` in absolute
/// value for `T` steps, which is more than the halves of a packed row hold.
#[derive(Clone, Copy)]
pub struct Tail {
    pub a: u32,
    pub b: u32,
    pub f0: u32,
    pub g0: u32,
    pub f1: u32,
    pub g1: u32,
}

/// One of the last steps: the step of the inner loop, on separate entries.
#[inline(always)]
pub fn tail_step(s: Tail) -> Tail {
    let a_odd = 0u32.wrapping_sub(s.a & 1);
    let (_, lt) = subb(s.a, s.b, false);
    let swap = a_odd & mask(lt);
    let t1 = swap & (s.a ^ s.b);
    let xa = s.a ^ t1;
    let xb = s.b ^ t1;
    let t2 = swap & (s.f0 ^ s.f1);
    let f0 = s.f0 ^ t2;
    let f1 = s.f1 ^ t2;
    let t3 = swap & (s.g0 ^ s.g1);
    let g0 = s.g0 ^ t3;
    let g1 = s.g1 ^ t3;
    Tail {
        a: xa.wrapping_sub(a_odd & xb) >> 1,
        b: xb,
        f0: f0.wrapping_sub(a_odd & f1),
        g0: g0.wrapping_sub(a_odd & g1),
        f1: f1 << 1,
        g1: g1 << 1,
    }
}

/// The last steps: `T` steps from the words `a`, `b` and the identity matrix.
pub fn tail<const T: u32>(a: u32, b: u32) -> Tail {
    let mut s = Tail {
        a,
        b,
        f0: 1,
        g0: 0,
        f1: 0,
        g1: 1,
    };
    let mut i = 0u32;
    while i < T {
        s = tail_step(s);
        i += 1;
    }
    s
}

// ---------------------------------------------------------------------------
// Eight limbs
// ---------------------------------------------------------------------------

/// `a * f + b * g` for signed words `f` and `g`: eight limbs and a signed top word.
pub fn lin_comb(a: &[u32; 8], b: &[u32; 8], f: u32, g: u32) -> ([u32; 8], u32) {
    let (r0, c0) = smul_add2(a[0], b[0], f, g, 0);
    let (r1, c1) = smul_add2(a[1], b[1], f, g, c0);
    let (r2, c2) = smul_add2(a[2], b[2], f, g, c1);
    let (r3, c3) = smul_add2(a[3], b[3], f, g, c2);
    let (r4, c4) = smul_add2(a[4], b[4], f, g, c3);
    let (r5, c5) = smul_add2(a[5], b[5], f, g, c4);
    let (r6, c6) = smul_add2(a[6], b[6], f, g, c5);
    let (r7, c7) = smul_add2(a[7], b[7], f, g, c6);
    ([r0, r1, r2, r3, r4, r5, r6, r7], c7)
}

/// The eight low limbs of the nine-limb value `(r, c)` shifted right by `S` bits, for
/// `0 < S < 32`.
#[inline(always)]
pub fn shr_low<const S: u32>(r: &[u32; 8], c: u32) -> [u32; 8] {
    [
        (r[0] >> S) | (r[1] << (32 - S)),
        (r[1] >> S) | (r[2] << (32 - S)),
        (r[2] >> S) | (r[3] << (32 - S)),
        (r[3] >> S) | (r[4] << (32 - S)),
        (r[4] >> S) | (r[5] << (32 - S)),
        (r[5] >> S) | (r[6] << (32 - S)),
        (r[6] >> S) | (r[7] << (32 - S)),
        (r[7] >> S) | (c << (32 - S)),
    ]
}

/// `a - b` modulo `2^256`, and the borrow.
pub fn sub8(a: &[u32; 8], b: &[u32; 8]) -> ([u32; 8], bool) {
    let (r0, c0) = subb(a[0], b[0], false);
    let (r1, c1) = subb(a[1], b[1], c0);
    let (r2, c2) = subb(a[2], b[2], c1);
    let (r3, c3) = subb(a[3], b[3], c2);
    let (r4, c4) = subb(a[4], b[4], c3);
    let (r5, c5) = subb(a[5], b[5], c4);
    let (r6, c6) = subb(a[6], b[6], c5);
    let (r7, c7) = subb(a[7], b[7], c6);
    ([r0, r1, r2, r3, r4, r5, r6, r7], c7)
}

/// `a` if `c`, `b` otherwise, limb by limb.
pub fn select8(c: bool, a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    [
        select(c, a[0], b[0]),
        select(c, a[1], b[1]),
        select(c, a[2], b[2]),
        select(c, a[3], b[3]),
        select(c, a[4], b[4]),
        select(c, a[5], b[5]),
        select(c, a[6], b[6]),
        select(c, a[7], b[7]),
    ]
}

/// Subtract `p` from the nine-limb value `(a, c)` unless that would be negative.
pub fn cond_sub(a: &[u32; 8], c: bool, p: &[u32; 8]) -> [u32; 8] {
    let (r, borrow) = sub8(a, p);
    select8(borrow & !c, a, &r)
}

/// `|(r, c) / 2^K|` and the sign of `(r, c)`, for a signed nine-limb value.
pub fn shr_abs(r: &[u32; 8], c: u32) -> ([u32; 8], bool) {
    let low = shr_low::<K>(r, c);
    let neg = (c >> 31) == 1;
    let (n, _) = sub8(&[0, 0, 0, 0, 0, 0, 0, 0], &low);
    (select8(neg, &n, &low), neg)
}

/// `|(a * f + b * g) / 2^K|` and the sign of `a * f + b * g`.
pub fn apply_row(a: &[u32; 8], b: &[u32; 8], f: u32, g: u32) -> ([u32; 8], bool) {
    let (r, c) = lin_comb(a, b, f, g);
    shr_abs(&r, c)
}

/// `a | b`, limb by limb. It is as long as the longer of `a` and `b`.
pub fn or8(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    [
        a[0] | b[0],
        a[1] | b[1],
        a[2] | b[2],
        a[3] | b[3],
        a[4] | b[4],
        a[5] | b[5],
        a[6] | b[6],
        a[7] | b[7],
    ]
}

/// `(x[j], x[j - 1])` for the most significant nonzero limb `m[j]` of `m` with `j >= 1`, and
/// `(0, 0)` if there is none. Every limb is visited, and each visit ends with two selections.
pub fn top_two(m: &[u32; 8], x: &[u32; 8]) -> (u32, u32) {
    let h1 = select(m[1] == 0, 0, x[1]);
    let l1 = select(m[1] == 0, 0, x[0]);
    let h2 = select(m[2] == 0, h1, x[2]);
    let l2 = select(m[2] == 0, l1, x[1]);
    let h3 = select(m[3] == 0, h2, x[3]);
    let l3 = select(m[3] == 0, l2, x[2]);
    let h4 = select(m[4] == 0, h3, x[4]);
    let l4 = select(m[4] == 0, l3, x[3]);
    let h5 = select(m[5] == 0, h4, x[5]);
    let l5 = select(m[5] == 0, l4, x[4]);
    let h6 = select(m[6] == 0, h5, x[6]);
    let l6 = select(m[6] == 0, l5, x[5]);
    let h7 = select(m[7] == 0, h6, x[7]);
    let l7 = select(m[7] == 0, l6, x[6]);
    (h7, l7)
}

/// The approximation of an operand `a` no longer than `m`: its 17 bits below the top of `m`,
/// above its 15 low bits. The two limbs of `a` at the top of `m` are shifted left by the
/// number of leading zeros of the top limb of `m`; when `m` fits in a word, so does `a`, and
/// the approximation is `a` itself.
pub fn approx_top(m: &[u32; 8], a: &[u32; 8]) -> u32 {
    let (tm, _) = top_two(m, m);
    let (hi, lo) = top_two(m, a);
    let none = tm == 0;
    let c = select(none, 0, tm.leading_zeros());
    // a right shift by `32 - c`, as two shifts by less than 32
    let win = select(none, a[0], (hi << c) | ((lo >> 1) >> (31 - c)));
    ((win >> (32 - K - 2)) << K).wrapping_add(a[0] & ((1u32 << K) - 1))
}

// ---------------------------------------------------------------------------
// Cofactors
// ---------------------------------------------------------------------------

/// The limbs of `2^31 * p` for the limbs of 26 and 25 bits: the first one, those at odd
/// positions, and the others at even positions. Added to a row of cofactors, they keep every
/// limb nonnegative.
pub const P31_0: u64 = 0x1fffff680000000;
pub const P31_ODD: u64 = 0xffffff80000000;
pub const P31_EVEN: u64 = 0x1ffffff80000000;

/// `c + a * f + b * g` on 64 bits, for signed words `f` and `g` (in two's complement).
#[inline(always)]
pub fn cof_limb(c: u64, a: u32, b: u32, f: u32, g: u32) -> u64 {
    c.wrapping_add((a as u64).wrapping_mul(f as i32 as i64 as u64))
        .wrapping_add((b as u64).wrapping_mul(g as i32 as i64 as u64))
}

/// `u * f + v * g` in the field, negated when `neg` is set, for signed words `f` and `g` of at
/// most `2^28` in absolute value and limbs of `u` and `v` below `2^26`. There is no division
/// by a power of two, and no decision on the cofactors: each limb is `u[i] * f + v[i] * g`
/// plus a limb of `2^31 * p`, which keeps it nonnegative, and `reduce` carries.
#[inline(always)]
pub fn cof_row(
    u: &FieldElement2625,
    v: &FieldElement2625,
    f: u32,
    g: u32,
    neg: bool,
) -> FieldElement2625 {
    let f = select(neg, 0u32.wrapping_sub(f), f);
    let g = select(neg, 0u32.wrapping_sub(g), g);
    FieldElement2625::reduce([
        cof_limb(P31_0, u.0[0], v.0[0], f, g),
        cof_limb(P31_ODD, u.0[1], v.0[1], f, g),
        cof_limb(P31_EVEN, u.0[2], v.0[2], f, g),
        cof_limb(P31_ODD, u.0[3], v.0[3], f, g),
        cof_limb(P31_EVEN, u.0[4], v.0[4], f, g),
        cof_limb(P31_ODD, u.0[5], v.0[5], f, g),
        cof_limb(P31_EVEN, u.0[6], v.0[6], f, g),
        cof_limb(P31_ODD, u.0[7], v.0[7], f, g),
        cof_limb(P31_EVEN, u.0[8], v.0[8], f, g),
        cof_limb(P31_ODD, u.0[9], v.0[9], f, g),
    ])
}

// ---------------------------------------------------------------------------
// Rounds
// ---------------------------------------------------------------------------

/// The state of the algorithm: the operands `a`, `b` on eight limbs, and their cofactors
/// `u`, `v` as field elements.
#[derive(Clone, Copy)]
pub struct State {
    pub a: [u32; 8],
    pub u: FieldElement2625,
    pub b: [u32; 8],
    pub v: FieldElement2625,
}

/// One round: the approximations are read from the operands, the inner loop runs on words,
/// and the transition matrix is applied to the operands and to the cofactors.
#[inline(always)]
pub fn round(s: &State) -> State {
    // the top of `a | b` is the top of the longer operand
    let ab = or8(&s.a, &s.b);
    let t = inner(approx_top(&ab, &s.a), approx_top(&ab, &s.b));
    let (a1, na) = apply_row(&s.a, &s.b, t.f0, t.g0);
    let (b1, nb) = apply_row(&s.a, &s.b, t.f1, t.g1);
    State {
        a: a1,
        u: cof_row(&s.u, &s.v, t.f0, t.g0, na),
        b: b1,
        v: cof_row(&s.u, &s.v, t.f1, t.g1, nb),
    }
}

// ---------------------------------------------------------------------------
// The field of integers modulo 2^255 - 19
// ---------------------------------------------------------------------------

/// The modulus `2^255 - 19`.
pub const P: [u32; 8] = [
    0xFFFFFFED, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0x7FFFFFFF,
];

/// The number of rounds for a 255-bit modulus: after `32 * 15 = 480` steps the operands have
/// at most 30 bits, or `a` is zero.
pub const ROUNDS: u32 = 32;

/// The number of last steps for a 255-bit modulus: `2 * 255 - 2 - 480`.
pub const TAIL: u32 = 28;

const MASK26: u32 = (1u32 << 26) - 1;

const MASK25: u32 = (1u32 << 25) - 1;

/// The canonical representative in `[0, p)` of a field element given by ten limbs, below
/// `2^26` at even positions and below `2^25 + 2^18` at odd ones, on eight 32-bit limbs: a
/// carry pass, a packing and one conditional subtraction.
pub fn freeze(a: &[u32; 10]) -> [u32; 8] {
    let s0 = a[0];
    let s1 = a[1].wrapping_add(s0 >> 26);
    let s2 = a[2].wrapping_add(s1 >> 25);
    let s3 = a[3].wrapping_add(s2 >> 26);
    let s4 = a[4].wrapping_add(s3 >> 25);
    let s5 = a[5].wrapping_add(s4 >> 26);
    let s6 = a[6].wrapping_add(s5 >> 25);
    let s7 = a[7].wrapping_add(s6 >> 26);
    let s8 = a[8].wrapping_add(s7 >> 25);
    let s9 = a[9].wrapping_add(s8 >> 26);
    let r0 = s0 & MASK26;
    let r1 = s1 & MASK25;
    let r2 = s2 & MASK26;
    let r3 = s3 & MASK25;
    let r4 = s4 & MASK26;
    let r5 = s5 & MASK25;
    let r6 = s6 & MASK26;
    let r7 = s7 & MASK25;
    let r8 = s8 & MASK26;
    let r9 = s9 & MASK25;
    let c = s9 >> 25;
    let packed = [
        r0.wrapping_add(r1 << 26),
        (r1 >> 6).wrapping_add(r2 << 19),
        (r2 >> 13).wrapping_add(r3 << 13),
        (r3 >> 19).wrapping_add(r4 << 6),
        r5.wrapping_add(r6 << 25),
        (r6 >> 7).wrapping_add(r7 << 19),
        (r7 >> 13).wrapping_add(r8 << 12),
        (r8 >> 20).wrapping_add(r9 << 6).wrapping_add(c << 31),
    ];
    cond_sub(&packed, false, &P)
}

/// `2^-508` in the field: the cofactors pick up a factor `2^K` in every round and `2^TAIL` in
/// the last steps, `2^(K * ROUNDS + TAIL) = 2^508` in all.
pub const SCALE: FieldElement2625 = FieldElement2625([
    0xb8606c, 0x1b7aae7, 0x7fa53a, 0x4413db, 0x1e23750, 0x5683e6, 0x23a264b, 0x63479f, 0x31490aa,
    0x93805a,
]);

/// `u * 2^508 / z` in the field, and zero if `z` is zero: the rounds and the last steps of
/// Pornin's algorithm on the canonical representative of `z` and the modulus, with the cofactor
/// of `z` started at `u`. The limbs of `z` are below `2^26` at even positions and below
/// `2^25 + 2^18` at odd ones, those of `u` and of the result are below `2^26`.
pub fn scaled_div(u: &FieldElement2625, z: &[u32; 10]) -> FieldElement2625 {
    let mut s = State {
        a: freeze(z),
        u: *u,
        b: P,
        v: FieldElement2625::ZERO,
    };
    let mut i = 0u32;
    while i < ROUNDS {
        s = round(&s);
        i += 1;
    }
    let t = tail::<TAIL>(s.a[0], s.b[0]);
    // only `v` is needed, and `b` is known to be nonnegative: there is no sign to fix
    cof_row(&s.u, &s.v, t.f1, t.g1, false)
}

/// The inverse of a field element modulo `2^255 - 19`; the inverse of zero is zero. The limbs
/// of the input are below `2^26` at even positions and below `2^25 + 2^18` at odd ones, those
/// of the result are below `2^26`.
// Not inlined: when it is, the callers' own field arithmetic was measured to compile worse.
#[inline(never)]
pub fn invert(z: &[u32; 10]) -> FieldElement2625 {
    scaled_div(&SCALE, z)
}

/// The quotient `x / z` of two field elements modulo `2^255 - 19`; a quotient by zero is zero.
/// The limbs of `z` are below `2^26` at even positions and below `2^25 + 2^18` at odd ones,
/// those of `x` and of the result are below `2^26`. This is one run of the binary gcd, started
/// from `x * 2^-508`.
#[inline(never)]
pub fn divide(x: &FieldElement2625, z: &[u32; 10]) -> FieldElement2625 {
    scaled_div(&(x * &SCALE), z)
}
