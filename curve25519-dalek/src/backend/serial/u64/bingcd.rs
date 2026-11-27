//! Pornin's optimized binary GCD (<https://eprint.iacr.org/2020/972>) for inversion and
//! division in the field of integers modulo `2^255 - 19`: the operands of the GCD are four 64-bit
//! limbs, with 31 inner iterations per round, and the cofactors are field elements.
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
//! `lean/Proofs/Helpers/Bingcd/`, function by function, at 64-bit words: its extraction by
//! Aeneas is proved equal to it.
//!
//! There is no branch on the operands: decisions are turned into masks and selections, and
//! the loops have fixed lengths.

use super::field::FieldElement51;

/// The number of inner iterations per round.
pub const K: u32 = 31;

// ---------------------------------------------------------------------------
// Words
// ---------------------------------------------------------------------------

/// All ones if `c`, zero otherwise.
#[inline(always)]
pub fn mask(c: bool) -> u64 {
    0u64.wrapping_sub(c as u64)
}

/// `a` if `c`, `b` otherwise, without branching.
#[inline(always)]
pub fn select(c: bool, a: u64, b: u64) -> u64 {
    b ^ (mask(c) & (a ^ b))
}

/// `a - b - c`, as a word and a borrow.
///
/// The borrow is the top bit of the difference computed on 128 bits. This compiles to a
/// comparison; computing `a + 2^64 - b - c` and testing its high word instead puts two more
/// instructions on the dependency chain of the inner loop.
#[inline(always)]
pub fn subb(a: u64, b: u64, c: bool) -> (u64, bool) {
    let z = (a as u128).wrapping_sub(b as u128).wrapping_sub(c as u128);
    (z as u64, (z >> 127) != 0)
}

/// `a * f + b * g + c` for unsigned `a`, `b` and signed `f`, `g`, `c` (in two's complement),
/// as a low word and a signed high word.
#[inline(always)]
pub fn smul_add2(a: u64, b: u64, f: u64, g: u64, c: u64) -> (u64, u64) {
    let fz = f as i64 as i128 as u128;
    let gz = g as i64 as i128 as u128;
    let cz = c as i64 as i128 as u128;
    let z = (a as u128)
        .wrapping_mul(fz)
        .wrapping_add((b as u128).wrapping_mul(gz))
        .wrapping_add(cz);
    (z as u64, (z >> 64) as u64)
}

// ---------------------------------------------------------------------------
// The inner loop, on words
// ---------------------------------------------------------------------------

/// The state of the inner loop: the approximations of the operands, and the two rows of the
/// transition matrix. The entries of a row are signed and at most `2^31` in absolute value;
/// a row `(f, g)` is packed in one word as `f + 2^32 * g`, modulo `2^64`.
#[derive(Clone, Copy)]
pub struct Inner {
    pub abar: u64,
    pub bbar: u64,
    pub fg0: u64,
    pub fg1: u64,
}

/// The transition matrix of a round: four signed words.
#[derive(Clone, Copy)]
pub struct Matrix {
    pub f0: u64,
    pub g0: u64,
    pub f1: u64,
    pub g1: u64,
}

/// One step of the inner loop: if `abar` is odd and below `bbar`, the operands and the rows
/// are swapped; if `abar` is odd, the second operand and row are subtracted from the first;
/// then `abar` is halved and the second row doubled. The two decisions are masks, and the
/// packing is linear, so that subtracting and doubling packed rows acts on their entries.
#[inline(always)]
pub fn inner_step(s: Inner) -> Inner {
    let a_odd = 0u64.wrapping_sub(s.abar & 1);
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
/// they are in `(-2^31, 2^31]`: adding `2^31 - 1` to each makes both halves nonnegative.
#[inline(always)]
pub fn unpack_row(fg: u64) -> (u64, u64) {
    let t = fg.wrapping_add(0x7FFFFFFF7FFFFFFF);
    (
        (t & 0xFFFFFFFF).wrapping_sub(0x7FFFFFFF),
        (t >> 32).wrapping_sub(0x7FFFFFFF),
    )
}

/// The inner loop: `K` steps from the approximations and the identity matrix.
pub fn inner(abar: u64, bbar: u64) -> Matrix {
    let mut s = Inner {
        abar,
        bbar,
        fg0: 1,
        fg1: 0x1_0000_0000,
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
    pub a: u64,
    pub b: u64,
    pub f0: u64,
    pub g0: u64,
    pub f1: u64,
    pub g1: u64,
}

/// One of the last steps: the step of the inner loop, on separate entries.
#[inline(always)]
pub fn tail_step(s: Tail) -> Tail {
    let a_odd = 0u64.wrapping_sub(s.a & 1);
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
pub fn tail<const T: u32>(a: u64, b: u64) -> Tail {
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
// Four limbs
// ---------------------------------------------------------------------------

/// `a * f + b * g` for signed words `f` and `g`: four limbs and a signed top word.
pub fn lin_comb(a: &[u64; 4], b: &[u64; 4], f: u64, g: u64) -> ([u64; 4], u64) {
    let (r0, c0) = smul_add2(a[0], b[0], f, g, 0);
    let (r1, c1) = smul_add2(a[1], b[1], f, g, c0);
    let (r2, c2) = smul_add2(a[2], b[2], f, g, c1);
    let (r3, c3) = smul_add2(a[3], b[3], f, g, c2);
    ([r0, r1, r2, r3], c3)
}

/// The four low limbs of the five-limb value `(r, c)` shifted right by `S` bits, for
/// `0 < S < 64`.
#[inline(always)]
pub fn shr_low<const S: u32>(r: &[u64; 4], c: u64) -> [u64; 4] {
    [
        (r[0] >> S) | (r[1] << (64 - S)),
        (r[1] >> S) | (r[2] << (64 - S)),
        (r[2] >> S) | (r[3] << (64 - S)),
        (r[3] >> S) | (c << (64 - S)),
    ]
}

/// `a - b` modulo `2^256`, and the borrow.
pub fn sub4(a: &[u64; 4], b: &[u64; 4]) -> ([u64; 4], bool) {
    let (r0, c0) = subb(a[0], b[0], false);
    let (r1, c1) = subb(a[1], b[1], c0);
    let (r2, c2) = subb(a[2], b[2], c1);
    let (r3, c3) = subb(a[3], b[3], c2);
    ([r0, r1, r2, r3], c3)
}

/// `a` if `c`, `b` otherwise, limb by limb.
pub fn select4(c: bool, a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    [
        select(c, a[0], b[0]),
        select(c, a[1], b[1]),
        select(c, a[2], b[2]),
        select(c, a[3], b[3]),
    ]
}

/// Subtract `p` from the five-limb value `(a, c)` unless that would be negative.
pub fn cond_sub(a: &[u64; 4], c: bool, p: &[u64; 4]) -> [u64; 4] {
    let (r, borrow) = sub4(a, p);
    select4(borrow & !c, a, &r)
}

/// `|(r, c) / 2^K|` and the sign of `(r, c)`, for a signed five-limb value.
pub fn shr_abs(r: &[u64; 4], c: u64) -> ([u64; 4], bool) {
    let low = shr_low::<K>(r, c);
    let neg = (c >> 63) == 1;
    let (n, _) = sub4(&[0, 0, 0, 0], &low);
    (select4(neg, &n, &low), neg)
}

/// `|(a * f + b * g) / 2^K|` and the sign of `a * f + b * g`.
pub fn apply_row(a: &[u64; 4], b: &[u64; 4], f: u64, g: u64) -> ([u64; 4], bool) {
    let (r, c) = lin_comb(a, b, f, g);
    shr_abs(&r, c)
}

/// `a | b`, limb by limb. It is as long as the longer of `a` and `b`.
pub fn or4(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    [a[0] | b[0], a[1] | b[1], a[2] | b[2], a[3] | b[3]]
}

/// `(x[j], x[j - 1])` for the most significant nonzero limb `m[j]` of `m` with `j >= 1`, and
/// `(0, 0)` if there is none. Every limb is visited, and each visit ends with two selections.
pub fn top_two(m: &[u64; 4], x: &[u64; 4]) -> (u64, u64) {
    let h1 = select(m[1] == 0, 0, x[1]);
    let l1 = select(m[1] == 0, 0, x[0]);
    let h2 = select(m[2] == 0, h1, x[2]);
    let l2 = select(m[2] == 0, l1, x[1]);
    let h3 = select(m[3] == 0, h2, x[3]);
    let l3 = select(m[3] == 0, l2, x[2]);
    (h3, l3)
}

/// The approximation of an operand `a` no longer than `m`: its 33 bits below the top of `m`,
/// above its 31 low bits. The two limbs of `a` at the top of `m` are shifted left by the
/// number of leading zeros of the top limb of `m`; when `m` fits in a word, so does `a`, and
/// the approximation is `a` itself.
pub fn approx_top(m: &[u64; 4], a: &[u64; 4]) -> u64 {
    let (tm, _) = top_two(m, m);
    let (hi, lo) = top_two(m, a);
    let none = tm == 0;
    let c = select(none, 0, tm.leading_zeros() as u64) as u32;
    // a right shift by `64 - c`, as two shifts by less than 64
    let win = select(none, a[0], (hi << c) | ((lo >> 1) >> (63 - c)));
    ((win >> (64 - K - 2)) << K).wrapping_add(a[0] & ((1u64 << K) - 1))
}

// ---------------------------------------------------------------------------
// Cofactors
// ---------------------------------------------------------------------------

/// The limbs of `2^46 * p` in radix `2^51`: the first one, and the four others. Added to a
/// row of cofactors, they keep every limb nonnegative.
pub const P46_0: u128 = 0x1fffffffffffb400000000000;
pub const P46_I: u128 = 0x1ffffffffffffc00000000000;

/// `c + a * f + b * g` on 128 bits, for signed words `f` and `g` (in two's complement).
#[inline(always)]
pub fn cof_limb(c: u128, a: u64, b: u64, f: u64, g: u64) -> u128 {
    c.wrapping_add((a as u128).wrapping_mul(f as i64 as i128 as u128))
        .wrapping_add((b as u128).wrapping_mul(g as i64 as i128 as u128))
}

/// The field element with limbs `c0, ..., c4` in radix `2^51`, each below `2^98`: the carry
/// chain that ends a field multiplication. The limbs of the result are below `2^52`.
#[inline(always)]
pub fn carry_wide(c0: u128, c1: u128, c2: u128, c3: u128, c4: u128) -> FieldElement51 {
    let c1 = c1 + (((c0 >> 51) as u64) as u128);
    let c2 = c2 + (((c1 >> 51) as u64) as u128);
    let c3 = c3 + (((c2 >> 51) as u64) as u128);
    let c4 = c4 + (((c3 >> 51) as u64) as u128);
    let carry = (c4 >> 51) as u64;
    let r0 = ((c0 as u64) & MASK51) + carry * 19;
    FieldElement51([
        r0 & MASK51,
        ((c1 as u64) & MASK51) + (r0 >> 51),
        (c2 as u64) & MASK51,
        (c3 as u64) & MASK51,
        (c4 as u64) & MASK51,
    ])
}

/// `u * f + v * g` in the field, negated when `neg` is set, for signed words `f` and `g` of at
/// most `2^43` in absolute value and limbs of `u` and `v` below `2^52`. There is no division
/// by a power of two, and no decision on the cofactors: each limb is `u[i] * f + v[i] * g`
/// plus a limb of `2^46 * p`, which keeps it nonnegative.
#[inline(always)]
pub fn cof_row(
    u: &FieldElement51,
    v: &FieldElement51,
    f: u64,
    g: u64,
    neg: bool,
) -> FieldElement51 {
    let f = select(neg, 0u64.wrapping_sub(f), f);
    let g = select(neg, 0u64.wrapping_sub(g), g);
    carry_wide(
        cof_limb(P46_0, u.0[0], v.0[0], f, g),
        cof_limb(P46_I, u.0[1], v.0[1], f, g),
        cof_limb(P46_I, u.0[2], v.0[2], f, g),
        cof_limb(P46_I, u.0[3], v.0[3], f, g),
        cof_limb(P46_I, u.0[4], v.0[4], f, g),
    )
}

// ---------------------------------------------------------------------------
// Rounds
// ---------------------------------------------------------------------------

/// The state of the algorithm: the operands `a`, `b` on four limbs, and their cofactors
/// `u`, `v` as field elements.
#[derive(Clone, Copy)]
pub struct State {
    pub a: [u64; 4],
    pub u: FieldElement51,
    pub b: [u64; 4],
    pub v: FieldElement51,
}

/// One round: the approximations are read from the operands, the inner loop runs on words,
/// and the transition matrix is applied to the operands and to the cofactors.
#[inline(always)]
pub fn round(s: &State) -> State {
    // the top of `a | b` is the top of the longer operand
    let ab = or4(&s.a, &s.b);
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
pub const P: [u64; 4] = [
    0xFFFFFFFFFFFFFFED,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
    0x7FFFFFFFFFFFFFFF,
];

/// The number of rounds for a 255-bit modulus: after `15 * 31 = 465` steps the operands have
/// at most 44 bits, or `a` is zero.
pub const ROUNDS: u32 = 15;

/// The number of last steps for a 255-bit modulus: `2 * 255 - 2 - 465`.
pub const TAIL: u32 = 43;

const MASK51: u64 = (1u64 << 51) - 1;

/// The canonical representative in `[0, p)` of a field element given by five limbs of at most
/// `2^51 + 2^23`, on four 64-bit limbs: a carry pass, a packing and one conditional subtraction.
pub fn freeze(a: &[u64; 5]) -> [u64; 4] {
    let s0 = a[0];
    let s1 = a[1].wrapping_add(s0 >> 51);
    let s2 = a[2].wrapping_add(s1 >> 51);
    let s3 = a[3].wrapping_add(s2 >> 51);
    let s4 = a[4].wrapping_add(s3 >> 51);
    let r0 = s0 & MASK51;
    let r1 = s1 & MASK51;
    let r2 = s2 & MASK51;
    let r3 = s3 & MASK51;
    let r4 = s4 & MASK51;
    let c = s4 >> 51;
    let packed = [
        r0.wrapping_add(r1 << 51),
        (r1 >> 13).wrapping_add(r2 << 38),
        (r2 >> 26).wrapping_add(r3 << 25),
        (r3 >> 39).wrapping_add(r4 << 12).wrapping_add(c << 63),
    ];
    cond_sub(&packed, false, &P)
}

/// `2^-508` in the field: the cofactors pick up a factor `2^K` in every round and `2^TAIL` in
/// the last steps, `2^(K * ROUNDS + TAIL) = 2^508` in all.
pub const SCALE: FieldElement51 = FieldElement51([
    0x6deab9cb8606c,
    0x1104f6c7fa53a,
    0x15a0f99e23750,
    0x18d1e7e3a264b,
    0x24e016b1490aa,
]);

/// `u * 2^508 / z` in the field, and zero if `z` is zero: the rounds and the last steps of
/// Pornin's algorithm on the canonical representative of `z` and the modulus, with the cofactor
/// of `z` started at `u`. The limbs of `z` are at most `2^51 + 2^23`, those of `u` and of the
/// result are below `2^52`.
pub fn scaled_div(u: &FieldElement51, z: &[u64; 5]) -> FieldElement51 {
    let mut s = State {
        a: freeze(z),
        u: *u,
        b: P,
        v: FieldElement51::ZERO,
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
/// of the input are at most `2^51 + 2^23`, those of the result are below `2^52`.
// Not inlined: when it is, the callers' own field arithmetic was measured to compile worse.
#[inline(never)]
pub fn invert(z: &[u64; 5]) -> FieldElement51 {
    scaled_div(&SCALE, z)
}

/// The quotient `x / z` of two field elements modulo `2^255 - 19`; a quotient by zero is zero.
/// The limbs of `z` are at most `2^51 + 2^23`, those of `x` are below `2^54`, and those of the
/// result are below `2^52`. This is one run of the binary gcd, started from `x * 2^-508`.
#[inline(never)]
pub fn divide(x: &FieldElement51, z: &[u64; 5]) -> FieldElement51 {
    scaled_div(&(x * &SCALE), z)
}
