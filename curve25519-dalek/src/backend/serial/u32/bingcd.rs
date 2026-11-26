//! Pornin's optimized binary GCD (<https://eprint.iacr.org/2020/972>) for inversion and
//! division modulo an odd modulus of eight 32-bit limbs, with 15 inner iterations per round,
//! and its use for the field of integers modulo `2^255 - 19` on ten limbs of 25.5 bits.
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
//! A quotient `x / y` costs no more than an inverse: the cofactors only go through linear
//! combinations, so starting one of them at `x` instead of 1 multiplies the result by `x`.
//!
//! The code follows the Lean definitions of `Bingcd.Pornin.porninDivSL` and of
//! `Bingcd.Limbs.Curve25519.U32.div` and `inv` in `lean/Proofs/Helpers/Bingcd/`, function by
//! function, at 32-bit words: its extraction by Aeneas is proved equal to them.
//!
//! There is no branch on the operands: decisions are turned into masks and selections, and
//! the loops have fixed lengths.

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

/// `a + b + c`, as a word and a carry.
#[inline(always)]
pub fn addc(a: u32, b: u32, c: bool) -> (u32, bool) {
    let s = (a as u64) + (b as u64) + (c as u64);
    (s as u32, (s >> 32) != 0)
}

/// `a - b - c`, as a word and a borrow: the top bit of the difference computed on 64 bits.
#[inline(always)]
pub fn subb(a: u32, b: u32, c: bool) -> (u32, bool) {
    let z = (a as u64).wrapping_sub(b as u64).wrapping_sub(c as u64);
    (z as u32, (z >> 63) != 0)
}

/// `a * b + c + d`, as a low word and a high word.
#[inline(always)]
pub fn mul_add2(a: u32, b: u32, c: u32, d: u32) -> (u32, u32) {
    let p = (a as u64) * (b as u64) + (c as u64) + (d as u64);
    (p as u32, (p >> 32) as u32)
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

/// `a + b` modulo `2^256`.
pub fn add8(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    let (r0, c0) = addc(a[0], b[0], false);
    let (r1, c1) = addc(a[1], b[1], c0);
    let (r2, c2) = addc(a[2], b[2], c1);
    let (r3, c3) = addc(a[3], b[3], c2);
    let (r4, c4) = addc(a[4], b[4], c3);
    let (r5, c5) = addc(a[5], b[5], c4);
    let (r6, c6) = addc(a[6], b[6], c5);
    let (r7, _) = addc(a[7], b[7], c6);
    [r0, r1, r2, r3, r4, r5, r6, r7]
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

/// Whether `a = b`.
pub fn eq8(a: &[u32; 8], b: &[u32; 8]) -> bool {
    let x = (a[0] ^ b[0])
        | (a[1] ^ b[1])
        | (a[2] ^ b[2])
        | (a[3] ^ b[3])
        | (a[4] ^ b[4])
        | (a[5] ^ b[5])
        | (a[6] ^ b[6])
        | (a[7] ^ b[7]);
    x == 0
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

/// `acc + a * b + c`, as eight limbs and a carry word.
pub fn mul_add_row(acc: &[u32; 8], a: &[u32; 8], b: u32, c: u32) -> ([u32; 8], u32) {
    let (r0, c0) = mul_add2(a[0], b, acc[0], c);
    let (r1, c1) = mul_add2(a[1], b, acc[1], c0);
    let (r2, c2) = mul_add2(a[2], b, acc[2], c1);
    let (r3, c3) = mul_add2(a[3], b, acc[3], c2);
    let (r4, c4) = mul_add2(a[4], b, acc[4], c3);
    let (r5, c5) = mul_add2(a[5], b, acc[5], c4);
    let (r6, c6) = mul_add2(a[6], b, acc[6], c5);
    let (r7, c7) = mul_add2(a[7], b, acc[7], c6);
    ([r0, r1, r2, r3, r4, r5, r6, r7], c7)
}

/// The end of the Montgomery reduction by `2^S`: the signed nine-limb value `(r, c)`, a
/// multiple of `2^S`, is divided by `2^S` and brought to `[0, m)` by adding or subtracting `m`.
pub fn redc_tail<const S: u32>(r: &[u32; 8], c: u32, m: &[u32; 8]) -> [u32; 8] {
    let low = shr_low::<S>(r, c);
    let top = c >> S;
    let neg = (c >> 31) == 1;
    select8(neg, &add8(&low, m), &cond_sub(&low, top != 0, m))
}

/// `(u * f + v * g) / 2^S` modulo `m`, for signed words `f` and `g` with
/// `|f| + |g| <= 2^S` and `0 < S <= 29`; `ninv` is `-1 / m` modulo `2^32`. The shift is `K`
/// in a round and the number of last steps after them.
#[inline(always)]
pub fn lin_comb_redc<const S: u32>(
    u: &[u32; 8],
    v: &[u32; 8],
    f: u32,
    g: u32,
    m: &[u32; 8],
    ninv: u32,
) -> [u32; 8] {
    let (r, c) = lin_comb(u, v, f, g);
    let q = r[0].wrapping_mul(ninv) & ((1u32 << S) - 1);
    let (s, hi) = mul_add_row(&r, m, q, 0);
    redc_tail::<S>(&s, hi.wrapping_add(c), m)
}

/// `±(u * f + v * g) / 2^K` modulo `m`, negated when `neg` is set.
#[inline(always)]
pub fn cof_row(
    u: &[u32; 8],
    v: &[u32; 8],
    f: u32,
    g: u32,
    neg: bool,
    m: &[u32; 8],
    ninv: u32,
) -> [u32; 8] {
    lin_comb_redc::<K>(
        u,
        v,
        select(neg, 0u32.wrapping_sub(f), f),
        select(neg, 0u32.wrapping_sub(g), g),
        m,
        ninv,
    )
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
// Rounds
// ---------------------------------------------------------------------------

/// The state of the algorithm: the operands `a`, `b` and their cofactors `u`, `v`.
#[derive(Clone, Copy)]
pub struct State {
    pub a: [u32; 8],
    pub u: [u32; 8],
    pub b: [u32; 8],
    pub v: [u32; 8],
}

/// One round: the approximations are read from the operands, the inner loop runs on words,
/// and the transition matrix is applied to the operands and to the cofactors.
#[inline(always)]
pub fn round(m: &[u32; 8], ninv: u32, s: &State) -> State {
    // the top of `a | b` is the top of the longer operand
    let ab = or8(&s.a, &s.b);
    let t = inner(approx_top(&ab, &s.a), approx_top(&ab, &s.b));
    let (a1, na) = apply_row(&s.a, &s.b, t.f0, t.g0);
    let (b1, nb) = apply_row(&s.a, &s.b, t.f1, t.g1);
    State {
        a: a1,
        u: cof_row(&s.u, &s.v, t.f0, t.g0, na, m, ninv),
        b: b1,
        v: cof_row(&s.u, &s.v, t.f1, t.g1, nb, m, ninv),
    }
}

/// The quotient `x / y` modulo the odd modulus `m`, for `x, y < m`, by `rounds` rounds of
/// Pornin's algorithm followed by `T` steps on single words; `ninv` is `-1 / m` modulo
/// `2^32`. The result is zero if `y` is not invertible. The run is that of an inversion, with
/// the cofactor `u` started at `x` instead of 1.
///
/// For a modulus of `l` bits, the schedule must satisfy `0 < T <= 29`,
/// `15 * rounds + T >= 2 * l - 2`, which is the number of steps after which `b` is the gcd,
/// and `15 * rounds + 33 >= 2 * l`, for the operands to fit in a word after the rounds
/// (unless `a` is zero, and then the steps do not depend on `b`).
pub fn pornin_div<const T: u32>(
    m: &[u32; 8],
    ninv: u32,
    rounds: u32,
    x: &[u32; 8],
    y: &[u32; 8],
) -> [u32; 8] {
    let mut s = State {
        a: *y,
        u: *x,
        b: *m,
        v: [0, 0, 0, 0, 0, 0, 0, 0],
    };
    let mut i = 0u32;
    while i < rounds {
        s = round(m, ninv, &s);
        i += 1;
    }
    let t = tail::<T>(s.a[0], s.b[0]);
    // only `v` is needed, and `b` is known to be nonnegative: there is no sign to fix
    let v = lin_comb_redc::<T>(&s.u, &s.v, t.f1, t.g1, m, ninv);
    // the final `b`: the word the last steps end on, in place of the low limb of `b`
    let b = [t.b, s.b[1], s.b[2], s.b[3], s.b[4], s.b[5], s.b[6], s.b[7]];
    select8(
        eq8(&b, &[1, 0, 0, 0, 0, 0, 0, 0]),
        &v,
        &[0, 0, 0, 0, 0, 0, 0, 0],
    )
}

/// The inverse of `y < m` modulo the odd modulus `m`: the quotient of 1 by `y`, with the
/// schedule of `pornin_div`. The result is zero if `y` is not invertible.
pub fn pornin_inv<const T: u32>(m: &[u32; 8], ninv: u32, rounds: u32, y: &[u32; 8]) -> [u32; 8] {
    pornin_div::<T>(m, ninv, rounds, &[1, 0, 0, 0, 0, 0, 0, 0], y)
}

// ---------------------------------------------------------------------------
// The field of integers modulo 2^255 - 19
// ---------------------------------------------------------------------------

/// The modulus `2^255 - 19`.
pub const P: [u32; 8] = [
    0xFFFFFFED, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0x7FFFFFFF,
];

/// `-1 / p` modulo `2^32`.
pub const NINV: u32 = 0x286BCA1B;

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

/// Ten limbs of 26 and 25 bits from the 255 low bits of eight 32-bit limbs.
pub fn unpack(y: &[u32; 8]) -> [u32; 10] {
    [
        y[0] & MASK26,
        ((y[0] >> 26).wrapping_add(y[1] << 6)) & MASK25,
        ((y[1] >> 19).wrapping_add(y[2] << 13)) & MASK26,
        ((y[2] >> 13).wrapping_add(y[3] << 19)) & MASK25,
        y[3] >> 6,
        y[4] & MASK25,
        ((y[4] >> 25).wrapping_add(y[5] << 7)) & MASK26,
        ((y[5] >> 19).wrapping_add(y[6] << 13)) & MASK25,
        ((y[6] >> 12).wrapping_add(y[7] << 20)) & MASK26,
        (y[7] >> 6) & MASK25,
    ]
}

/// The inverse of a field element modulo `2^255 - 19`, on ten limbs of 25.5 bits; the
/// inverse of zero is zero. The limbs of the input are below `2^26` at even positions and
/// below `2^25 + 2^18` at odd ones, those of the result are below `2^26` and `2^25`.
pub fn invert(z: &[u32; 10]) -> [u32; 10] {
    unpack(&pornin_inv::<TAIL>(&P, NINV, ROUNDS, &freeze(z)))
}

/// The quotient `x / z` of two field elements modulo `2^255 - 19`, on ten limbs of 25.5
/// bits; a quotient by zero is zero. The limbs of the inputs are below `2^26` at even
/// positions and below `2^25 + 2^18` at odd ones, those of the result are below `2^26` and
/// `2^25`. This is one run of the binary gcd, without the multiplication that
/// `x * invert(z)` needs.
pub fn divide(x: &[u32; 10], z: &[u32; 10]) -> [u32; 10] {
    unpack(&pornin_div::<TAIL>(
        &P,
        NINV,
        ROUNDS,
        &freeze(x),
        &freeze(z),
    ))
}
