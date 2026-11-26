//! Pornin's optimized binary GCD (<https://eprint.iacr.org/2020/972>) for inversion and
//! division modulo an odd modulus of four 64-bit limbs, with 31 inner iterations per round,
//! and its use for the field of integers modulo `2^255 - 19` on five 51-bit limbs.
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
//! `Bingcd.Limbs.Curve25519.div` and `inv` in `lean/Proofs/Helpers/Bingcd/`, function by
//! function, at 64-bit words: its extraction by Aeneas is proved equal to them.
//!
//! There is no branch on the operands: decisions are turned into masks and selections, and
//! the loops have fixed lengths.

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

/// `a + b + c`, as a word and a carry.
#[inline(always)]
pub fn addc(a: u64, b: u64, c: bool) -> (u64, bool) {
    let s = (a as u128) + (b as u128) + (c as u128);
    (s as u64, (s >> 64) != 0)
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

/// `a * b + c + d`, as a low word and a high word.
#[inline(always)]
pub fn mul_add2(a: u64, b: u64, c: u64, d: u64) -> (u64, u64) {
    let p = (a as u128) * (b as u128) + (c as u128) + (d as u128);
    (p as u64, (p >> 64) as u64)
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

/// `a + b` modulo `2^256`.
pub fn add4(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let (r0, c0) = addc(a[0], b[0], false);
    let (r1, c1) = addc(a[1], b[1], c0);
    let (r2, c2) = addc(a[2], b[2], c1);
    let (r3, _) = addc(a[3], b[3], c2);
    [r0, r1, r2, r3]
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

/// Whether `a = b`.
pub fn eq4(a: &[u64; 4], b: &[u64; 4]) -> bool {
    let x = (a[0] ^ b[0]) | (a[1] ^ b[1]) | (a[2] ^ b[2]) | (a[3] ^ b[3]);
    x == 0
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

/// `acc + a * b + c`, as four limbs and a carry word.
pub fn mul_add_row(acc: &[u64; 4], a: &[u64; 4], b: u64, c: u64) -> ([u64; 4], u64) {
    let (r0, c0) = mul_add2(a[0], b, acc[0], c);
    let (r1, c1) = mul_add2(a[1], b, acc[1], c0);
    let (r2, c2) = mul_add2(a[2], b, acc[2], c1);
    let (r3, c3) = mul_add2(a[3], b, acc[3], c2);
    ([r0, r1, r2, r3], c3)
}

/// The end of the Montgomery reduction by `2^S`: the signed five-limb value `(r, c)`, a
/// multiple of `2^S`, is divided by `2^S` and brought to `[0, m)` by adding or subtracting `m`.
pub fn redc_tail<const S: u32>(r: &[u64; 4], c: u64, m: &[u64; 4]) -> [u64; 4] {
    let low = shr_low::<S>(r, c);
    let top = c >> S;
    let neg = (c >> 63) == 1;
    select4(neg, &add4(&low, m), &cond_sub(&low, top != 0, m))
}

/// `(u * f + v * g) / 2^S` modulo `m`, for signed words `f` and `g` with
/// `|f| + |g| <= 2^S` and `0 < S <= 61`; `ninv` is `-1 / m` modulo `2^64`. The shift is `K`
/// in a round and the number of last steps after them.
#[inline(always)]
pub fn lin_comb_redc<const S: u32>(
    u: &[u64; 4],
    v: &[u64; 4],
    f: u64,
    g: u64,
    m: &[u64; 4],
    ninv: u64,
) -> [u64; 4] {
    let (r, c) = lin_comb(u, v, f, g);
    let q = r[0].wrapping_mul(ninv) & ((1u64 << S) - 1);
    let (s, hi) = mul_add_row(&r, m, q, 0);
    redc_tail::<S>(&s, hi.wrapping_add(c), m)
}

/// `±(u * f + v * g) / 2^K` modulo `m`, negated when `neg` is set.
#[inline(always)]
pub fn cof_row(
    u: &[u64; 4],
    v: &[u64; 4],
    f: u64,
    g: u64,
    neg: bool,
    m: &[u64; 4],
    ninv: u64,
) -> [u64; 4] {
    lin_comb_redc::<K>(
        u,
        v,
        select(neg, 0u64.wrapping_sub(f), f),
        select(neg, 0u64.wrapping_sub(g), g),
        m,
        ninv,
    )
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
// Rounds
// ---------------------------------------------------------------------------

/// The state of the algorithm: the operands `a`, `b` and their cofactors `u`, `v`.
#[derive(Clone, Copy)]
pub struct State {
    pub a: [u64; 4],
    pub u: [u64; 4],
    pub b: [u64; 4],
    pub v: [u64; 4],
}

/// One round: the approximations are read from the operands, the inner loop runs on words,
/// and the transition matrix is applied to the operands and to the cofactors.
// `round`, `cof_row` and `lin_comb_redc` are inlined together: this measured about 50 ns
// faster per inversion, while inlining only some of the three was slower than none.
#[inline(always)]
pub fn round(m: &[u64; 4], ninv: u64, s: &State) -> State {
    // the top of `a | b` is the top of the longer operand
    let ab = or4(&s.a, &s.b);
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
/// `2^64`. The result is zero if `y` is not invertible. The run is that of an inversion, with
/// the cofactor `u` started at `x` instead of 1.
///
/// For a modulus of `l` bits, the schedule must satisfy `0 < T <= 61`,
/// `31 * rounds + T >= 2 * l - 2`, which is the number of steps after which `b` is the gcd,
/// and `31 * rounds + 65 >= 2 * l`, for the operands to fit in a word after the rounds
/// (unless `a` is zero, and then the steps do not depend on `b`).
pub fn pornin_div<const T: u32>(
    m: &[u64; 4],
    ninv: u64,
    rounds: u32,
    x: &[u64; 4],
    y: &[u64; 4],
) -> [u64; 4] {
    let mut s = State {
        a: *y,
        u: *x,
        b: *m,
        v: [0, 0, 0, 0],
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
    let b = [t.b, s.b[1], s.b[2], s.b[3]];
    select4(eq4(&b, &[1, 0, 0, 0]), &v, &[0, 0, 0, 0])
}

/// The inverse of `y < m` modulo the odd modulus `m`: the quotient of 1 by `y`, with the
/// schedule of `pornin_div`. The result is zero if `y` is not invertible.
pub fn pornin_inv<const T: u32>(m: &[u64; 4], ninv: u64, rounds: u32, y: &[u64; 4]) -> [u64; 4] {
    pornin_div::<T>(m, ninv, rounds, &[1, 0, 0, 0], y)
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

/// `-1 / p` modulo `2^64`.
pub const NINV: u64 = 0x86BCA1AF286BCA1B;

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

/// Five 51-bit limbs from the 255 low bits of four 64-bit limbs.
pub fn unpack(y: &[u64; 4]) -> [u64; 5] {
    [
        y[0] & MASK51,
        ((y[0] >> 51).wrapping_add(y[1] << 13)) & MASK51,
        ((y[1] >> 38).wrapping_add(y[2] << 26)) & MASK51,
        ((y[2] >> 25).wrapping_add(y[3] << 39)) & MASK51,
        (y[3] >> 12) & MASK51,
    ]
}

/// The inverse of a field element modulo `2^255 - 19`, on five 51-bit limbs; the inverse of
/// zero is zero. The limbs of the input are at most `2^51 + 2^23`, those of the result are
/// below `2^51`.
pub fn invert(z: &[u64; 5]) -> [u64; 5] {
    unpack(&pornin_inv::<TAIL>(&P, NINV, ROUNDS, &freeze(z)))
}

/// The quotient `x / z` of two field elements modulo `2^255 - 19`, on five 51-bit limbs; a
/// quotient by zero is zero. The limbs of the inputs are at most `2^51 + 2^23`, those of the
/// result are below `2^51`. This is one run of the binary gcd, without the multiplication
/// that `x * invert(z)` needs.
pub fn divide(x: &[u64; 5], z: &[u64; 5]) -> [u64; 5] {
    unpack(&pornin_div::<TAIL>(
        &P,
        NINV,
        ROUNDS,
        &freeze(x),
        &freeze(z),
    ))
}
