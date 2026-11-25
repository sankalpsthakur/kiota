use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LevelData {
    Zero,
    Succ(Level),
    Max(Level, Level),
    IMax(Level, Level),
    Param(u32), // name index
}

pub type Level = Rc<LevelData>;

pub fn zero() -> Level {
    Rc::new(LevelData::Zero)
}
pub fn succ(l: Level) -> Level {
    Rc::new(LevelData::Succ(l))
}
fn is_explicit(l: &Level) -> bool {
    match &**l {
        LevelData::Zero => true,
        LevelData::Succ(a) => is_explicit(a),
        _ => false,
    }
}

fn explicit_offset(l: &Level) -> u32 {
    let mut n = 0;
    let mut cur = l;
    while let LevelData::Succ(a) = &**cur {
        n += 1;
        cur = a;
    }
    n
}

/// Peel `succ^k(base)` into `(base, k)`.
fn to_offset(l: &Level) -> (Level, u32) {
    let mut k = 0;
    let mut cur = l.clone();
    while let LevelData::Succ(a) = &*cur {
        k += 1;
        cur = a.clone();
    }
    (cur, k)
}

/// True when `l` cannot be 0 under any parameter assignment.
pub fn is_not_zero(l: &Level) -> bool {
    match &**l {
        LevelData::Zero | LevelData::Param(_) => false,
        LevelData::Succ(_) => true,
        LevelData::Max(a, b) => is_not_zero(a) || is_not_zero(b),
        LevelData::IMax(_, b) => is_not_zero(b),
    }
}

fn is_one(l: &Level) -> bool {
    matches!(&**l, LevelData::Succ(z) if matches!(&**z, LevelData::Zero))
}

/// Lean kernel `mk_max` simplifications (level.cpp).
pub fn max(a: Level, b: Level) -> Level {
    if is_explicit(&a) && is_explicit(&b) {
        return if explicit_offset(&a) >= explicit_offset(&b) {
            a
        } else {
            b
        };
    }
    if a == b {
        return a;
    }
    if is_zero(&a) {
        return b;
    }
    if is_zero(&b) {
        return a;
    }
    if let LevelData::Max(l, r) = &*b {
        if *l == a || *r == a {
            return b;
        }
    }
    if let LevelData::Max(l, r) = &*a {
        if *l == b || *r == b {
            return a;
        }
    }
    let (b1, k1) = to_offset(&a);
    let (b2, k2) = to_offset(&b);
    if b1 == b2 {
        return if k1 > k2 { a } else { b };
    }
    Rc::new(LevelData::Max(a, b))
}

/// Lean kernel `mk_imax` simplifications (level.cpp):
///   imax u 0        = 0
///   imax u (succ v)  = max u (succ v)   (rhs never 0)
///   imax 0 u = imax 1 u = u             (for any u)
///   imax u u        = u
pub fn imax(a: Level, b: Level) -> Level {
    if is_not_zero(&b) {
        return max(a, b);
    }
    if is_zero(&b) {
        return zero();
    }
    if is_zero(&a) || is_one(&a) {
        return b;
    }
    if a == b {
        return a;
    }
    Rc::new(LevelData::IMax(a, b))
}
pub fn param(n: u32) -> Level {
    Rc::new(LevelData::Param(n))
}

pub fn mk_const(n: u64) -> Level {
    let mut l = zero();
    for _ in 0..n {
        l = succ(l);
    }
    l
}

/// Instantiate level params, looked up by their name-index, via `subst`.
pub fn instantiate(l: &Level, subst: &rustc_hash::FxHashMap<u32, Level>) -> Level {
    match &**l {
        LevelData::Zero => l.clone(),
        LevelData::Succ(a) => succ(instantiate(a, subst)),
        LevelData::Max(a, b) => max(instantiate(a, subst), instantiate(b, subst)),
        LevelData::IMax(a, b) => imax(instantiate(a, subst), instantiate(b, subst)),
        LevelData::Param(i) => subst.get(i).cloned().unwrap_or_else(|| l.clone()),
    }
}

pub fn subst_map(level_params: &[u32], us: &[Level]) -> rustc_hash::FxHashMap<u32, Level> {
    level_params
        .iter()
        .copied()
        .zip(us.iter().cloned())
        .collect()
}

/// Decide l1 <= l2 + diff, where params are treated as universally quantified
/// (must hold for every instantiation). Sound for the fragment the kernel needs;
/// may be conservatively strict on some deeply nested imax combinations.
pub fn leq(l1: &Level, l2: &Level, diff: i64) -> bool {
    use LevelData::*;

    if l1 == l2 {
        return diff >= 0;
    }

    if let Succ(a) = &**l1 {
        return leq(a, l2, diff - 1);
    }
    if let Succ(b) = &**l2 {
        return leq(l1, b, diff + 1);
    }
    if let Max(a, b) = &**l1 {
        return leq(a, l2, diff) && leq(b, l2, diff);
    }
    if let Max(a, b) = &**l2 {
        return leq(l1, a, diff) || leq(l1, b, diff);
    }
    if let (IMax(a1, b1), IMax(a2, b2)) = (&**l1, &**l2) {
        // Matching rhs (structurally or by leq): both 0 when that param is 0.
        if b1 == b2 || (leq(b1, b2, 0) && leq(b2, b1, 0)) {
            return leq(
                &max(a1.clone(), b1.clone()),
                &max(a2.clone(), b2.clone()),
                diff,
            );
        }
    }
    if let IMax(a, b) = &**l1 {
        // l1's value is 0 (if b=0) or max(a,b) (otherwise); must hold in both cases.
        return leq(&zero(), l2, diff) && leq(&max(a.clone(), b.clone()), l2, diff);
    }
    if let IMax(a, b) = &**l2 {
        return leq(l1, &zero(), diff) && leq(l1, &max(a.clone(), b.clone()), diff);
    }

    match (&**l1, &**l2) {
        (Zero, Zero) => diff >= 0,
        (Zero, Param(_)) => diff >= 0,
        (Param(_), Zero) => false,
        (Param(a), Param(b)) => a == b && diff >= 0,
        _ => false,
    }
}

/// A level under one choice of which parameters are zero: the maximum of a
/// constant and of `p + k` over parameters `p` that are at least one.
struct MaxPlus {
    konst: u64,
    terms: Vec<(u32, u64)>,
}

impl MaxPlus {
    fn is_zero(&self) -> bool {
        self.konst == 0 && self.terms.is_empty()
    }

    fn join(mut self, other: MaxPlus) -> MaxPlus {
        self.konst = self.konst.max(other.konst);
        for (p, k) in other.terms {
            match self.terms.iter_mut().find(|(q, _)| *q == p) {
                Some((_, k0)) => *k0 = (*k0).max(k),
                None => self.terms.push((p, k)),
            }
        }
        self
    }
}

fn max_plus(l: &Level, zero_params: &[u32]) -> MaxPlus {
    match &**l {
        LevelData::Zero => MaxPlus { konst: 0, terms: Vec::new() },
        LevelData::Param(p) => {
            if zero_params.contains(p) {
                MaxPlus { konst: 0, terms: Vec::new() }
            } else {
                MaxPlus { konst: 0, terms: vec![(*p, 0)] }
            }
        }
        LevelData::Succ(a) => {
            let mut f = max_plus(a, zero_params);
            f.konst += 1;
            for (_, k) in f.terms.iter_mut() {
                *k += 1;
            }
            f
        }
        LevelData::Max(a, b) => max_plus(a, zero_params).join(max_plus(b, zero_params)),
        LevelData::IMax(a, b) => {
            let fb = max_plus(b, zero_params);
            if fb.is_zero() {
                fb
            } else {
                max_plus(a, zero_params).join(fb)
            }
        }
    }
}

fn collect_params(l: &Level, out: &mut Vec<u32>) {
    match &**l {
        LevelData::Zero => {}
        LevelData::Param(p) => {
            if !out.contains(p) {
                out.push(*p);
            }
        }
        LevelData::Succ(a) => collect_params(a, out),
        LevelData::Max(a, b) | LevelData::IMax(a, b) => {
            collect_params(a, out);
            collect_params(b, out);
        }
    }
}

/// Decide `l1 <= l2` under every assignment of natural numbers to the
/// universe parameters, exactly.
///
/// For each choice of which parameters are zero, `imax` becomes `max` or `0`
/// and both sides are maxima of constants and `p + k` terms with `p >= 1`.
/// Then `l1 <= l2` holds for all remaining values iff every `p + a` of `l1`
/// has a `p + b` in `l2` with `b >= a` (otherwise a large `p` separates them)
/// and the constant of `l1` is at most the least value of `l2`, which is
/// attained with every parameter at one.
///
/// The official kernel's `is_geq` is sound but not complete, so anything it
/// admits is admitted here; `leq` above may be strict on nested `imax` and
/// is not a substitute.  With more than twelve parameters this falls back to
/// `leq` on normal forms rather than enumerate.
pub fn leq_all(l1: &Level, l2: &Level) -> bool {
    let mut params = Vec::new();
    collect_params(l1, &mut params);
    collect_params(l2, &mut params);
    if params.len() > 12 {
        return leq(&normalize(l1), &normalize(l2), 0);
    }
    let mut zero_params: Vec<u32> = Vec::with_capacity(params.len());
    for mask in 0u32..(1u32 << params.len()) {
        zero_params.clear();
        for (i, p) in params.iter().enumerate() {
            if mask & (1 << i) != 0 {
                zero_params.push(*p);
            }
        }
        let f1 = max_plus(l1, &zero_params);
        let f2 = max_plus(l2, &zero_params);
        let least2 = f2.terms.iter().map(|(_, k)| k + 1).fold(f2.konst, u64::max);
        if f1.konst > least2 {
            return false;
        }
        for (p, a) in &f1.terms {
            match f2.terms.iter().find(|(q, _)| q == p) {
                Some((_, b)) if b >= a => {}
                _ => return false,
            }
        }
    }
    true
}

pub fn pp(l: &Level) -> String {
    match &**l {
        LevelData::Zero => "0".into(),
        LevelData::Succ(a) => format!("succ({})", pp(a)),
        LevelData::Max(a, b) => format!("max({},{})", pp(a), pp(b)),
        LevelData::IMax(a, b) => format!("imax({},{})", pp(a), pp(b)),
        LevelData::Param(n) => format!("u{n}"),
    }
}

/// Push `succ` through `max` so `succ(max u v)` meets `max (succ v) (succ u)`.
pub fn normalize(l: &Level) -> Level {
    match &**l {
        LevelData::Zero | LevelData::Param(_) => l.clone(),
        LevelData::Succ(a) => {
            let a = normalize(a);
            match &*a {
                LevelData::Max(x, y) => max(succ(x.clone()), succ(y.clone())),
                _ => succ(a),
            }
        }
        LevelData::Max(a, b) => max(normalize(a), normalize(b)),
        LevelData::IMax(a, b) => imax(normalize(a), normalize(b)),
    }
}

pub fn is_def_eq(l1: &Level, l2: &Level) -> bool {
    let a = normalize(l1);
    let b = normalize(l2);
    leq(&a, &b, 0) && leq(&b, &a, 0)
}

pub fn is_zero(l: &Level) -> bool {
    matches!(&**l, LevelData::Zero)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eval(l: &Level, env: &[u64; 3]) -> u64 {
        match &**l {
            LevelData::Zero => 0,
            LevelData::Param(p) => env[*p as usize],
            LevelData::Succ(a) => eval(a, env) + 1,
            LevelData::Max(a, b) => eval(a, env).max(eval(b, env)),
            LevelData::IMax(a, b) => {
                let vb = eval(b, env);
                if vb == 0 { 0 } else { eval(a, env).max(vb) }
            }
        }
    }

    // Raw constructors: `max`/`imax` above simplify, and the comparison must
    // be right on unsimplified terms too.
    fn random_level(seed: &mut u64, depth: u32) -> Level {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let r = (*seed >> 33) % if depth == 0 { 2 } else { 6 };
        match r {
            0 => zero(),
            1 => param(((*seed >> 40) % 3) as u32),
            2 | 3 => succ(random_level(seed, depth - 1)),
            4 => Rc::new(LevelData::Max(random_level(seed, depth - 1), random_level(seed, depth - 1))),
            _ => Rc::new(LevelData::IMax(random_level(seed, depth - 1), random_level(seed, depth - 1))),
        }
    }

    #[test]
    fn leq_all_agrees_with_evaluation_on_small_assignments() {
        // Levels of depth four add at most four to a parameter, so a
        // violated inequality already fails for some value below ten.
        let mut seed = 0x5eed_u64;
        let (mut holds, mut fails) = (0, 0);
        for _ in 0..20_000 {
            let a = random_level(&mut seed, 4);
            let b = random_level(&mut seed, 4);
            let mut brute = true;
            'outer: for x in 0..10u64 {
                for y in 0..10u64 {
                    for z in 0..10u64 {
                        if eval(&a, &[x, y, z]) > eval(&b, &[x, y, z]) {
                            brute = false;
                            break 'outer;
                        }
                    }
                }
            }
            assert_eq!(leq_all(&a, &b), brute, "{} <= {}", pp(&a), pp(&b));
            if brute { holds += 1 } else { fails += 1 }
        }
        assert!(holds > 1000 && fails > 1000, "{holds} hold, {fails} fail");
    }

    #[test]
    fn leq_all_is_never_stricter_than_leq() {
        let mut seed = 0xfeed_u64;
        for _ in 0..20_000 {
            let a = random_level(&mut seed, 4);
            let b = random_level(&mut seed, 4);
            if leq(&normalize(&a), &normalize(&b), 0) {
                assert!(leq_all(&a, &b), "{} <= {}", pp(&a), pp(&b));
            }
        }
    }

    #[test]
    fn leq_all_field_universe_cases() {
        let (u, v) = (param(0), param(1));
        // Type v field in Type u.
        assert!(!leq_all(&succ(succ(v.clone())), &succ(u.clone())));
        // Type u field in Type u.
        assert!(!leq_all(&succ(succ(u.clone())), &succ(u.clone())));
        // Sort u field in Sort (max u v + 1).
        assert!(leq_all(&succ(u.clone()), &succ(max(u.clone(), v.clone()))));
        // Sort u field in Sort (max 1 u): fails at u = 1.
        assert!(!leq_all(&succ(u.clone()), &max(succ(zero()), u.clone())));
        // imax u 0 is always zero.
        assert!(leq_all(&Rc::new(LevelData::IMax(u.clone(), zero())), &zero()));
        assert!(!leq_all(&u, &zero()));
    }

    #[test]
    fn imax_one_param_is_param() {
        let u = param(7);
        let one = succ(zero());
        assert_eq!(imax(one, u.clone()), u);
        assert_eq!(imax(zero(), u.clone()), u);
        assert_eq!(imax(u.clone(), zero()), zero());
        assert!(is_def_eq(&imax(succ(zero()), u.clone()), &u));
    }

    #[test]
    fn imax_two_param_is_not_param() {
        let u = param(7);
        let two = succ(succ(zero()));
        let r = imax(two, u.clone());
        assert_ne!(r, u);
        assert!(!is_def_eq(&r, &u));
    }

    #[test]
    fn imax_succ_rhs_becomes_max() {
        let u = param(3);
        let s = succ(u.clone());
        // imax u (succ u) = max u (succ u) = succ u
        assert_eq!(imax(u.clone(), s.clone()), s);
    }

    #[test]
    fn succ_max_commutes_under_imax() {
        let u = param(1967);
        let v = param(517);
        let w = param(6);
        let lhs = imax(succ(max(u.clone(), v.clone())), w.clone());
        let rhs = imax(max(succ(v), succ(u)), w);
        assert!(is_def_eq(&lhs, &rhs), "{} vs {}", pp(&lhs), pp(&rhs));
    }

    #[test]
    fn max_assoc_comm_under_imax() {
        let u6 = param(6);
        let u22 = param(22);
        let u128 = param(128);
        let lhs = max(u22.clone(), max(u128.clone(), succ(u6.clone())));
        let rhs = max(max(succ(u6), u22), u128);
        assert!(is_def_eq(&lhs, &rhs), "{} vs {}", pp(&lhs), pp(&rhs));
    }
}
