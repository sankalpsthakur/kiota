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
