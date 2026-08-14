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
    level_params.iter().copied().zip(us.iter().cloned()).collect()
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

pub fn is_def_eq(l1: &Level, l2: &Level) -> bool {
    leq(l1, l2, 0) && leq(l2, l1, 0)
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
}
