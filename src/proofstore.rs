//! Released theorem proofs, kept on disk instead of in memory.
//!
//! After a theorem is checked its proof is read again only by
//! `unfold_delta`, when a comparison unfolds the theorem the way Lean's
//! `is_delta` does; mathlib needs that for a handful of declarations in
//! hundreds of thousands. Keeping every proof in memory cost about 2.6 GB
//! of the 6.95 GB resident at 300k mathlib declarations. So the parser
//! serializes each proof here when it releases it, and the checker reads
//! it back on demand.
//!
//! A blob is the proof's DAG in post-order with every shared node written
//! once; reading it back re-interns each node, so a reloaded proof is the
//! same term as the released one. Each blob carries a hash of its bytes
//! that is verified on reload: a mismatch is an error, never a term. On
//! Unix the file is unlinked as soon as it is open, so nothing is left
//! behind however the process ends.

use crate::expr::{self, BinderInfo, Expr, ExprData, Lit};
use crate::level::{self, Level, LevelData};
use rustc_hash::{FxHashMap, FxHasher};
use std::cell::{Cell, RefCell};
use std::fs::File;
use std::hash::Hasher;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::PathBuf;

struct Entry {
    offset: u64,
    len: u32,
    hash: u64,
}

pub struct ProofStore {
    file: RefCell<Option<File>>,
    path: PathBuf,
    index: RefCell<FxHashMap<u32, Entry>>,
    /// Proofs read back during this run; a reloaded proof is wanted again
    /// by every later unfolding of the same theorem.
    loaded: RefCell<FxHashMap<u32, Expr>>,
    bytes: Cell<u64>,
    loads: Cell<u64>,
}

impl Default for ProofStore {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofStore {
    pub fn new() -> Self {
        thread_local! {
            static SERIAL: Cell<u64> = const { Cell::new(0) };
        }
        let serial = SERIAL.with(|s| {
            let v = s.get();
            s.set(v + 1);
            v
        });
        let path = std::env::temp_dir().join(format!(
            "kiota-proofs-{}-{serial}.bin",
            std::process::id()
        ));
        ProofStore {
            file: RefCell::new(None),
            path,
            index: RefCell::new(FxHashMap::default()),
            loaded: RefCell::new(FxHashMap::default()),
            bytes: Cell::new(0),
            loads: Cell::new(0),
        }
    }

    /// Theorems stored so far.
    pub fn stored(&self) -> usize {
        self.index.borrow().len()
    }

    /// Bytes written so far.
    pub fn bytes(&self) -> u64 {
        self.bytes.get()
    }

    /// Proofs read back so far (first reads only; later ones are in memory).
    pub fn loads(&self) -> u64 {
        self.loads.get()
    }

    fn open(&self) -> io::Result<()> {
        if self.file.borrow().is_some() {
            return Ok(());
        }
        let f = File::options()
            .read(true)
            .write(true)
            .create_new(true)
            .open(&self.path)?;
        #[cfg(unix)]
        {
            // The open descriptor keeps the file; the name goes away now.
            let _ = std::fs::remove_file(&self.path);
        }
        *self.file.borrow_mut() = Some(f);
        Ok(())
    }

    /// Write `value`, the proof of theorem `name`, to the store. An `Err`
    /// means nothing was recorded: the caller keeps the proof in memory.
    pub fn store(&self, name: u32, value: &Expr) -> io::Result<()> {
        self.open()?;
        let bytes = encode(value);
        let hash = hash_bytes(&bytes);
        let mut guard = self.file.borrow_mut();
        let f = guard.as_mut().expect("opened above");
        let offset = f.seek(SeekFrom::End(0))?;
        f.write_all(&bytes)?;
        let len = u32::try_from(bytes.len())
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "proof over 4 GB"))?;
        self.index
            .borrow_mut()
            .insert(name, Entry { offset, len, hash });
        self.bytes.set(self.bytes.get() + bytes.len() as u64);
        Ok(())
    }

    /// The proof of theorem `name`, if it was stored. `Err` is a damaged
    /// blob (hash mismatch or malformed), reported as an error by the caller.
    pub fn load(&self, name: u32) -> Result<Option<Expr>, String> {
        if let Some(e) = self.loaded.borrow().get(&name) {
            return Ok(Some(e.clone()));
        }
        let (offset, len, hash) = match self.index.borrow().get(&name) {
            Some(e) => (e.offset, e.len, e.hash),
            None => return Ok(None),
        };
        let mut bytes = vec![0u8; len as usize];
        {
            let mut guard = self.file.borrow_mut();
            let f = guard
                .as_mut()
                .ok_or_else(|| "proof store: no file".to_string())?;
            f.seek(SeekFrom::Start(offset))
                .and_then(|_| f.read_exact(&mut bytes))
                .map_err(|e| format!("proof store: read failed: {e}"))?;
        }
        if hash_bytes(&bytes) != hash {
            return Err(format!(
                "proof store: stored proof of theorem {name} does not hash to what was written"
            ));
        }
        let e = decode(&bytes).map_err(|m| format!("proof store: {m}"))?;
        self.loads.set(self.loads.get() + 1);
        self.loaded.borrow_mut().insert(name, e.clone());
        Ok(Some(e))
    }

    /// Test only: damage one byte of a stored blob through the descriptor.
    #[cfg(test)]
    fn corrupt(&self, name: u32) {
        let (offset, len) = {
            let index = self.index.borrow();
            let e = index.get(&name).expect("stored");
            (e.offset, e.len)
        };
        let mut guard = self.file.borrow_mut();
        let f = guard.as_mut().expect("opened");
        let at = offset + (len as u64) / 2;
        let mut b = [0u8; 1];
        f.seek(SeekFrom::Start(at)).unwrap();
        f.read_exact(&mut b).unwrap();
        b[0] ^= 0x55;
        f.seek(SeekFrom::Start(at)).unwrap();
        f.write_all(&b).unwrap();
    }
}

impl Drop for ProofStore {
    fn drop(&mut self) {
        if self.file.borrow().is_some() {
            let _ = std::fs::remove_file(&self.path);
        }
    }
}

fn hash_bytes(bytes: &[u8]) -> u64 {
    let mut h = FxHasher::default();
    h.write(bytes);
    h.write_usize(bytes.len());
    h.finish()
}

// ---------------- encoding ----------------

const T_BVAR: u8 = 0;
const T_SORT: u8 = 1;
const T_CONST: u8 = 2;
const T_APP: u8 = 3;
const T_LAM: u8 = 4;
const T_PI: u8 = 5;
const T_LET: u8 = 6;
const T_PROJ: u8 = 7;
const T_NAT: u8 = 8;
const T_STR: u8 = 9;

const L_ZERO: u8 = 0;
const L_SUCC: u8 = 1;
const L_MAX: u8 = 2;
const L_IMAX: u8 = 3;
const L_PARAM: u8 = 4;

fn put_varint(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(b);
            return;
        }
        out.push(b | 0x80);
    }
}

fn binder_byte(bi: BinderInfo) -> u8 {
    match bi {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}

fn put_level(out: &mut Vec<u8>, l: &Level) {
    match &**l {
        LevelData::Zero => out.push(L_ZERO),
        LevelData::Succ(a) => {
            out.push(L_SUCC);
            put_level(out, a);
        }
        LevelData::Max(a, b) => {
            out.push(L_MAX);
            put_level(out, a);
            put_level(out, b);
        }
        LevelData::IMax(a, b) => {
            out.push(L_IMAX);
            put_level(out, a);
            put_level(out, b);
        }
        LevelData::Param(n) => {
            out.push(L_PARAM);
            put_varint(out, *n as u64);
        }
    }
}

/// The DAG of `root` in post-order, shared nodes once, children by index.
pub fn encode(root: &Expr) -> Vec<u8> {
    let mut index: FxHashMap<usize, u32> = FxHashMap::default();
    let mut order: Vec<Expr> = Vec::new();
    // (node, children pushed)
    let mut stack: Vec<(Expr, bool)> = vec![(root.clone(), false)];
    while let Some((e, expanded)) = stack.pop() {
        let id = expr::identity(&e);
        if index.contains_key(&id) {
            continue;
        }
        if expanded {
            index.insert(id, order.len() as u32);
            order.push(e);
            continue;
        }
        stack.push((e.clone(), true));
        match &**e {
            ExprData::App(f, a) => {
                stack.push((a.clone(), false));
                stack.push((f.clone(), false));
            }
            ExprData::Lam(_, t, b) | ExprData::Pi(_, t, b) => {
                stack.push((b.clone(), false));
                stack.push((t.clone(), false));
            }
            ExprData::Let(t, v, b) => {
                stack.push((b.clone(), false));
                stack.push((v.clone(), false));
                stack.push((t.clone(), false));
            }
            ExprData::Proj(_, _, v) => stack.push((v.clone(), false)),
            ExprData::BVar(_) | ExprData::Sort(_) | ExprData::Const(_, _) | ExprData::Lit(_) => {}
        }
    }
    let mut out = Vec::new();
    put_varint(&mut out, order.len() as u64);
    let at = |e: &Expr| index[&expr::identity(e)] as u64;
    for e in &order {
        match &***e {
            ExprData::BVar(i) => {
                out.push(T_BVAR);
                put_varint(&mut out, *i as u64);
            }
            ExprData::Sort(l) => {
                out.push(T_SORT);
                put_level(&mut out, l);
            }
            ExprData::Const(n, us) => {
                out.push(T_CONST);
                put_varint(&mut out, *n as u64);
                put_varint(&mut out, us.len() as u64);
                for u in us.iter() {
                    put_level(&mut out, u);
                }
            }
            ExprData::App(f, a) => {
                out.push(T_APP);
                put_varint(&mut out, at(f));
                put_varint(&mut out, at(a));
            }
            ExprData::Lam(bi, t, b) | ExprData::Pi(bi, t, b) => {
                out.push(if matches!(&***e, ExprData::Lam(..)) { T_LAM } else { T_PI });
                out.push(binder_byte(*bi));
                put_varint(&mut out, at(t));
                put_varint(&mut out, at(b));
            }
            ExprData::Let(t, v, b) => {
                out.push(T_LET);
                put_varint(&mut out, at(t));
                put_varint(&mut out, at(v));
                put_varint(&mut out, at(b));
            }
            ExprData::Proj(s, i, v) => {
                out.push(T_PROJ);
                put_varint(&mut out, *s as u64);
                put_varint(&mut out, *i as u64);
                put_varint(&mut out, at(v));
            }
            ExprData::Lit(Lit::Nat(n)) => {
                out.push(T_NAT);
                let bytes = n.to_bytes_le();
                put_varint(&mut out, bytes.len() as u64);
                out.extend_from_slice(&bytes);
            }
            ExprData::Lit(Lit::Str(s)) => {
                out.push(T_STR);
                put_varint(&mut out, s.len() as u64);
                out.extend_from_slice(s.as_bytes());
            }
        }
    }
    out
}

struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn byte(&mut self) -> Result<u8, String> {
        let b = *self
            .bytes
            .get(self.pos)
            .ok_or_else(|| "truncated".to_string())?;
        self.pos += 1;
        Ok(b)
    }

    fn varint(&mut self) -> Result<u64, String> {
        let mut v = 0u64;
        let mut shift = 0u32;
        loop {
            let b = self.byte()?;
            if shift >= 64 {
                return Err("varint too long".into());
            }
            v |= ((b & 0x7f) as u64) << shift;
            if b & 0x80 == 0 {
                return Ok(v);
            }
            shift += 7;
        }
    }

    fn u32(&mut self) -> Result<u32, String> {
        u32::try_from(self.varint()?).map_err(|_| "value over 32 bits".to_string())
    }

    fn slice(&mut self, len: usize) -> Result<&'a [u8], String> {
        let end = self
            .pos
            .checked_add(len)
            .filter(|&e| e <= self.bytes.len())
            .ok_or_else(|| "truncated".to_string())?;
        let s = &self.bytes[self.pos..end];
        self.pos = end;
        Ok(s)
    }

    fn level(&mut self, depth: u32) -> Result<Level, String> {
        if depth > 10_000 {
            return Err("level too deep".into());
        }
        Ok(match self.byte()? {
            L_ZERO => level::zero(),
            L_SUCC => level::succ(self.level(depth + 1)?),
            L_MAX => {
                let a = self.level(depth + 1)?;
                level::max(a, self.level(depth + 1)?)
            }
            L_IMAX => {
                let a = self.level(depth + 1)?;
                level::imax(a, self.level(depth + 1)?)
            }
            L_PARAM => level::param(self.u32()?),
            t => return Err(format!("unknown level tag {t}")),
        })
    }

    fn binder(&mut self) -> Result<BinderInfo, String> {
        Ok(match self.byte()? {
            0 => BinderInfo::Default,
            1 => BinderInfo::Implicit,
            2 => BinderInfo::StrictImplicit,
            3 => BinderInfo::InstImplicit,
            b => return Err(format!("unknown binder info {b}")),
        })
    }
}

/// Rebuild a term written by `encode`, re-interning every node.
pub fn decode(bytes: &[u8]) -> Result<Expr, String> {
    let mut r = Reader { bytes, pos: 0 };
    let count = r.varint()?;
    if count == 0 {
        return Err("empty proof".into());
    }
    let mut nodes: Vec<Expr> = Vec::new();
    let node = |nodes: &Vec<Expr>, i: u64| -> Result<Expr, String> {
        nodes
            .get(usize::try_from(i).map_err(|_| "bad reference".to_string())?)
            .cloned()
            .ok_or_else(|| "reference to a later node".to_string())
    };
    for _ in 0..count {
        let e = match r.byte()? {
            T_BVAR => expr::bvar(r.u32()?),
            T_SORT => expr::sort(r.level(0)?),
            T_CONST => {
                let n = r.u32()?;
                let k = r.varint()?;
                let mut us = Vec::new();
                for _ in 0..k {
                    us.push(r.level(0)?);
                }
                expr::const_(n, us)
            }
            T_APP => {
                let f = node(&nodes, r.varint()?)?;
                let a = node(&nodes, r.varint()?)?;
                expr::app(f, a)
            }
            t @ (T_LAM | T_PI) => {
                let bi = r.binder()?;
                let ty = node(&nodes, r.varint()?)?;
                let body = node(&nodes, r.varint()?)?;
                if t == T_LAM {
                    expr::lam(bi, ty, body)
                } else {
                    expr::pi(bi, ty, body)
                }
            }
            T_LET => {
                let ty = node(&nodes, r.varint()?)?;
                let val = node(&nodes, r.varint()?)?;
                let body = node(&nodes, r.varint()?)?;
                expr::let_(ty, val, body)
            }
            T_PROJ => {
                let s = r.u32()?;
                let i = r.u32()?;
                let v = node(&nodes, r.varint()?)?;
                expr::proj(s, i, v)
            }
            T_NAT => {
                let len = r.varint()? as usize;
                let b = r.slice(len)?;
                expr::lit_nat(num_bigint::BigUint::from_bytes_le(b))
            }
            T_STR => {
                let len = r.varint()? as usize;
                let b = r.slice(len)?;
                let s = std::str::from_utf8(b).map_err(|_| "string is not UTF-8".to_string())?;
                expr::lit_str(s)
            }
            t => return Err(format!("unknown node tag {t}")),
        };
        nodes.push(e);
    }
    if r.pos != bytes.len() {
        return Err("trailing bytes".into());
    }
    Ok(nodes.pop().expect("count > 0"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;

    fn fixture() -> Expr {
        let u = level::param(0);
        let nat = expr::const_(7, vec![]);
        let f = expr::const_(8, vec![level::succ(u.clone()), level::max(u.clone(), level::zero())]);
        // Shared subterm `f 5` used three times.
        let five = expr::app(f.clone(), expr::lit_nat(5u32.into()));
        let big = expr::lit_nat(num_bigint::BigUint::from(1u8) << 200u32);
        let body = expr::let_(
            nat.clone(),
            expr::app(five.clone(), big),
            expr::proj(3, 1, expr::app(expr::app(five.clone(), five.clone()), expr::bvar(0))),
        );
        let inner = expr::lam(
            BinderInfo::InstImplicit,
            expr::sort(level::imax(u.clone(), level::succ(level::zero()))),
            expr::app(body, expr::lit_str("héllo")),
        );
        expr::pi(BinderInfo::Implicit, expr::bvar(3), expr::app(inner, expr::bvar(1)))
    }

    #[test]
    fn a_proof_round_trips_through_the_encoding_as_the_same_term() {
        let e = fixture();
        let bytes = encode(&e);
        let back = decode(&bytes).unwrap();
        assert!(Rc::ptr_eq(&e, &back), "re-interned to the same node");
        // Sharing is kept: `f 5` is written once, so the blob is small.
        assert!(bytes.len() < 120, "{} bytes", bytes.len());
    }

    #[test]
    fn damaged_or_malformed_blobs_are_errors_not_terms() {
        let e = fixture();
        let bytes = encode(&e);
        assert!(decode(&bytes[..bytes.len() - 1]).is_err(), "truncated");
        let mut extra = bytes.clone();
        extra.push(0);
        assert!(decode(&extra).is_err(), "trailing");
        assert!(decode(&[]).is_err());
        assert!(decode(&[1, 99]).is_err(), "unknown tag");
        // A reference to a node not yet built.
        assert!(decode(&[2, T_APP, 1, 1, T_BVAR, 0]).is_err());
    }

    #[test]
    fn stored_proofs_come_back_and_corruption_is_caught() {
        let store = ProofStore::new();
        let e = fixture();
        let small = expr::const_(1, vec![]);
        store.store(4, &e).unwrap();
        store.store(5, &small).unwrap();
        assert_eq!(store.stored(), 2);
        assert!(store.bytes() > 0);
        assert!(store.load(6).unwrap().is_none(), "never stored");
        assert!(Rc::ptr_eq(&store.load(4).unwrap().unwrap(), &e));
        assert!(Rc::ptr_eq(&store.load(5).unwrap().unwrap(), &small));
        assert_eq!(store.loads(), 2);
        assert!(Rc::ptr_eq(&store.load(4).unwrap().unwrap(), &e));
        assert_eq!(store.loads(), 2, "second read is from memory");
        let other = ProofStore::new();
        other.store(4, &e).unwrap();
        other.corrupt(4);
        let r = other.load(4);
        assert!(matches!(r, Err(ref m) if m.contains("hash")), "{r:?}");
    }
}
