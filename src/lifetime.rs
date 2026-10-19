//! Lifetimes of the export's expression nodes.
//!
//! lean4export shares expressions globally: every `ie` line defines one node
//! by index, and any later line may reference it. The parser therefore kept
//! every node ever read in its index table, so the whole export's DAG stayed
//! in memory for the entire run (main held 8 GB after a third of mathlib). A
//! first pass over the file finds the last line that references each index;
//! the parser then releases an index from its table once that line is behind
//! it. A node stays alive after release only through the environment
//! (declaration types and retained values), which is what the checker needs.
//!
//! Most nodes are referenced only by the declaration that follows them, so
//! they are released in bulk at that declaration ("short-lived"). The rest
//! expire at a known later line ("long-lived"), kept in a list sorted by that
//! line. Releasing an index the parser still needs cannot produce a wrong
//! term: the table slot becomes `None`, and reading it is an error.
//!
//! The same pass records which constant names any expression mentions. A
//! theorem no expression in the export refers to can never be unfolded after
//! its own check, so the parser releases its proof too (see
//! `Parser::release_theorem_value`); a referenced theorem keeps its proof.
use std::io::{BufRead, BufReader, Read};

/// Keys whose numeric value is an expression index inside an `ie` record.
const EXPR_REF_KEYS: &[&[u8]] = &[b"fn", b"arg", b"type", b"body", b"value", b"struct", b"expr"];
/// Keys whose numeric value is an expression index inside a declaration record
/// (`axiom`, `def`, `thm`, `opaque`, `quot`, `inductive` types/ctors/recs/rules).
const DECL_REF_KEYS: &[&[u8]] = &[b"type", b"value", b"rhs"];

pub struct Lifetimes {
    /// Bit `idx`: the node expires at the declaration that follows its
    /// definition (its home declaration).
    short: Vec<u64>,
    /// `(line, idx)` for nodes that expire later, sorted by line.
    long: Vec<(u32, u32)>,
    next_long: usize,
    /// First index defined after the last declaration released.
    group_first: u32,
    /// Bit `n`: some expression node is `const n`.
    referenced_names: Vec<u64>,
    pub lines: u32,
    pub nodes: u32,
}

/// One line of the export, classified by its top-level keys.
#[derive(Debug, PartialEq, Eq)]
pub enum Kind {
    Expr(u32),
    Other,
    Decl,
}

/// Scan the file once and compute every expression index's last reference.
pub fn scan(path: &str) -> std::io::Result<Lifetimes> {
    let file = std::fs::File::open(path)?;
    scan_reader(BufReader::with_capacity(1 << 22, file))
}

pub fn scan_reader<R: Read>(reader: BufReader<R>) -> std::io::Result<Lifetimes> {
    let mut last_ref: Vec<u32> = Vec::new();
    let mut decl_lines: Vec<u32> = Vec::new();
    let mut decl_first: Vec<u32> = Vec::new();
    let mut line_no: u32 = 0;
    let mut refs: Vec<u32> = Vec::new();
    let mut names: Vec<u32> = Vec::new();
    let mut referenced_names: Vec<u64> = Vec::new();
    let mut buf: Vec<u8> = Vec::new();
    let mut reader = reader;
    loop {
        buf.clear();
        if reader.read_until(b'\n', &mut buf)? == 0 {
            break;
        }
        line_no += 1;
        refs.clear();
        names.clear();
        match classify(&buf, &mut refs, &mut names) {
            Kind::Expr(idx) => {
                for &n in &names {
                    let word = n as usize / 64;
                    if word >= referenced_names.len() {
                        referenced_names.resize(word + 1, 0);
                    }
                    referenced_names[word] |= 1u64 << (n % 64);
                }
                let defined = last_ref.len() as u32;
                for &r in &refs {
                    if r < defined {
                        last_ref[r as usize] = line_no;
                    }
                }
                if (idx as usize) >= last_ref.len() {
                    last_ref.resize(idx as usize + 1, 0);
                }
                last_ref[idx as usize] = line_no;
            }
            Kind::Decl => {
                let defined = last_ref.len() as u32;
                for &r in &refs {
                    if r < defined {
                        last_ref[r as usize] = line_no;
                    }
                }
                decl_lines.push(line_no);
                decl_first.push(defined);
            }
            Kind::Other => {}
        }
    }
    let nodes = last_ref.len() as u32;
    let mut short = vec![0u64; (nodes as usize + 63) / 64];
    let mut long: Vec<(u32, u32)> = Vec::new();
    let mut group = 0usize;
    for idx in 0..nodes {
        // The home declaration is the first declaration line after the node.
        while group < decl_first.len() && decl_first[group] <= idx {
            group += 1;
        }
        let home = if group < decl_lines.len() { decl_lines[group] } else { u32::MAX };
        if last_ref[idx as usize] <= home {
            short[idx as usize / 64] |= 1u64 << (idx % 64);
        } else {
            long.push((last_ref[idx as usize], idx));
        }
    }
    drop(last_ref);
    long.sort_unstable();
    Ok(Lifetimes { short, long, next_long: 0, group_first: 0, referenced_names, lines: line_no, nodes })
}

impl Lifetimes {
    /// Called after the parser has handled a declaration line. `defined` is
    /// the parser's table length. Every index that expires at or before this
    /// line is passed to `release`.
    pub fn release_after_decl(&mut self, line: u32, defined: u32, mut release: impl FnMut(u32)) {
        for idx in self.group_first..defined.min(self.nodes) {
            if self.short[idx as usize / 64] >> (idx % 64) & 1 == 1 {
                release(idx);
            }
        }
        self.group_first = defined;
        while self.next_long < self.long.len() && self.long[self.next_long].0 <= line {
            release(self.long[self.next_long].1);
            self.next_long += 1;
        }
    }

    pub fn long_lived(&self) -> usize {
        self.long.len()
    }

    /// Whether any expression node in the export is `const name`.
    pub fn name_referenced(&self, name: u32) -> bool {
        self.referenced_names
            .get(name as usize / 64)
            .map(|w| w >> (name % 64) & 1 == 1)
            .unwrap_or(false)
    }
}

/// Classify one line, collect the expression indices it references and, for
/// an expression record, the constant names it mentions (`const.name`; the
/// only `name` key inside an expression record).
pub fn classify(line: &[u8], refs: &mut Vec<u32>, names: &mut Vec<u32>) -> Kind {
    let mut w = Walker { s: line, i: 0 };
    w.skip_ws();
    if w.peek() != Some(b'{') {
        return Kind::Other;
    }
    // First pass over the top-level keys: the record's kind.
    let mut probe = Walker { s: line, i: w.i };
    let mut kind = Kind::Decl;
    let mut top_keys = 0;
    if probe.walk_object(&mut |key, value| {
        top_keys += 1;
        match key {
            b"ie" => {
                if let Some(n) = value {
                    kind = Kind::Expr(n);
                }
            }
            b"il" | b"in" | b"meta" => kind = Kind::Other,
            _ => {}
        }
    }).is_err()
    {
        return Kind::Other;
    }
    if top_keys == 0 {
        return Kind::Other;
    }
    let keys: &[&[u8]] = match kind {
        Kind::Expr(_) => EXPR_REF_KEYS,
        Kind::Decl => DECL_REF_KEYS,
        Kind::Other => return Kind::Other,
    };
    // Second pass: every numeric value under a reference key, at any depth.
    let is_expr = matches!(kind, Kind::Expr(_));
    let mut deep = Walker { s: line, i: w.i };
    let _ = deep.walk_all(&mut |key, n| {
        if keys.contains(&key) {
            refs.push(n);
        } else if is_expr && key == b"name" {
            names.push(n);
        }
    });
    kind
}

/// A minimal JSON walker for one export line. It understands exactly what
/// lean4export emits (objects, arrays, strings, integers, literals) and
/// reports `(key, integer)` pairs; anything else is skipped.
struct Walker<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> Walker<'a> {
    fn peek(&self) -> Option<u8> {
        self.s.get(self.i).copied()
    }

    fn skip_ws(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t' | b'\r' | b'\n')) {
            self.i += 1;
        }
    }

    fn expect(&mut self, c: u8) -> Result<(), ()> {
        self.skip_ws();
        if self.peek() == Some(c) {
            self.i += 1;
            Ok(())
        } else {
            Err(())
        }
    }

    fn string(&mut self) -> Result<&'a [u8], ()> {
        self.expect(b'"')?;
        let start = self.i;
        loop {
            match self.peek() {
                None => return Err(()),
                Some(b'\\') => self.i += 2,
                Some(b'"') => {
                    let s = &self.s[start..self.i];
                    self.i += 1;
                    return Ok(s);
                }
                Some(_) => self.i += 1,
            }
        }
    }

    /// Parse a non-negative integer; `None` for any other number.
    fn number(&mut self) -> Result<Option<u32>, ()> {
        let start = self.i;
        let mut value: Option<u64> = Some(0);
        let mut digits = false;
        while let Some(c) = self.peek() {
            match c {
                b'0'..=b'9' => {
                    digits = true;
                    value = value.and_then(|v| v.checked_mul(10)).and_then(|v| v.checked_add((c - b'0') as u64));
                    self.i += 1;
                }
                b'-' | b'+' | b'.' | b'e' | b'E' => {
                    value = None;
                    self.i += 1;
                }
                _ => break,
            }
        }
        if self.i == start || !digits {
            return Err(());
        }
        Ok(value.filter(|v| *v <= u32::MAX as u64).map(|v| v as u32))
    }

    /// Walk the object at the cursor, reporting each top-level key with its
    /// integer value (if it is one). Nested values are skipped, not reported.
    fn walk_object(&mut self, f: &mut impl FnMut(&[u8], Option<u32>)) -> Result<(), ()> {
        self.expect(b'{')?;
        loop {
            self.skip_ws();
            if self.peek() == Some(b'}') {
                self.i += 1;
                return Ok(());
            }
            let key = self.string()?;
            self.expect(b':')?;
            self.skip_ws();
            let n = match self.peek() {
                Some(b'0'..=b'9' | b'-') => self.number()?,
                _ => {
                    self.skip_value()?;
                    None
                }
            };
            f(key, n);
            self.skip_ws();
            match self.peek() {
                Some(b',') => self.i += 1,
                Some(b'}') => {}
                _ => return Err(()),
            }
        }
    }

    /// Walk the value at the cursor at every depth, reporting `(key, integer)`
    /// for each integer stored directly under a key.
    fn walk_all(&mut self, f: &mut impl FnMut(&[u8], u32)) -> Result<(), ()> {
        self.skip_ws();
        match self.peek() {
            Some(b'{') => {
                self.i += 1;
                loop {
                    self.skip_ws();
                    if self.peek() == Some(b'}') {
                        self.i += 1;
                        return Ok(());
                    }
                    let key = self.string()?;
                    self.expect(b':')?;
                    self.skip_ws();
                    match self.peek() {
                        Some(b'0'..=b'9' | b'-') => {
                            if let Some(n) = self.number()? {
                                f(key, n);
                            }
                        }
                        _ => self.walk_all(f)?,
                    }
                    self.skip_ws();
                    match self.peek() {
                        Some(b',') => self.i += 1,
                        Some(b'}') => {}
                        _ => return Err(()),
                    }
                }
            }
            Some(b'[') => {
                self.i += 1;
                loop {
                    self.skip_ws();
                    if self.peek() == Some(b']') {
                        self.i += 1;
                        return Ok(());
                    }
                    self.walk_all(f)?;
                    self.skip_ws();
                    match self.peek() {
                        Some(b',') => self.i += 1,
                        Some(b']') => {}
                        _ => return Err(()),
                    }
                }
            }
            Some(b'"') => self.string().map(|_| ()),
            Some(b'0'..=b'9' | b'-') => self.number().map(|_| ()),
            _ => self.skip_literal(),
        }
    }

    fn skip_value(&mut self) -> Result<(), ()> {
        self.walk_all(&mut |_, _| {})
    }

    fn skip_literal(&mut self) -> Result<(), ()> {
        for lit in [&b"true"[..], b"false", b"null"] {
            if self.s[self.i..].starts_with(lit) {
                self.i += lit.len();
                return Ok(());
            }
        }
        Err(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    fn refs_of(line: &str) -> (Kind, Vec<u32>) {
        let mut refs = Vec::new();
        let mut names = Vec::new();
        let kind = classify(line.as_bytes(), &mut refs, &mut names);
        (kind, refs)
    }

    fn names_of(line: &str) -> Vec<u32> {
        let mut refs = Vec::new();
        let mut names = Vec::new();
        classify(line.as_bytes(), &mut refs, &mut names);
        names
    }

    #[test]
    fn constant_names_are_collected_from_expression_records_only() {
        assert_eq!(names_of(r#"{"ie":1,"const":{"name":7,"us":[1,2]}}"#), vec![7]);
        assert_eq!(names_of(r#"{"const":{"us":[],"name":9},"ie":2}"#), vec![9]);
        assert_eq!(names_of(r#"{"ie":3,"proj":{"typeName":4,"idx":0,"struct":1}}"#), vec![]);
        assert_eq!(names_of(r#"{"thm":{"name":5,"type":1,"value":2}}"#), vec![]);
        assert_eq!(names_of(r#"{"in":6,"str":{"pre":0,"str":"name"}}"#), vec![]);
    }

    #[test]
    fn classifies_records_regardless_of_key_order() {
        assert_eq!(refs_of(r#"{"bvar":0,"ie":1}"#), (Kind::Expr(1), vec![]));
        assert_eq!(refs_of(r#"{"ie":7,"app":{"fn":3,"arg":5}}"#), (Kind::Expr(7), vec![3, 5]));
        assert_eq!(
            refs_of(r#"{"forallE":{"binderInfo":"default","body":3,"type":2},"ie":4}"#),
            (Kind::Expr(4), vec![3, 2])
        );
        assert_eq!(refs_of(r#"{"ie":9,"letE":{"type":1,"value":2,"body":3}}"#), (Kind::Expr(9), vec![1, 2, 3]));
        assert_eq!(refs_of(r#"{"ie":9,"proj":{"typeName":4,"idx":1,"struct":8}}"#), (Kind::Expr(9), vec![8]));
        assert_eq!(refs_of(r#"{"ie":2,"mdata":{"data":[["k",{"str":"x\"y"}]],"expr":1}}"#), (Kind::Expr(2), vec![1]));
        // Level and name records reference nothing, even with a `rhs` key.
        assert_eq!(refs_of(r#"{"il":5,"max":{"lhs":2,"rhs":3}}"#), (Kind::Other, vec![]));
        assert_eq!(refs_of(r#"{"in":4,"str":{"pre":0,"str":"type"}}"#), (Kind::Other, vec![]));
        assert_eq!(refs_of(r#"{"meta":{"format":{"version":"3.1.0"}}}"#), (Kind::Other, vec![]));
        assert_eq!(refs_of(r#"{"sort":1,"ie":0}"#), (Kind::Expr(0), vec![]));
        assert_eq!(refs_of(r#"{"ie":3,"natVal":"123456789012345678901234567890"}"#), (Kind::Expr(3), vec![]));
    }

    #[test]
    fn declaration_records_reference_types_values_and_rules() {
        assert_eq!(
            refs_of(r#"{"thm":{"levelParams":[1],"name":9,"type":40,"value":41}}"#),
            (Kind::Decl, vec![40, 41])
        );
        assert_eq!(refs_of(r#"{"quot":{"kind":"type","levelParams":[2],"name":5,"type":12}}"#), (Kind::Decl, vec![12]));
        let ind = r#"{"inductive":{"types":[{"all":[3],"ctors":[4],"name":3,"type":20,"numParams":0,"numIndices":0}],"ctors":[{"name":4,"type":21,"induct":3,"cidx":0,"numParams":0,"numFields":0}],"recs":[{"name":5,"type":22,"all":[3],"numParams":0,"numIndices":0,"numMotives":1,"numMinors":1,"rules":[{"ctor":4,"nfields":0,"rhs":23}],"k":false}]}}"#;
        assert_eq!(refs_of(ind), (Kind::Decl, vec![20, 21, 22, 23]));
        assert_eq!(refs_of(r#"{"def":{"name":1,"type":2,"value":3,"hints":{"regular":7},"safety":"safe"}}"#), (Kind::Decl, vec![2, 3]));
    }

    #[test]
    fn nodes_expire_at_their_last_reference() {
        // 0: used only by the first declaration. 1: used by both. 2: defined
        // between the declarations, used by the second only. 3: never used.
        let export = "\
{\"meta\":{}}\n\
{\"ie\":0,\"sort\":0}\n\
{\"ie\":1,\"sort\":0}\n\
{\"def\":{\"name\":1,\"type\":1,\"value\":0}}\n\
\n\
{\"ie\":2,\"app\":{\"fn\":1,\"arg\":1}}\n\
{\"ie\":3,\"sort\":0}\n\
{\"thm\":{\"name\":2,\"type\":1,\"value\":2}}\n";
        let mut lt = scan_reader(BufReader::new(Cursor::new(export.as_bytes()))).unwrap();
        assert_eq!((lt.lines, lt.nodes), (8, 4));
        assert_eq!(lt.long_lived(), 1, "only node 1 outlives its home declaration");
        assert!(!lt.name_referenced(1) && !lt.name_referenced(2), "no expression mentions a constant");
        let mut released = Vec::new();
        lt.release_after_decl(4, 2, |i| released.push(i));
        assert_eq!(released, vec![0]);
        released.clear();
        lt.release_after_decl(8, 4, |i| released.push(i));
        assert_eq!(released, vec![2, 3, 1]);
    }

    #[test]
    fn references_to_undefined_indices_are_ignored() {
        let export = "{\"ie\":0,\"app\":{\"fn\":5,\"arg\":0}}\n{\"def\":{\"name\":1,\"type\":0,\"value\":9}}\n{\"ie\":1,\"sort\":0}\n";
        let lt = scan_reader(BufReader::new(Cursor::new(export.as_bytes()))).unwrap();
        assert_eq!(lt.nodes, 2);
        assert_eq!(lt.long_lived(), 0);
    }
}
