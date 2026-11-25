set_option linter.unusedVariables false
def seven : Nat := 7
abbrev K (a b : Nat) : Nat := a

-- c1: proof argument under an abbrev head (const_has_proof_arg: defeq_args path).
abbrev G (n : Nat) (h : 0 < n) : Nat := n + 1
theorem c1 : G seven (by decide) = G 7 (Nat.succ_pos 6) := rfl

-- c2: ten abbrev frames with unequal arguments in one declaration
-- (MAX_DECL_EXHAUSTIONS = 8 under forced exhaustion).
theorem c2 : K seven 0 = K 7 10 ∧ K seven 1 = K 7 11 ∧ K seven 2 = K 7 12 ∧ K seven 3 = K 7 13 ∧
    K seven 4 = K 7 14 ∧ K seven 5 = K 7 15 ∧ K seven 6 = K 7 16 ∧ K seven 7 = K 7 17 ∧
    K seven 8 = K 7 18 ∧ K seven 9 = K 7 19 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- c3: nested inductive; iota through Tree.rec inside an abbrev frame
-- (mk_rec_call + nested_rec_for_type compare under the frame budget).
inductive Tree where
  | node : Nat → List Tree → Tree
def Tree.size : Tree → Nat
  | .node n ts => n + sizeF ts
where sizeF : List Tree → Nat
  | [] => 0
  | t :: ts => t.size + sizeF ts
theorem c3 : K (Tree.size (.node seven [.node 1 [], .node 2 [.node 3 []]])) 0 = K 13 1 := rfl

-- c4: nested through Array (two container levels: Array, then List).
inductive Rose where
  | node : Nat → Array Rose → Rose
mutual
def Rose.sum : Rose → Nat
  | .node n ts => n + sumA ts
def sumA : Array Rose → Nat
  | ⟨ts⟩ => sumF ts
def sumF : List Rose → Nat
  | [] => 0
  | t :: ts => t.sum + sumF ts
end
theorem c4 : K (Rose.sum (.node seven #[.node 1 #[], .node 2 #[]])) 0 = K 10 1 := rfl

-- c5: string literals under an abbrev head.
abbrev SG (s : String) : String := s
theorem c5 : SG ("ab" ++ toString seven) = SG "ab7" := rfl

-- c6: the same list pair first inside a frame, then bare in a later declaration.
def big : List Nat := (List.range 30).map (· + seven)
def big' : List Nat := (List.range 30).map (· + 7)
theorem c6a : K big.length 0 = K 30 1 := rfl
abbrev KL (l : List Nat) (n : Nat) : List Nat := l
theorem c6b : KL big 0 = KL big' 1 := rfl
theorem c6c : big = big' := rfl

-- c7: decide through an abbrev frame (Nat.decEq on a K application).
theorem c7 : decide (K seven 0 = 7) = true := rfl

-- c8: frame argument that is expensive to compare, main path cheap (K ignores b).
def fib : Nat → Nat
  | 0 => 0 | 1 => 1 | n + 2 => fib n + fib (n + 1)
def fib' : Nat → Nat
  | 0 => 0 | 1 => 1 | n + 2 => fib' (n + 1) + fib' n
theorem c8 : K seven (fib 22) = K 7 (fib' 22) := rfl

-- c9: subsingleton / structure eta under a frame: Unit-like and Subtype args.
abbrev PS (p : Nat × Nat) (u : Unit) : Nat := p.1 + p.2
theorem c9 : PS (seven, 1) () = PS (7, 1) (id ()) := rfl
