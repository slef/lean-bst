import Std

/-! BST shapes: nodes have implicit zero-based inorder labels.
An access must put its requested label at the root. Cost counts rotations only,
including rotations inside subtrees; no pointer movement is charged. -/
namespace RotationBST

inductive Tree where
  | nil
  | node (left right : Tree)
  deriving DecidableEq, Repr

def Tree.size : Tree → Nat
  | .nil => 0
  | .node l r => l.size + 1 + r.size

/-- One rotation, at any depth. -/
inductive Rotate : Tree → Tree → Prop where
  | right : Rotate (.node (.node a b) c) (.node a (.node b c))
  | left : Rotate (.node a (.node b c)) (.node (.node a b) c)
  | inLeft : Rotate a b → Rotate (.node a c) (.node b c)
  | inRight : Rotate a b → Rotate (.node c a) (.node c b)

/-- Exactly `k` rotations. -/
inductive Rotations : Tree → Tree → Nat → Prop where
  | refl : Rotations t t 0
  | step : Rotate s t → Rotations t u k → Rotations s u (k + 1)

/-- Access rank `x` from `s`, finish at `t`, using `k` rotations. -/
def Access (s t : Tree) (x k : Nat) : Prop :=
  Rotations s t k ∧ match t with
    | .nil => False
    | .node l _ => l.size = x

/-- An offline execution serving an entire request sequence. -/
inductive Execution : Tree → List Nat → Tree → Nat → Prop where
  | nil : Execution t [] t 0
  | cons : Access s t x k → Execution t xs u m → Execution s (x :: xs) u (k + m)

theorem Rotate.size_eq (h : Rotate s t) : s.size = t.size := by
  induction h with
  | right => simp only [Tree.size]; omega
  | left => simp only [Tree.size]; omega
  | inLeft _ ih => simp only [Tree.size, ih]
  | inRight _ ih => simp only [Tree.size, ih]

theorem Rotations.size_eq (h : Rotations s t k) : s.size = t.size := by
  induction h with
  | refl => rfl
  | step h _ ih => exact h.size_eq.trans ih

theorem Access.in_range (h : Access s t x k) : x < s.size := by
  obtain ⟨hr, hx⟩ := h
  rw [hr.size_eq]
  cases t with
  | nil => exact hx.elim
  | node l r => simp only [Tree.size]; change l.size = x at hx; omega

/-- An online rule sees only past requests, the current tree and current request.
For each existing rank, it returns a tree and a certified rotation count. -/
structure Algorithm where
  step : List Nat → Tree → Nat → Tree × Nat
  correct : ∀ past t x, x < t.size →
    Access t (step past t x).1 x (step past t x).2

def Algorithm.runFrom (a : Algorithm) (past : List Nat) (t : Tree) :
    List Nat → Tree × Nat
  | [] => (t, 0)
  | x :: xs =>
      let (u, k) := a.step past t x
      let (v, m) := a.runFrom (past ++ [x]) u xs
      (v, k + m)

def Algorithm.cost (a : Algorithm) (t : Tree) (xs : List Nat) : Nat :=
  (a.runFrom [] t xs).2

/-- Compare against every legal offline execution from the same initial tree. -/
def DynamicallyOptimal (a : Algorithm) : Prop :=
  ∃ C D : Nat, ∀ t xs u k, Execution t xs u k →
    a.cost t xs ≤ C * k + D * t.size

/-- First access has working-set number `n`; otherwise count distinct keys
since its last access, plus one. -/
def workingSetNumber (n : Nat) (past : List Nat) (x : Nat) : Nat :=
  if x ∈ past then 1 + (past.reverse.takeWhile (· != x)).eraseDups.length else n

def workingSetSum (n : Nat) (past : List Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => 1 + (workingSetNumber n past x).log2 +
      workingSetSum n (past ++ [x]) xs

/-- Total working-set bound, with an initial-tree allowance. -/
def HasWorkingSetBound (a : Algorithm) : Prop :=
  ∃ C D : Nat, ∀ t xs, (∀ x ∈ xs, x < t.size) →
    a.cost t xs ≤ C * workingSetSum t.size [] xs +
      D * t.size * (1 + t.size.log2)

end RotationBST
