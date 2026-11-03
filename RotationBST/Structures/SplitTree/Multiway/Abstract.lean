module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section
namespace RotationBST.Geometric.Split

/-- Unlabelled 2–3–4 trees. Inorder ranks supply the keys, just as for binary BSTs. -/
inductive Multiway where
  | nil
  | two (left right : Multiway)
  | three (left middle right : Multiway)
  | four (first second third fourth : Multiway)
  deriving DecidableEq, Repr

namespace Multiway

/-- Number of keys, including the one, two, or three keys in each internal node. -/
def size : Multiway → Nat
  | .nil => 0
  | .two a b => a.size + b.size + 1
  | .three a b c => a.size + b.size + c.size + 2
  | .four a b c d => a.size + b.size + c.size + d.size + 3

/-- Number of multiway nodes; each merge decreases this reserve. -/
def nodes : Multiway → Nat
  | .nil => 0
  | .two a b => a.nodes + b.nodes + 1
  | .three a b c => a.nodes + b.nodes + c.nodes + 1
  | .four a b c d => a.nodes + b.nodes + c.nodes + d.nodes + 1

/-- Binary comparison-tree representation. Every attached subtree remains intact. -/
def binary : Multiway → Tree
  | .nil => .nil
  | .two a b => .node a.binary b.binary
  | .three a b c => .node a.binary (.node b.binary c.binary)
  | .four a b c d => .node (.node a.binary b.binary) (.node c.binary d.binary)

/-- All external leaves have depth `height`; each internal node has 2–4 children. -/
inductive Balanced : Nat → Multiway → Prop
  | nil : Balanced 0 .nil
  | two {h : Nat} {a b : Multiway} :
      Balanced h a → Balanced h b → Balanced (h + 1) (.two a b)
  | three {h : Nat} {a b c : Multiway} :
      Balanced h a → Balanced h b → Balanced h c → Balanced (h + 1) (.three a b c)
  | four {h : Nat} {a b c d : Multiway} :
      Balanced h a → Balanced h b → Balanced h c → Balanced h d → Balanced (h + 1) (.four a b c d)

/-- Give the left 2-node another key by borrowing from its right sibling, or
merge the two children when borrowing is impossible. The second result is the
exact binary rotation count; unmatched configurations are unchanged. -/
def prepareLeft : Multiway → Multiway × Nat
  | .two (.two a b) (.two c d) => (.four a b c d, 0)
  | .two (.two a b) (.three c d e) => (.two (.three a b c) (.two d e), 2)
  | .two (.two a b) (.four c d e f) => (.two (.three a b c) (.three d e f), 3)
  | t => (t, 0)

/-- Symmetric sibling repair for a right 2-node. -/
def prepareRight : Multiway → Multiway × Nat
  | .two (.two a b) (.two c d) => (.four a b c d, 0)
  | .two (.three a b c) (.two d e) => (.two (.two a b) (.three c d e), 2)
  | .two (.four a b c d) (.two e f) => (.two (.three a b c) (.three d e f), 4)
  | t => (t, 0)

end Multiway
end RotationBST.Geometric.Split
