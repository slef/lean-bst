module

public import RotationBST.Structures.PopTart.Definitions.Abstract

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

/-- The regular right-spine nodes of one Chocolate layer. -/
inductive Regulars where
  | zero
  | one (a : WeightedTree)
  | two (a b : WeightedTree)
  | three (a b c : WeightedTree)

namespace Regulars

def attach (tail : WeightedTree) : Regulars → WeightedTree
  | .zero => tail
  | .one a => .node a tail
  | .two a b => .node a (.node b tail)
  | .three a b c => .node a (.node b (.node c tail))

def Valid (level : Nat) : Regulars → Prop
  | .zero => True
  | .one a => Perfect level a ∧ a.Nonnegative
  | .two a b => (Perfect level a ∧ a.Nonnegative) ∧ (Perfect level b ∧ b.Nonnegative)
  | .three a b c => (Perfect level a ∧ a.Nonnegative) ∧
      (Perfect level b ∧ b.Nonnegative) ∧ (Perfect level c ∧ c.Nonnegative)

/-- Empty base layers and two-crumb layers need no repair credit. -/
def potential : Regulars → Nat
  | .zero | .two _ _ => 0
  | .one _ | .three _ _ _ => 20

end Regulars

mutual
/-- Active layers retain a distinct next node with its child on the left and
icing on the right. A last layer has no next node. -/
inductive Layer where
  | last (regulars : Regulars) (icing : Icing)
  | next (regulars : Regulars) (child : Layer) (icing : Icing)

/-- The icing keeps enough frozen metadata for subsequent thawing. `solid`
is a frozen perfect crumb; `frozen` remembers the carried crumb and the old
next layer as separate pieces of the unchanged frozen subtree. -/
inductive Icing where
  | base (crumb : WeightedTree)
  | solid (crumb : WeightedTree) (tail : Icing)
  | frozen (carry : WeightedTree) (old : Layer) (tail : Icing)
end

mutual
def Layer.decode : Layer → WeightedTree
  | .last rs icing => rs.attach icing.decode
  | .next rs child icing => rs.attach (.node child.decode icing.decode)

def Icing.decode : Icing → WeightedTree
  | .base crumb => crumb
  | .solid crumb tail => .node crumb tail.decode
  | .frozen carry old tail => .node (WeightedTree.node carry old.decode) tail.decode
end

/-- The same icing viewed as a Vanilla stack of frozen physical subtrees.
Each frozen block carries its actual aggregate fringe mass. `decode` retains
the full interior; this view is used only for the outer access bound. -/
def Icing.outer : Icing → WeightedTree
  | .base crumb => .leaf crumb.tree crumb.mass
  | .solid crumb tail => .node (.leaf crumb.tree crumb.mass) tail.outer
  | .frozen carry old tail =>
      .node (.leaf (WeightedTree.node carry old.decode).tree (WeightedTree.node carry old.decode).mass) tail.outer

mutual
/-- Credits in frozen layers remain stored, so freezing does not discard the
potential that will be needed when those layers are thawed. -/
def Layer.potential : Layer → Nat
  | .last rs icing => rs.potential + icing.potential
  | .next rs child icing => rs.potential + child.potential + icing.potential

def Icing.potential : Icing → Nat
  | .base _ => 0
  | .solid _ tail => tail.potential
  | .frozen _ old tail => old.potential + tail.potential
end

mutual
/-- Structural validity, nonnegative weights, and the strict thick-icing
invariant. An empty regular list is permitted only for a single base crumb. -/
def Layer.Valid (level : Nat) : Layer → Prop
  | .last rs icing => rs.Valid level ∧ icing.Valid level ∧
      (rs = .zero → ∃ crumb, icing = .base crumb)
  | .next rs child icing => rs.Valid level ∧ child.Valid (level + 1) ∧ icing.Valid level ∧
      rs ≠ .zero ∧ child.decode.mass < icing.decode.mass

/-- Frozen pending carries retain both the old strict mass inequality and the
new domination inequality. These are the certificates needed when thawing and
when bounding paths inside a frozen next layer. -/
def Icing.Valid (level : Nat) : Icing → Prop
  | .base crumb => Perfect level crumb ∧ crumb.Nonnegative
  | .solid crumb tail => Perfect (level + 1) crumb ∧ crumb.Nonnegative ∧ tail.Valid level ∧
      tail.decode.mass ≤ crumb.mass
  | .frozen carry old tail => Perfect (level + 1) carry ∧ carry.Nonnegative ∧
      old.Valid (level + 1) ∧ tail.Valid level ∧ old.decode.mass < tail.decode.mass ∧
      tail.decode.mass ≤ carry.mass + old.decode.mass
end

namespace Icing

/-- Refill an empty regular list from the icing. Frozen pending carries retain
their saved next layer; only the carried perfect crumb is split. -/
def thaw : Icing → Option Layer
  | .base crumb => some (.last .zero (.base crumb))
  | .solid (.node b c) tail => some (.last (.two b c) tail)
  | .frozen (.node b c) old tail => some (.next (.two b c) old tail)
  | _ => none

def thawCost : Icing → Nat
  | .base _ => 0
  | .solid _ _ => 2
  | .frozen _ _ _ => 4

/-- Thaw cost inside the right child of an exposed popped separator. -/
def popCost : Icing → Nat
  | .base _ => 0
  | .solid _ _ => 4
  | .frozen _ _ _ => 6

end Icing

namespace Layer

/-- Number of next-layer transitions before reaching the last active layer.
Frozen icing interiors do not participate in a recursive carry. -/
def activeDepth : Layer → Nat
  | .last _ _ => 0
  | .next _ child _ => child.activeDepth + 1

def HasTop : Layer → Prop
  | .last .zero _ | .next .zero _ _ => False
  | _ => True

/-- A next layer consisting of only its initial crumb is borrowed directly,
without trying to pop a nonexistent separator from that layer. -/
def baseCrumb : Layer → Option WeightedTree
  | .last .zero (.base crumb) => some crumb
  | _ => none

def pop : Layer → Option (WeightedTree × Layer)
  | .last .zero _ => none
  | .last (.one a) icing => icing.thaw.map (fun rest => (a, rest))
  | .last (.two a b) icing => some (a, .last (.one b) icing)
  | .last (.three a b c) icing => some (a, .last (.two b c) icing)
  | .next .zero _ _ => none
  | .next (.one a) child icing => match child.baseCrumb with
      | some (.node b c) => some (a, .last (.two b c) icing)
      | some (.leaf _ _) => none
      | none => match child.pop with
          | some (.node b c, rest) => some (a, .next (.two b c) rest icing)
          | _ => none
  | .next (.two a b) child icing => some (a, .next (.one b) child icing)
  | .next (.three a b c) child icing => some (a, .next (.two b c) child icing)

def popCost : Layer → Nat
  | .last (.one _) icing => icing.popCost
  | .next (.one _) child _ => match child.baseCrumb with
      | some _ => 4
      | none => 10 + child.popCost
  | _ => 0

/-- A push compares only the mass of the proposed next layer with its icing.
When that mass reaches the icing mass it freezes immediately, before further
rebalancing of the saved next layer. -/
noncomputable def push (new : WeightedTree) : Layer → Layer := by
  classical
  exact fun stack => match stack with
  | .last .zero icing => .last (.one new) icing
  | .last (.one a) icing => .last (.two new a) icing
  | .last (.two a b) icing => .last (.three new a b) icing
  | .last (.three a b c) icing =>
      if (.node b c : WeightedTree).mass < icing.decode.mass then
        .next (.two new a) (.last .zero (.base (.node b c))) icing
      else .last (.two new a) (.solid (.node b c) icing)
  | .next .zero child icing => .next (.one new) child icing
  | .next (.one a) child icing => .next (.two new a) child icing
  | .next (.two a b) child icing => .next (.three new a b) child icing
  | .next (.three a b c) child icing =>
      if (.node b c : WeightedTree).mass + child.decode.mass < icing.decode.mass then
        .next (.two new a) (child.push (.node b c)) icing
      else .last (.two new a) (.frozen (.node b c) child icing)

/-- Exact pointer cost of the rebalancing trace, including returning to the
outer root between the local rotation and recursive carry phases. -/
noncomputable def pushCost : Layer → Nat := by
  classical
  exact fun stack => match stack with
  | .last (.three _ _ _) _ => 6
  | .next (.three _ b c) child icing =>
      if (.node b c : WeightedTree).mass + child.decode.mass < icing.decode.mass then
        14 + child.pushCost
      else 8
  | _ => 0

end Layer

/-- Concrete push histories retain the chosen weights and every intermediate
layer state. The general mixed-operation interface appears below. -/
inductive Pushes (level : Nat) : Layer → Layer → Nat → Type where
  | nil (stack : Layer) : Pushes level stack stack 0
  | cons {stack rest : Layer} {n : Nat} (new : WeightedTree)
      (perfect : Perfect level new) (nonnegative : new.Nonnegative)
      (tail : Pushes level (stack.push new) rest n) : Pushes level stack rest (n + 1)

namespace Pushes

noncomputable def cost {level : Nat} {stack rest : Layer} {n : Nat} : Pushes level stack rest n → Nat
  | .nil _ => 0
  | .cons _ _ _ tail => stack.pushCost + tail.cost

/-- Every rebalancing boundary is realized; caller-supplied separators are
accounted for separately, as in the other pop-tart structures. -/
inductive Realizes {level : Nat} : {stack rest : Layer} → {n : Nat} → Pushes level stack rest n → Prop where
  | nil (stack : Layer) : Realizes (.nil stack)
  | cons {stack rest : Layer} {n : Nat} {new : WeightedTree}
      {perfect : Perfect level new} {nonnegative : new.Nonnegative}
      {tail : Pushes level (stack.push new) rest n}
      (first : Pointer.Trace ⟨.node new.tree stack.decode.tree, []⟩
        ⟨(stack.push new).decode.tree, []⟩ stack.pushCost)
      (later : Realizes tail) : Realizes (.cons new perfect nonnegative tail)

end Pushes

/-- Legal operations preserve the caller-supplied/exposed-separator boundary. -/
inductive Operation (level : Nat) : Layer → Layer → Type where
  | push (stack : Layer) (new : WeightedTree) (perfect : Perfect level new)
      (nonnegative : new.Nonnegative) : Operation level stack (stack.push new)
  | pop (stack rest : Layer) (crumb : WeightedTree) (popped : stack.pop = some (crumb, rest)) :
      Operation level stack rest

namespace Operation

noncomputable def cost {level : Nat} {stack rest : Layer} : Operation level stack rest → Nat
  | .push _ _ _ _ => stack.pushCost
  | .pop _ _ _ _ => stack.popCost

def input {level : Nat} {stack rest : Layer} : Operation level stack rest → Tree
  | .push _ new _ _ => .node new.tree stack.decode.tree
  | .pop _ _ _ _ => stack.decode.tree

def output {level : Nat} {stack rest : Layer} : Operation level stack rest → Tree
  | .push _ _ _ _ => rest.decode.tree
  | .pop _ _ crumb _ => .node crumb.tree rest.decode.tree

end Operation

inductive Program (level : Nat) : Layer → Layer → Nat → Type where
  | nil (stack : Layer) : Program level stack stack 0
  | cons {stack middle rest : Layer} {n : Nat}
      (op : Operation level stack middle) (tail : Program level middle rest n) :
      Program level stack rest (n + 1)

namespace Program

noncomputable def cost {level : Nat} {stack rest : Layer} {n : Nat} : Program level stack rest n → Nat
  | .nil _ => 0
  | .cons op tail => op.cost + tail.cost

inductive Realizes {level : Nat} : {stack rest : Layer} → {n : Nat} → Program level stack rest n → Prop where
  | nil (stack : Layer) : Realizes (.nil stack)
  | cons {stack middle rest : Layer} {n : Nat}
      {op : Operation level stack middle} {tail : Program level middle rest n}
      (first : Pointer.Trace ⟨op.input, []⟩ ⟨op.output, []⟩ op.cost)
      (later : Realizes tail) : Realizes (.cons op tail)

end Program
end RotationBST.PopTart.Chocolate
