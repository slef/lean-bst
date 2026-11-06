module

public import RotationBST.Structures.PopTart.Definitions.Abstract

@[expose] public section
namespace RotationBST.PopTart.Cherry
open WeightedTree

/-- Redundant binary digits store one to three crumbs at each layer. -/
inductive Layers where
  | nil
  | one (a : WeightedTree) (tail : Layers)
  | two (a b : WeightedTree) (tail : Layers)
  | three (a b c : WeightedTree) (tail : Layers)

namespace Layers

def decode (bottom : WeightedTree) : Layers → WeightedTree
  | .nil => bottom
  | .one a tail => .node a (tail.decode bottom)
  | .two a b tail => .node a (.node b (tail.decode bottom))
  | .three a b c tail => .node a (.node b (.node c (tail.decode bottom)))

def height : Layers → Nat
  | .nil => 0
  | .one _ tail | .two _ _ tail | .three _ _ _ tail => tail.height + 1

/-- Ten units on a one- or three-crumb layer pay for a full pointer round trip
when that layer must carry or borrow. -/
def potential : Layers → Nat
  | .nil => 0
  | .one _ tail | .three _ _ _ tail => 10 + tail.potential
  | .two _ _ tail => tail.potential

/-- Overflow retains the first two crumbs and carries the joined last two. -/
def push (new : WeightedTree) : Layers → Layers
  | .nil => .one new .nil
  | .one a tail => .two new a tail
  | .two a b tail => .three new a b tail
  | .three a b c tail => .two new a (tail.push (.node b c))

/-- Underflow borrows one next-level crumb and splits it into its two children.
Invalid layers are totalized by failure; the invariant proves success. -/
def pop : Layers → Option (WeightedTree × Layers)
  | .nil => none
  | .one a .nil => some (a, .nil)
  | .one a tail => match tail.pop with
      | some (.node b c, rest) => some (a, .two b c rest)
      | _ => none
  | .two a b tail => some (a, .one b tail)
  | .three a b c tail => some (a, .two b c tail)

def pushCost : Layers → Nat
  | .three _ _ _ tail => 10 + tail.pushCost
  | _ => 0

def popCost : Layers → Nat
  | .one _ .nil => 0
  | .one _ tail => 6 + tail.popCost
  | _ => 0

end Layers

/-- Each layer contains perfect crumbs of its level; the next level is one
higher. Empty layers terminate the structure. -/
inductive Valid : Nat → Layers → Prop where
  | nil (level : Nat) : Valid level .nil
  | one {level : Nat} {a : WeightedTree} {tail : Layers} :
      Perfect level a → Valid (level + 1) tail → Valid level (.one a tail)
  | two {level : Nat} {a b : WeightedTree} {tail : Layers} :
      Perfect level a → Perfect level b → Valid (level + 1) tail → Valid level (.two a b tail)
  | three {level : Nat} {a b c : WeightedTree} {tail : Layers} :
      Perfect level a → Perfect level b → Perfect level c → Valid (level + 1) tail → Valid level (.three a b c tail)


/-- Legal stack operations at one crumb level. The enclosing algorithm supplies
or receives the top separator at the stated operation boundary. -/
inductive Operation (level : Nat) : Layers → Layers → Type where
  | push (layers : Layers) (crumb : WeightedTree) (perfect : Perfect level crumb) :
      Operation level layers (layers.push crumb)
  | pop (layers rest : Layers) (crumb : WeightedTree) (popped : layers.pop = some (crumb, rest)) :
      Operation level layers rest

namespace Operation

def cost {level : Nat} {layers rest : Layers} : Operation level layers rest → Nat
  | .push _ _ _ => layers.pushCost
  | .pop _ _ _ _ => layers.popCost

def input {level : Nat} {layers rest : Layers} (bottom : WeightedTree) : Operation level layers rest → Tree
  | .push _ crumb _ => .node crumb.tree (layers.decode bottom).tree
  | .pop _ _ _ _ => (layers.decode bottom).tree

def output {level : Nat} {layers rest : Layers} (bottom : WeightedTree) : Operation level layers rest → Tree
  | .push _ _ _ => (rest.decode bottom).tree
  | .pop _ _ crumb _ => .node crumb.tree (rest.decode bottom).tree

/-- A pushed crumb is itself ordered and no lighter than any old fringe
occurrence. At level zero it consists of exactly one newly pushed leaf.
Pop operations impose no extra weight restriction. -/
def Increasing {level : Nat} {layers rest : Layers} (bottom : WeightedTree) :
    Operation level layers rest → Prop
  | .push _ crumb _ => crumb.Ordered ∧
      ∀ a ∈ crumb.fringe, ∀ b ∈ (layers.decode bottom).fringe, b.2 ≤ a.2
  | .pop _ _ _ _ => True

end Operation

inductive Program (level : Nat) : Layers → Layers → Nat → Type where
  | nil (layers : Layers) : Program level layers layers 0
  | cons {layers middle rest : Layers} {n : Nat}
      (op : Operation level layers middle) (tail : Program level middle rest n) :
      Program level layers rest (n + 1)

namespace Program

def cost {level : Nat} {layers rest : Layers} {n : Nat} : Program level layers rest n → Nat
  | .nil _ => 0
  | .cons op tail => op.cost + tail.cost

def Increasing (bottom : WeightedTree) {level : Nat} :
    {layers rest : Layers} → {n : Nat} → Program level layers rest n → Prop
  | _, _, _, .nil _ => True
  | _, _, _, .cons op tail => op.Increasing bottom ∧ tail.Increasing bottom

/-- Each operation's actual pointer trace, with all caller transfers between
operation boundaries left explicit. The bottom fringe slot stays fixed. -/
inductive Realizes (bottom : WeightedTree) {level : Nat} :
    {layers rest : Layers} → {n : Nat} → Program level layers rest n → Prop where
  | nil (layers : Layers) : Realizes bottom (.nil layers)
  | cons {layers middle rest : Layers} {n : Nat}
      {op : Operation level layers middle} {tail : Program level middle rest n}
      (first : Pointer.Trace ⟨op.input bottom, []⟩ ⟨op.output bottom, []⟩ op.cost)
      (later : Realizes bottom tail) : Realizes bottom (.cons op tail)

end Program

end RotationBST.PopTart.Cherry
