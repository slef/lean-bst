module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Reference.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Results

/-- The leaf interpretation has one more key than internal nodes. Its forest
is ordered, with nonempty component intervals inside the original range. -/
theorem layout (t : Tree) (lo searched : Nat) :
    leaves t = t.size + 1 ∧
    (forest t lo searched).Pairwise (fun a b => a.last ≤ b.first) ∧
    ∀ c ∈ forest t lo searched,
      lo ≤ c.first ∧ c.first < c.last ∧ c.last ≤ lo + leaves t :=
  ⟨leaves_eq t, ordered t lo searched, fun c hc =>
    ⟨(bounds t lo searched hc).1, component_nonempty c, (bounds t lo searched hc).2⟩⟩

theorem partition (t : Tree) (lo searched key : Nat)
    (valid : lo ≤ key ∧ key < lo + leaves t) :
    ∃! c, c ∈ forest t lo searched ∧ c.Contains key := Reference.partition t lo searched key valid

/-- Exactly the searched singleton contains the current searched key. -/
theorem searched (t : Tree) (lo key : Nat) (valid : lo ≤ key ∧ key < lo + leaves t) :
    (⟨key, .nil⟩ : Component) ∈ forest t lo key ∧
      ∀ c ∈ forest t lo key, c.Contains key → c = ⟨key, .nil⟩ :=
  ⟨selected t lo key valid, fun _ member contains => contains_searched t lo key valid member contains⟩

/-- Persistent components other than the searched singletons see both
searches on the same side of their interval. -/
theorem side (t : Tree) (lo x y : Nat) {c : Component}
    (vx : lo ≤ x ∧ x < lo + leaves t) (vy : lo ≤ y ∧ y < lo + leaves t)
    (mx : c ∈ forest t lo x) (my : c ∈ forest t lo y)
    (nx : c ≠ ⟨x, .nil⟩) (ny : c ≠ ⟨y, .nil⟩) :
    (x < c.first ∧ y < c.first) ∨ (c.last ≤ x ∧ c.last ≤ y) :=
  persistent_side t lo x y vx vy mx my nx ny

theorem stream (t : Tree) (lo first : Nat) (xs : List Nat) {c : Component}
    (valid : ∀ x ∈ first :: xs, lo ≤ x ∧ x < lo + leaves t)
    (member : ∀ x ∈ first :: xs, c ∈ forest t lo x)
    (other : ∀ x ∈ first :: xs, c ≠ ⟨x, .nil⟩) :
    (∀ x ∈ first :: xs, x < c.first) ∨ (∀ x ∈ first :: xs, c.last ≤ x) :=
  stream_side t lo first xs valid member other

/-- Connect reference-forest persistence to actual GreedyASS accesses after
an earlier component access. The searched-singleton exception stays explicit. -/
theorem access (t : Tree) (lo first : Nat) (xs : List Nat)
    {c : Component} {n stamp accessed : Nat} {P : Finset Point}
    (history : History n (stamp + 1) P) (point : (accessed, stamp) ∈ P)
    (within : c.Contains accessed)
    (valid : ∀ x ∈ first :: xs, lo ≤ x ∧ x < lo + leaves t)
    (member : ∀ x ∈ first :: xs, c ∈ forest t lo x)
    (other : ∀ x ∈ first :: xs, c ≠ ⟨x, .nil⟩) :
    ((∀ x ∈ first :: xs, x < c.first) ∧
      ∀ p ∈ fill greedySweep (stamp + 1) P xs, stamp < p.2 → p.1 ≤ accessed) ∨
    ((∀ x ∈ first :: xs, c.last ≤ x) ∧
      ∀ p ∈ fill greedySweep (stamp + 1) P xs, stamp < p.2 → accessed ≤ p.1) :=
  access_barrier t lo first xs history point within valid member other

theorem point_side (t : Tree) (lo : Nat) (xs : List Nat) {c : Component} {key : Nat}
    (within : c.Contains key)
    (valid : ∀ x ∈ xs, lo ≤ x ∧ x < lo + leaves t)
    (member : ∀ x ∈ xs, c ∈ forest t lo x) :
    (∀ x ∈ xs, x ≤ key) ∨ (∀ x ∈ xs, key ≤ x) := Reference.point_side t lo xs within valid member

/-- The point-side barrier includes visits to a searched singleton. -/
theorem barrier (t : Tree) (lo : Nat) (xs : List Nat)
    {c : Component} {n stamp accessed : Nat} {P : Finset Point}
    (history : History n (stamp + 1) P) (point : (accessed, stamp) ∈ P)
    (within : c.Contains accessed)
    (valid : ∀ x ∈ xs, lo ≤ x ∧ x < lo + leaves t)
    (member : ∀ x ∈ xs, c ∈ forest t lo x) :
    ((∀ x ∈ xs, x ≤ accessed) ∧
      ∀ p ∈ fill greedySweep (stamp + 1) P xs, stamp < p.2 → p.1 ≤ accessed) ∨
    ((∀ x ∈ xs, accessed ≤ x) ∧
      ∀ p ∈ fill greedySweep (stamp + 1) P xs, stamp < p.2 → accessed ≤ p.1) :=
  persistent_barrier t lo xs history point within valid member

end RotationBST.Geometric.GreedyASS.Reference.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Reference.Results`: 8 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Reference.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Algorithms.GreedyASS.Algorithm.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract]
