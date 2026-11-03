module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Repair.Context.Accounting

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger.Repair.Context.Results

/-- Repair a shortened first-child interval through its enclosing ancestors.
The computed result is balanced, and its counter counts actual finger rotations. -/
theorem repair {expected actual : Nat} {focus : Multiway} {fs : List Context.Frame}
    (balanced : Balanced actual focus) (ancestors : Context.Valid expected fs)
    (left : ∀ f ∈ fs, IsLeftFrame f) (shorter : actual ≤ expected) :
    let result := repairContext expected actual focus fs
    Rotations (enclosingView focus fs) (binaryView result.tree).tree result.cost ∧
      Balanced result.height result.tree ∧ result.height ≤ expected + fs.length :=
  ⟨repairContext_rotations fs expected actual focus left,
    repairContext_balance fs balanced ancestors left shorter⟩

/-- Two credits per multiway node pay for an arbitrarily long repair cascade.
Only the initial height gap and a fixed terminal allowance remain charged. -/
theorem amortized {expected actual : Nat} {focus : Multiway} {fs : List Context.Frame}
    (balanced : Balanced actual focus) (ancestors : Context.Valid expected fs)
    (left : ∀ f ∈ fs, IsLeftFrame f) (shorter : actual ≤ expected) :
    let result := repairContext expected actual focus fs
    result.cost + 2 * result.tree.nodes ≤
      2 * (Context.plug fs focus).nodes + 6 * (expected - actual) + 26 :=
  repairContext_credit fs balanced ancestors left shorter

/-- A one-level deficit has a constant amortized repair cost. -/
theorem one_level {h : Nat} {focus : Multiway} {fs : List Context.Frame}
    (balanced : Balanced h focus) (ancestors : Context.Valid (h + 1) fs)
    (left : ∀ f ∈ fs, IsLeftFrame f) :
    let result := repairContext (h + 1) h focus fs
    result.cost + 2 * result.tree.nodes ≤ 2 * (Context.plug fs focus).nodes + 16 :=
  repairContext_one_level fs balanced ancestors left

end RotationBST.Geometric.Split.Multiway.Finger.Repair.Context.Results

/-- info: abstract audit passed for `RotationBST.Geometric.Split.Multiway.Finger.Repair.Context.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.Split.Multiway.Finger.Repair.Context.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Context.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs,
  RotationBST.Structures.SplitTree.Multiway.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Abstract,
  RotationBST.Structures.SplitTree.Finger.Locate.Embedding.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Abstract,
  RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Join.Defs,
  RotationBST.Structures.SplitTree.Finger.Repair.Frame.Defs,
  RotationBST.Structures.SplitTree.Finger.Repair.Context.Defs]
