module

public import RotationBST.Algorithms.Tango.State.Abstract
public import RotationBST.Algorithms.Tango.State.Initial

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Wilber
open Region Pointer.Lazy.Skeleton

@[simp] theorem canonical_tree (t : Tree) (lo : Nat) (past : List Nat) :
    (canonical t lo past).tree = t := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
    cases h : (labels lo (lo + l.size) (lo + l.size + 1 + r.size) past).getLast?
    all_goals try cases ‹Bool›
    all_goals simp [canonical, h, tree, il, ir]

theorem canonical_initial (t : Tree) (lo : Nat) : canonical t lo [] = initial t := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir => simp [canonical, initial, labels, il, ir]

theorem canonical_decomposition (t : Tree) (lo : Nat) (past : List Nat) :
    (canonical t lo past).region.keys lo = (decomposePaths t lo past).1.toFinset ∧
    (((canonical t lo past).detached lo).map fun p => p.2.keys p.1) =
      (decomposePaths t lo past).2.map List.toFinset ∧
    (((canonical t lo past).components lo).map fun p => p.2.keys p.1) =
      (decomposePaths t lo past).parts.map List.toFinset := by
  induction t generalizing lo with
  | nil => simp [canonical, region, keys, detached, components, rootComponent, decomposePaths,
      PathDecomposition.parts]
  | node l r il ir =>
    obtain ⟨lh, ld, lc⟩ := il lo
    obtain ⟨rh, rd, rc⟩ := ir (lo + l.size + 1)
    have main : (canonical (.node l r) lo past).region.keys lo =
        (decomposePaths (.node l r) lo past).1.toFinset := by
      cases h : (labels lo (lo + l.size) (lo + l.size + 1 + r.size) past).getLast?
      all_goals try cases ‹Bool›
      all_goals simp [canonical, decomposePaths, h, region, keys, Pointer.Lazy.Skeleton.tree, lh, rh]
    have rest : (((canonical (.node l r) lo past).detached lo).map fun p => p.2.keys p.1) =
        (decomposePaths (.node l r) lo past).2.map List.toFinset := by
      cases h : (labels lo (lo + l.size) (lo + l.size + 1 + r.size) past).getLast?
      all_goals try cases ‹Bool›
      all_goals
        simp only [canonical, h, detached, ite_true, Bool.false_eq_true, ite_false,
          canonical_tree, List.nil_append, List.append_nil, List.map_append, decomposePaths]
        simp only [← lc, ← rc]
        simp only [components, List.map_append, ld, rd, List.append_assoc]
    refine ⟨main, rest, ?_⟩
    cases h : (labels lo (lo + l.size) (lo + l.size + 1 + r.size) past).getLast?
    all_goals try cases ‹Bool›
    all_goals
      simp only [canonical, h, components, rootComponent, List.singleton_append, List.map_cons,
        decomposePaths, PathDecomposition.parts, List.cons_ne_nil, ite_false] at main rest ⊢
      rw [main, rest]

end RotationBST.Tango.MarkedTree
