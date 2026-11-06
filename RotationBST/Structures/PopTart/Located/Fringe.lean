module

public import RotationBST.Structures.PopTart.Located.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.WeightedTree

theorem fringeSpan_append (xs ys : List (Tree × ℝ)) :
    fringeSpan (xs ++ ys) = fringeSpan xs + fringeSpan ys := by simp [fringeSpan]

theorem fringeSpan_fringe (t : WeightedTree) : fringeSpan t.fringe = t.tree.size + 1 := by
  induction t with
  | leaf t w => simp [fringeSpan, fringe, tree, skeleton, Pointer.Lazy.Skeleton.tree]
  | node l r ihL ihR =>
    rw [fringe, fringeSpan_append, ihL, ihR]
    change l.tree.size + 1 + (r.tree.size + 1) = l.tree.size + 1 + r.tree.size + 1
    omega

theorem LocatedSlot.forget {t : WeightedTree} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot t subtree weight offset depth) : SlotAt t subtree weight depth := by
  induction slot with
  | leaf t w => exact .leaf t w
  | left slot ih => exact .left ih
  | right slot ih => exact .right ih

theorem LocatedSlot.fits {t : WeightedTree} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot t subtree weight offset depth) : offset + subtree.size ≤ t.tree.size := by
  induction slot with
  | leaf s w => change 0 + s.size ≤ s.size; omega
  | @left l r subtree weight offset depth slot ih =>
    change offset + subtree.size ≤ l.tree.size + 1 + r.tree.size
    omega
  | @right l r subtree weight offset depth slot ih =>
    change offset + l.tree.size + 1 + subtree.size ≤ l.tree.size + 1 + r.tree.size
    omega

theorem LocatedSlot.split {t : WeightedTree} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot t subtree weight offset depth) :
    ∃ before after, t.fringe = before ++ (subtree, weight) :: after ∧ fringeSpan before = offset := by
  induction slot with
  | leaf => exact ⟨[], [], rfl, rfl⟩
  | @left l r subtree weight offset depth slot ih =>
    obtain ⟨before, after, split, span⟩ := ih
    exact ⟨before, after ++ r.fringe, by simp [fringe, split, List.append_assoc], span⟩
  | @right l r subtree weight offset depth slot ih =>
    obtain ⟨before, after, split, span⟩ := ih
    refine ⟨l.fringe ++ before, after, by simp [fringe, split, List.append_assoc], ?_⟩
    rw [fringeSpan_append, fringeSpan_fringe, span]
    omega

/-- An exact fringe split locates that occurrence, even if another slot has
the same shape and weight. The prefix determines its physical inorder rank. -/
theorem locate_split {t : WeightedTree} {before after : List (Tree × ℝ)} {subtree : Tree} {weight : ℝ}
    (split : t.fringe = before ++ (subtree, weight) :: after) :
    ∃ depth, LocatedSlot t subtree weight (fringeSpan before) depth := by
  induction t generalizing before after with
  | leaf s w =>
    cases before with
    | nil =>
      simp only [fringe, List.nil_append, List.cons.injEq] at split
      obtain ⟨same, _⟩ := split
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact ⟨0, .leaf _ _⟩
    | cons head tail =>
      have length := congrArg List.length split
      simp only [fringe, List.length_cons, List.length_nil, List.length_append] at length
      omega
  | node l r ihL ihR =>
    change l.fringe ++ r.fringe = before ++ (subtree, weight) :: after at split
    rcases List.append_eq_append_iff.mp split with ⟨extra, beforeEq, right⟩ | ⟨extra, left, suffix⟩
    · obtain ⟨depth, located⟩ := ihR right
      refine ⟨depth + 1, ?_⟩
      rw [beforeEq, fringeSpan_append, fringeSpan_fringe]
      convert LocatedSlot.right (l := l) located using 1
      omega
    · cases extra with
      | nil =>
        simp only [List.append_nil] at left
        simp only [List.nil_append] at suffix
        obtain ⟨depth, located⟩ := ihR (before := []) (by simpa only [List.nil_append] using suffix.symm)
        refine ⟨depth + 1, ?_⟩
        rw [← left, fringeSpan_fringe]
        simpa only [fringeSpan, List.map_nil, List.sum_nil, Nat.zero_add] using
          LocatedSlot.right (l := l) located
      | cons head tail =>
        simp only [List.cons_append, List.cons.injEq] at suffix
        obtain ⟨same, _⟩ := suffix
        subst head
        obtain ⟨depth, located⟩ := ihL left
        exact ⟨depth + 1, .left located⟩

end RotationBST.PopTart.WeightedTree
