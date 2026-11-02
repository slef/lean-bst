module

public import RotationBST.Splay.Scanning.Step
public import RotationBST.Splay.Online.Abstract

@[expose] public section

namespace RotationBST.Splay.Scanning
open Marked

/-- Telescope the successor potential over the entire remaining inorder suffix. -/
theorem suffix_bound (n : Nat) (before : Tree) (ls : List Marked) (past : List Nat)
    (valid : AllValid ls) (size : (spine ls).size = n) :
    2 * (algorithm.runFrom past (.node before (spine ls))
      (List.range' (before.size + 1) n)).2 ≤ 6 * n + totalPotential ls := by
  induction n generalizing before ls past with
  | zero => simp [List.range', Algorithm.runFrom]
  | succ n ih =>
      have hn : spine ls ≠ .nil := by intro h; rw [h] at size; simp [Tree.size] at size
      obtain ⟨next, k, hv, hrun, hcost, hsize⟩ := step before ls valid hn
      have hs : (spine next).size = n := by omega
      have hb := ih (.node before .nil) next (past ++ [before.size + 1]) hv hs
      have he : (Tree.node before .nil).size + 1 = before.size + 1 + 1 := by simp [Tree.size]
      rw [he] at hb
      simp only [List.range', Algorithm.runFrom, algorithm, hrun]
      change 2 * (k + (algorithm.runFrom (past ++ [before.size + 1])
        (.node (.node before .nil) (spine next)) (List.range' (before.size + 1 + 1) n)).2) ≤
        6 * (n + 1) + totalPotential ls
      omega

/-- Starting at an already accessed root, scanning its unvisited right subtree
uses at most twelve rotations per remaining key. -/
theorem suffix_linear (before rest : Tree) (past : List Nat) :
    (algorithm.runFrom past (.node before rest)
      (List.range' (before.size + 1) rest.size)).2 ≤ 12 * rest.size := by
  have h := suffix_bound rest.size before (initialSpine rest) past
    (initialSpine_valid rest) (by rw [initialSpine_tree])
  rw [initialSpine_tree] at h
  have hp := initialSpine_potential rest
  omega

/-- Sequential access for the implemented bottom-up splay, from any initial
shape. This deliberately uses a generous constant, not the best literature bound. -/
theorem rotation_bound (t : Tree) : algorithm.cost t (List.range t.size) ≤ 13 * t.size := by
  cases ht : t with
  | nil => simp [Algorithm.cost, Algorithm.runFrom, Tree.size]
  | node l r =>
      have hx : 0 < (Tree.node l r).size := by simp [Tree.size]
      have ha := (run_correct (.node l r) 0 hx).1
      have hc := (run_correct (.node l r) 0 hx).2
      cases he : (Splay.run (.node l r) 0).1 with
      | nil => rw [he] at ha; exact False.elim ha.2
      | node a b =>
          have hz : a = .nil := by
            have hh := ha.2
            rw [he] at hh
            cases a with
            | nil => rfl
            | node u v => simp [Tree.size] at hh
          subst a
          have hs := ha.1.size_eq
          rw [he] at hs
          simp only [Tree.size] at hs
          have hb := suffix_linear .nil b [0]
          simp only [Tree.size, Nat.zero_add] at hb
          have htotal : (Tree.node l r).size = b.size + 1 := by simp only [Tree.size]; omega
          unfold Algorithm.cost
          rw [List.range_eq_range', htotal]
          simp only [List.range', Algorithm.runFrom, algorithm, he, Nat.zero_add]
          change (Splay.run (.node l r) 0).2 +
            (algorithm.runFrom [0] (.node .nil b) (List.range' 1 b.size)).2 ≤ 13 * (b.size + 1)
          omega

end RotationBST.Splay.Scanning
