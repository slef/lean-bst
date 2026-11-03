module

public import RotationBST.Structures.SplitTree.Finger.Binary.Bounds
public import RotationBST.Bounds.StaticTree.Definitions.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open StaticTree

theorem depth_node_bound {l r : Tree} {bound : Nat}
    (left : ∀ x, depth l x ≤ bound) (right : ∀ x, depth r x ≤ bound) (x : Nat) :
    depth (.node l r) x ≤ bound + 1 := by
  simp only [depth]
  split
  · exact Nat.add_le_add_right (left x) 1
  · split
    · omega
    · exact Nat.add_le_add_right (right _) 1

/-- Each 2–3–4 level has at most two binary comparisons below its entry. -/
theorem binary_depth {h : Nat} {t : Multiway} (valid : Balanced h t) (x : Nat) :
    depth t.binary x ≤ 2 * h := by
  induction valid generalizing x with
  | nil => exact Nat.le_refl _
  | two ha hb ia ib =>
    have bound := depth_node_bound ia ib x
    change depth (.node _ _) x ≤ _
    omega
  | three ha hb hc ia ib ic =>
    have right := depth_node_bound ib ic
    have bound := depth_node_bound (fun x => Nat.le_trans (ia x) (Nat.le_succ _)) right x
    change depth (.node _ _) x ≤ _
    omega
  | four ha hb hc hd ia ib ic id =>
    have bound := depth_node_bound (depth_node_bound ia ib) (depth_node_bound ic id) x
    change depth (.node _ _) x ≤ _
    omega

/-- Extending the far end of a comparison spine does not affect searches for
old keys except for the one added comparison before its last attached subtree. -/
theorem comb_depth_extend (xs : List Tree) (tail rest : Tree) (bound rank : Nat)
    (left : ∀ t ∈ xs, ∀ x, depth t x ≤ bound) (last : ∀ x, depth tail x ≤ bound)
    (valid : rank < (comb xs tail).size) :
    depth (comb xs (.node tail rest)) rank ≤ xs.length + bound + 1 := by
  induction xs generalizing rank with
  | nil =>
    change rank < tail.size at valid
    simp only [comb, List.length_nil, Nat.zero_add, depth, ite_eq_left valid]
    exact Nat.add_le_add_right (last rank) 1
  | cons t xs ih =>
    have subtree := left t (List.mem_cons_self ..) rank
    have remaining := ih (rank - t.size - 1) (fun u hu => left u (List.mem_cons_of_mem _ hu))
    simp only [comb, depth]
    split
    · simp only [List.length_cons]
      omega
    · split
      · omega
      · have h := remaining (by simp only [comb, Tree.size] at valid; omega)
        simp only [List.length_cons]
        omega

end RotationBST.Arboral.Split.Multiway.Finger
