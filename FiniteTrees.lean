import StateElimination

/-! A finite (deliberately redundant) enumeration covering all trees of a given
size. Used for existence bounds, not an efficient tree-generation algorithm. -/
namespace RotationBST

def treeCover : Nat → List Tree
  | 0 => [.nil]
  | n + 1 => .nil :: (treeCover n).flatMap (fun l => (treeCover n).map (Tree.node l))

theorem mem_treeCover (t : Tree) (n : Nat) (hs : t.size ≤ n) : t ∈ treeCover n := by
  induction n generalizing t with
  | zero =>
      cases t with
      | nil => simp [treeCover]
      | node l r => simp only [Tree.size] at hs; omega
  | succ n ih =>
      cases t with
      | nil => simp [treeCover]
      | node l r =>
          have hl : l.size ≤ n := by simp only [Tree.size] at hs; omega
          have hr : r.size ≤ n := by simp only [Tree.size] at hs; omega
          simp only [treeCover, List.mem_cons,
            List.mem_flatMap, List.mem_map]
          exact Or.inr ⟨l, ih l hl, r, ih r hr, rfl⟩

/-- Bounding each finite collection of step costs requires no complexity or
computability assumption on the online rule. -/
def stepBound (b : TreeAlgorithm) (n : Nat) : Nat :=
  ((treeCover n).flatMap (fun t => (List.range n).map
    (fun x => 1 + (b.step () t x).2.2))).foldr Nat.max 0

private theorem le_foldr_max (xs : List Nat) (x : Nat) (hx : x ∈ xs) :
    x ≤ xs.foldr Nat.max 0 := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

theorem step_le_stepBound (b : TreeAlgorithm) (t : Tree) (hs : t.size = n)
    (hx : x < n) : 1 + (b.step () t x).2.2 ≤ stepBound b n := by
  apply le_foldr_max
  apply List.mem_flatMap.mpr
  refine ⟨t, mem_treeCover t n (by omega), ?_⟩
  exact List.mem_map.mpr ⟨x, List.mem_range.mpr hx, rfl⟩

/-- info: 'RotationBST.step_le_stepBound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_le_stepBound
end RotationBST
