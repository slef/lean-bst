module

public import RotationBST.Algorithms.Simulation.Supernode.Nested.Proofs
public import RotationBST.Algorithms.Simulation.Supernode.Ranks.Proofs

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode
open Split.Multiway.Finger.TwoEnded

theorem supernodeKeys_congr {P Q : Finset Point} {lo hi : Nat}
    (same : ∀ key, lo ≤ key → key < hi → lastTouch P key = lastTouch Q key) :
    supernodeKeys P lo hi = supernodeKeys Q lo hi := by
  have priority : supernodePriority P lo hi = supernodePriority Q lo hi :=
    Finset.sup_congr rfl (fun key member => same key (Finset.mem_Ico.mp member).1 (Finset.mem_Ico.mp member).2)
  apply Finset.filter_congr
  intro key member
  rw [priority, same key (Finset.mem_Ico.mp member).1 (Finset.mem_Ico.mp member).2]

/-- Every child interval lies inside the parent interval, including the first
and last gaps and empty children. -/
theorem nested_child_bounds (state : State) (children : List Nested)
    (arity : children.length = state.size + 1) (lo : Nat) (i : Fin children.length) :
    let start := lo + i.val + gapWeight (fun j => ((children.map Nested.tree)[j]?).getD .nil) 0 i.val
    lo ≤ start ∧ start + children[i].tree.size ≤ lo + (Nested.layer state children).tree.size := by
  let gaps := fun (j : Nat) => ((children.map Nested.tree)[j]?).getD Tree.nil
  have bound : i.val ≤ state.tree.size := by rw [state_size]; have h := i.isLt; omega
  have weight := gapWeight_mono gaps 0 (show i.val + 1 ≤ state.tree.size + 1 by omega)
  have sum := gapWeight_add gaps 0 i.val 1
  have one : gapWeight gaps i.val 1 = (gaps i.val).size := by simp [gapWeight]
  rw [Nat.zero_add, one] at sum
  have atIndex : gaps i.val = children[i].tree := by
    simp only [gaps, List.getElem?_map, List.getElem?_eq_getElem i.isLt,
      Option.map_some, Option.getD_some, Fin.getElem_fin]
  rw [atIndex] at sum
  simp only [Nested.tree, withGaps_tree_size]
  change lo ≤ lo + i.val + gapWeight gaps 0 i.val ∧
    lo + i.val + gapWeight gaps 0 i.val + children[i].tree.size ≤
      lo + (state.tree.size + gapWeight gaps 0 (state.tree.size + 1))
  omega

/-- The recursive representation depends only on priorities within its own
interval. Changes to the history outside it cannot invalidate its descendants. -/
theorem Represents.congr {P Q : Finset Point} {lo : Nat} {state : Nested}
    (valid : Represents P lo state)
    (same : ∀ key, lo ≤ key → key < lo + state.tree.size → lastTouch P key = lastTouch Q key) :
    Represents Q lo state := by
  induction valid with
  | empty lo => exact .empty lo
  | layer lo state children balanced arity canonical subtrees ih =>
    refine .layer lo state children balanced arity ?_ ?_
    · exact canonical.trans (supernodeKeys_congr (by simpa only [Nested.tree, nestedRegion] using same))
    · intro i
      have bounds := nested_child_bounds state children arity lo i
      apply ih i
      intro key lower upper
      exact same key (by omega) (by omega)

/-- A row avoiding a nested interval leaves its complete represented state
unchanged, not just its outer heap or active keys. -/
theorem Represents.untouched {time : Nat} {P : Finset Point} {keys : Finset Nat}
    {lo : Nat} {state : Nested} (valid : Represents P lo state)
    (misses : ∀ key, lo ≤ key → key < lo + state.tree.size → key ∉ keys) :
    Represents (P ∪ row time keys) lo state := by
  apply valid.congr
  intro key lower upper
  exact (last_new_untouched (misses key lower upper)).symm

end RotationBST.Geometric.Online.Supernode
