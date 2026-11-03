module

public import RotationBST.Algorithms.Simulation.Supernode.Extraction.Execution
public import RotationBST.Algorithms.Simulation.Supernode.Assembly.Completion

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

/-- A size-bounded extraction exposes every key of the legal row in its
interval, and exposes no other key. The recursion strictly decreases at each
entered layer, so the fuel cutoff never hides a remaining touched key. -/
theorem extract_keys {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (legal : Completion n time request P keys)
    (fuel : Nat) {lo : Nat} {state : Nested} (represented : Represents P lo state)
    (enough : state.tree.size < fuel) :
    Region.keys (extract fuel keys lo state).1.region lo = keys ∩ Finset.Ico lo (lo + state.tree.size) := by
  induction fuel generalizing lo state with
  | zero => omega
  | succ fuel ih =>
    simp only [extract]
    split
    · rename_i untouched
      simp only [Assembly.region, Region.keys, untouched]
    · rename_i entered
      cases state with
      | empty => simp [Assembly.region, Region.keys, Nested.tree, Tree.size]
      | layer parent children =>
        have touches := Finset.nonempty_iff_ne_empty.mpr entered
        have selected := selectParent_spec represented keys
        have active : Region.keys (selectParent parent children lo keys).1.region lo ⊆ keys := by
          rw [selectParent_keys represented keys]
          exact Finset.inter_subset_left
        have smaller : ∀ hole ∈ Region.holes (selectParent parent children lo keys).1.region lo,
            hole.2.size < fuel := by
          intro hole member
          have bound := selectParent_hole_smaller history legal represented touches member
          omega
        have complete := Assembly.fill_keys (limit := fuel)
          (fun child start => extract fuel keys start child)
          (fun child start valid => extract_execution fuel keys valid)
          (fun child start valid bound => ih valid bound) selected.1 active smaller
        have size := selected.2.1.size_eq
        simpa only [← size] using complete

/-- The concrete row extractor covers the entire row interval with exact
rotations and canonical retained holes, using only current history and keys. -/
theorem extractRow_spec {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (legal : Completion n time request P keys)
    {lo : Nat} {state : Nested} (represented : Represents P lo state) :
    (extractRow keys lo state).1.Valid P lo ∧
      Rotations state.tree (extractRow keys lo state).1.region.tree (extractRow keys lo state).2 ∧
      Region.keys (extractRow keys lo state).1.region lo = keys ∩ Finset.Ico lo (lo + state.tree.size) :=
  ⟨(extract_execution _ keys represented).1, (extract_execution _ keys represented).2,
    extract_keys history legal _ represented (by omega)⟩

end RotationBST.Arboral.Online.Supernode
