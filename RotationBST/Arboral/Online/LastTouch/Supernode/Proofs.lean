module

public import RotationBST.Arboral.Online.LastTouch.Supernode.Abstract
public import RotationBST.Arboral.Online.LastTouch.Proofs

@[expose] public section
namespace RotationBST.Arboral

theorem supernodeKeys_nonempty (P : Finset Point) {lo hi : Nat} (nonempty : lo < hi) :
    (supernodeKeys P lo hi).Nonempty := by
  have interval : (Finset.Ico lo hi).Nonempty := ⟨lo, by simp [nonempty]⟩
  obtain ⟨key, member, equal⟩ := Finset.sup_mem_of_nonempty (f := lastTouch P) interval
  exact ⟨key, Finset.mem_filter.mpr ⟨member, equal⟩⟩

theorem supernode_priority_upper (P : Finset Point) {lo hi key : Nat}
    (inside : key ∈ Finset.Ico lo hi) : lastTouch P key ≤ supernodePriority P lo hi :=
  Finset.le_sup inside

/-- Untouched keys all belong to one bottom-priority supernode, so a genuine
gap below a supernode necessarily has a previously touched boundary. -/
theorem supernode_gap_positive {P : Finset Point} {lo hi boundary key : Nat}
    (gap : SupernodeGap P lo hi boundary key) : ⊥ < supernodePriority P lo hi := by
  by_contra notPositive
  have bottom : supernodePriority P lo hi = ⊥ := le_antisymm (le_of_not_gt notPositive) bot_le
  have inside : key ∈ Finset.Ico lo hi := Finset.mem_Ico.mpr ⟨gap.2.1, gap.2.2.1⟩
  have upper := supernode_priority_upper P inside
  have equal : lastTouch P key = supernodePriority P lo hi := by
    rw [bottom] at upper ⊢
    exact le_antisymm upper bot_le
  exact gap.2.2.2.2 key (by omega) (by omega) (Ne.symm gap.2.2.2.1)
    (Finset.mem_filter.mpr ⟨inside, equal⟩)

theorem supernode_gap_boundary {P : Finset Point} {lo hi boundary key : Nat}
    (gap : SupernodeGap P lo hi boundary key)
    (positive : ⊥ < supernodePriority P lo hi) : LastTouchBoundary P boundary key := by
  obtain ⟨root, keyLo, keyHi, different, between⟩ := gap
  obtain ⟨rootInside, rootPriority⟩ := Finset.mem_filter.mp root
  obtain ⟨rootLo, rootHi⟩ := Finset.mem_Ico.mp rootInside
  refine ⟨different, by rwa [rootPriority], ?_⟩
  intro y lower upper notRoot
  have inside : y ∈ Finset.Ico lo hi := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have bound := supernode_priority_upper P inside
  have strict : lastTouch P y ≠ supernodePriority P lo hi := by
    intro equal
    exact between y lower upper notRoot (Finset.mem_filter.mpr ⟨inside, equal⟩)
  rw [rootPriority]
  exact lt_of_le_of_ne bound strict

theorem supernode_gap_required {n time request lo hi boundary key : Nat}
    {P : Finset Point} {keys : Finset Nat} (history : History n time P)
    (legal : Completion n time request P keys) (touched : key ∈ keys)
    (gap : SupernodeGap P lo hi boundary key) :
    boundary ∈ keys := boundary_required history legal touched (supernode_gap_boundary gap (supernode_gap_positive gap))

/-- Historical priorities are strictly below the current row, even for keys
that have never been touched. -/
theorem lastTouch_before_row {n time : Nat} {P : Finset Point} (history : History n time P) (key : Nat) :
    lastTouch P key < (time : WithBot Nat) := by
  by_contra notBefore
  obtain ⟨future, member, later⟩ := last_witness (le_of_not_gt notBefore)
  have old := (history _ member).2
  omega

theorem supernode_row_priority {n time lo hi : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (touched : (keys ∩ Finset.Ico lo hi).Nonempty) :
    supernodePriority (P ∪ row time keys) lo hi = (time : WithBot Nat) := by
  apply le_antisymm
  · exact Finset.sup_le (fun _ _ => last_new_bound history keys _)
  · obtain ⟨key, member⟩ := touched
    obtain ⟨inKeys, inInterval⟩ := Finset.mem_inter.mp member
    have bound := supernode_priority_upper (P ∪ row time keys) inInterval
    rwa [lastTouch_extend history, ite_eq_left inKeys] at bound

/-- In every interval touched on the new row, precisely its newly touched keys
form the new root supernode. Untouched keys retain strictly lower priorities. -/
theorem supernode_row_keys {n time lo hi : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (touched : (keys ∩ Finset.Ico lo hi).Nonempty) :
    supernodeKeys (P ∪ row time keys) lo hi = keys ∩ Finset.Ico lo hi := by
  ext key
  simp only [supernodeKeys, Finset.mem_filter, Finset.mem_inter,
    supernode_row_priority history touched, lastTouch_extend history]
  by_cases member : key ∈ keys
  · simp [member]
  · have old := lastTouch_before_row history key
    simp [member, ne_of_lt old]

end RotationBST.Arboral
