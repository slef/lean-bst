module

public import RotationBST.Algorithms.Simulation.Supernode.Assembly.Keys

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

/-- Valid assemblies have last-touch heaps in every untouched fringe subtree. -/
theorem Assembly.Valid.holes {P : Finset Point} {assembly : Assembly} {lo : Nat}
    (valid : assembly.Valid P lo) :
    ∀ hole ∈ Region.holes assembly.region lo,
      Heap (fun key => OrderDual.toDual (lastTouch P key)) hole.2 hole.1 := by
  induction assembly generalizing lo with
  | hole state =>
    intro hole member
    have equal : hole = (lo, state.tree) := List.mem_singleton.mp member
    subst hole
    exact valid.heap
  | node left right il ir =>
    intro hole member
    rcases List.mem_append.mp member with member | member
    · exact il valid.1 hole member
    · exact ir valid.2 hole member

/-- Child executions compose under exposed parent keys. Absolute offsets are
unchanged because each execution preserves the full subtree size. -/
theorem Assembly.fill_spec {P Q : Finset Point} (expand : Nested → Nat → Assembly × Nat)
    (correct : ∀ state lo, Represents P lo state →
      (expand state lo).1.Valid Q lo ∧
        Rotations state.tree (expand state lo).1.region.tree (expand state lo).2)
    {assembly : Assembly} {lo : Nat} (valid : assembly.Valid P lo) :
    (assembly.fill expand lo).1.Valid Q lo ∧
      Rotations assembly.region.tree (assembly.fill expand lo).1.region.tree
        (assembly.fill expand lo).2 := by
  induction assembly generalizing lo with
  | hole state => exact correct state lo valid
  | node left right il ir =>
    have l := il valid.1
    have r := ir valid.2
    have size := l.2.size_eq
    constructor
    · change (left.fill expand lo).1.Valid Q lo ∧
        (right.fill expand (lo + left.region.tree.size + 1)).1.Valid Q
          (lo + (left.fill expand lo).1.region.tree.size + 1)
      exact ⟨l.1, by rw [← size]; exact r.1⟩
    · exact (l.2.inLeft).append r.2.inRight

end RotationBST.Arboral.Online.Supernode
