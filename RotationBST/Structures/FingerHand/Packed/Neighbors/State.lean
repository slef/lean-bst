module

public import RotationBST.Structures.FingerHand.Packed.Neighbors.Children
public import RotationBST.Structures.FingerHand.Packed.Neighbors.Parent

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Convert a contextual local bound to a finger-count bound in a maintained
hand. The same trace and final state are retained. -/
theorem state_cost {fingers : Nat} (fs : List ContextFrame) (h : Hand)
    {s : Multifinger.State fingers} (rep : (Context.plug fs h).Represents s)
    {after : Hand} {k C : Nat}
    (cost : k + after.potential ≤ C + 10 * fs.length + (Context.plug fs h).potential) :
    k + after.potential ≤ C + 20 * (fingers + 1) + (Context.plug fs h).potential := by
  have count := rep.count
  have len := Context.length_le_count fs
  rw [Context.plug_count] at count
  omega

/-- Every actual finger admits a bounded editable decomposition and an exact
reference cursor, even after the tendons have been updated and rebalanced. -/
theorem Represents.locate {fingers : Nat} {h : Hand} {s : Multifinger.State fingers}
    (rep : h.Represents s) (valid : s.Valid) (i : Fin fingers) :
    ∃ (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State) (l r : Hand),
      h = Context.plug fs (.node cs d l r) ∧
      (Pointer.Config.mk (.node l.reference r.reference) (cs ++ Context.referencePath fs)).tree = s.tree ∧
      (Pointer.Config.mk (.node l.reference r.reference) (cs ++ Context.referencePath fs)).key? = some (s.position i) ∧
      fs.length < 2 * (fingers + 1) := by
  obtain ⟨fs, cs, d, l, r, eq, tree, key, depth⟩ := locate_reference h _ (rep.finger valid i)
  exact ⟨fs, cs, d, l, r, eq, tree.trans rep.2.1, key, lt_of_lt_of_le depth rep.count⟩

end RotationBST.FingerHand.Hand
