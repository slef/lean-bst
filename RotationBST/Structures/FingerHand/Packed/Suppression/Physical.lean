module

public import RotationBST.Structures.FingerHand.Packed.Suppression.Unary

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Suppress a unary top endpoint in any enclosing hand. The labelled
suppression and physical trace refer to the same final representation. -/
theorem suppress_top_under (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State)
    (f : Pointer.Frame) (l r : Hand) (marks : Finset Nat)
    (valid : (Context.plug fs (graft [] (Tendon.State.ofPath []) f (.node cs d l r))).Valid) :
    let before := Context.plug fs (graft [] (Tendon.State.ofPath []) f (.node cs d l r))
    let after := Context.plug fs (.node (cs ++ [f]) (d.addTop f) l r)
    let key := Pointer.offset (Context.referencePath fs) +
      rootRank (graft [] (Tendon.State.ofPath []) f (.node cs d l r)).reference
    after.Valid ∧ after.reference = before.reference ∧
      Suppress marks key (before.labels 0) (after.labels 0) ∧
      ∃ k, Pointer.Trace ⟨before.tree, []⟩ ⟨after.tree, []⟩ k ∧
        k + after.potential ≤ 86 + 10 * fs.length + before.potential := by
  dsimp only
  obtain ⟨inside, outside⟩ := (Context.plug_valid_iff fs _).mp valid
  have child := ((graft_valid_iff [] (Tendon.State.ofPath []) f _).mp inside).2
  obtain ⟨ex, k, trace, cost⟩ := suppressTop cs d f l r child
  have whole := ex.under fs outside
  have labels := Context.suppress fs ex.reference 0
    (suppress_top_labels cs d f l r marks (0 + Pointer.offset (Context.referencePath fs)))
  obtain ⟨m, run, bound⟩ := Context.lift_trace fs trace ex.nonempty.2 ex.nonempty.1 cost
  exact ⟨whole.before_valid, whole.reference.symm, by simpa only [Nat.zero_add] using labels,
    m, run, bound⟩

/-- Absorb a unary bottom parent into its incoming tendon in any enclosing
hand, charging both travel directions through the enclosing hand. -/
theorem suppress_bottom_under (fs : List ContextFrame) (cs : List Pointer.Frame) (d : Tendon.State)
    (f : Pointer.Frame) (l r : Hand) (marks : Finset Nat)
    (valid : (Context.plug fs (graft cs d f (fork l r))).Valid) :
    let before := Context.plug fs (graft cs d f (fork l r))
    let after := Context.plug fs (.node (f :: cs) (d.addBottom f) l r)
    let key := Pointer.offset (Context.referencePath fs) + Pointer.offset cs +
      rootRank (Pointer.plug [f] (.node l.reference r.reference))
    after.Valid ∧ after.reference = before.reference ∧
      Suppress marks key (before.labels 0) (after.labels 0) ∧
      ∃ k, Pointer.Trace ⟨before.tree, []⟩ ⟨after.tree, []⟩ k ∧
        k + after.potential ≤ 134 + 10 * fs.length + before.potential := by
  dsimp only
  obtain ⟨inside, outside⟩ := (Context.plug_valid_iff fs _).mp valid
  have parts := (graft_valid_iff cs d f _).mp inside
  have child : (Hand.node cs d l r).Valid := ⟨parts.1, parts.2.2⟩
  obtain ⟨ex, k, trace, cost⟩ := suppressBottom cs d f l r child
  have whole := ex.under fs outside
  have labels := Context.suppress fs ex.reference 0
    (suppress_bottom_labels cs d f l r marks (0 + Pointer.offset (Context.referencePath fs)))
  obtain ⟨m, run, bound⟩ := Context.lift_trace fs trace ex.nonempty.2 ex.nonempty.1 cost
  exact ⟨whole.before_valid, whole.reference.symm, by simpa only [Nat.zero_add, fork] using labels,
    m, run, bound⟩

end RotationBST.FingerHand.Hand
