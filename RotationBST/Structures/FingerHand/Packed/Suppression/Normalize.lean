module

public import RotationBST.Structures.FingerHand.Packed.Suppression.Physical
public import RotationBST.Structures.FingerHand.Packed.Neighbors.Root

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Replacing any valid empty incoming tendon by its canonical empty state is
a zero-cost change, even inside an enclosing hand. -/
theorem normalize_empty_under (fs : List ContextFrame) (d : Tendon.State) (l r : Hand)
    (valid : (Context.plug fs (.node [] d l r)).Valid) :
    let before := Context.plug fs (.node [] d l r)
    let after := Context.plug fs (fork l r)
    after.Valid ∧ after.reference = before.reference ∧
      (∀ lo, after.labels lo = before.labels lo) ∧
      after.tree = before.tree ∧ after.potential = before.potential := by
  dsimp only
  obtain ⟨inside, outside⟩ := (Context.plug_valid_iff fs _).mp valid
  have empty := Tendon.State.represents_empty inside.1
  refine ⟨Context.plug_valid outside ⟨Tendon.State.ofPath_represents [], inside.2⟩, ?_, ?_, ?_, ?_⟩
  · rw [Context.plug_reference, Context.plug_reference]
    rfl
  · exact Context.labels_congr fs rfl (fun _ => rfl)
  · rw [Context.plug_tree, Context.plug_tree]
    congr 1
    change (Tendon.State.ofPath []).tree _ = d.tree _
    rw [empty_tendon_tree]
    simp only [Tendon.State.tree, empty.1, Pointer.plug]
  · simp only [Context.plug_potential, fork, potential, empty_tendon_potential, empty.2]

/-- Top contraction accepts any valid empty incoming tendon at the obsolete
endpoint, retaining the child's existing tendon state. -/
theorem suppress_top_empty (fs : List ContextFrame) (cs : List Pointer.Frame) (d e : Tendon.State)
    (f : Pointer.Frame) (l r : Hand) (marks : Finset Nat)
    (valid : (Context.plug fs (graft [] e f (.node cs d l r))).Valid) :
    let before := Context.plug fs (graft [] e f (.node cs d l r))
    let after := Context.plug fs (.node (cs ++ [f]) (d.addTop f) l r)
    let key := Pointer.offset (Context.referencePath fs) +
      rootRank (graft [] e f (.node cs d l r)).reference
    after.Valid ∧ after.reference = before.reference ∧
      Suppress marks key (before.labels 0) (after.labels 0) ∧
      ∃ k, Pointer.Trace ⟨before.tree, []⟩ ⟨after.tree, []⟩ k ∧
        k + after.potential ≤ 86 + 10 * fs.length + before.potential := by
  dsimp only
  have normalized :
      (Context.plug fs (graft [] (Tendon.State.ofPath []) f (.node cs d l r))).Valid ∧
      (Context.plug fs (graft [] (Tendon.State.ofPath []) f (.node cs d l r))).reference =
        (Context.plug fs (graft [] e f (.node cs d l r))).reference ∧
      (∀ lo, (Context.plug fs (graft [] (Tendon.State.ofPath []) f (.node cs d l r))).labels lo =
        (Context.plug fs (graft [] e f (.node cs d l r))).labels lo) ∧
      (Context.plug fs (graft [] (Tendon.State.ofPath []) f (.node cs d l r))).tree =
        (Context.plug fs (graft [] e f (.node cs d l r))).tree ∧
      (Context.plug fs (graft [] (Tendon.State.ofPath []) f (.node cs d l r))).potential =
        (Context.plug fs (graft [] e f (.node cs d l r))).potential := by
    cases f with
    | left g => exact normalize_empty_under fs e (.node cs d l r) (.knuckle g) valid
    | right g => exact normalize_empty_under fs e (.knuckle g) (.node cs d l r) valid
  obtain ⟨afterValid, reference, suppression, k, trace, cost⟩ :=
    suppress_top_under fs cs d f l r marks normalized.1
  have sameRoot : (graft [] (Tendon.State.ofPath []) f (.node cs d l r)).reference =
      (graft [] e f (.node cs d l r)).reference := by cases f <;> rfl
  refine ⟨afterValid, reference.trans normalized.2.1, ?_, k, ?_, ?_⟩
  · simpa only [sameRoot, normalized.2.2.1 0] using suppression
  · simpa only [normalized.2.2.2.1] using trace
  · simpa only [normalized.2.2.2.2] using cost

/-- The bottom contraction accepts any valid representation of the child's
empty tendon. Normalizing that state changes neither the tree nor potential. -/
theorem suppress_bottom_empty (fs : List ContextFrame) (cs : List Pointer.Frame) (d e : Tendon.State)
    (f : Pointer.Frame) (l r : Hand) (marks : Finset Nat)
    (valid : (Context.plug fs (graft cs d f (.node [] e l r))).Valid) :
    let before := Context.plug fs (graft cs d f (.node [] e l r))
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
  have empty := Tendon.State.represents_empty parts.2.1
  have normalized : (fork l r).Valid := ⟨Tendon.State.ofPath_represents [], parts.2.2⟩
  have ref : (graft cs d f (fork l r)).reference = (graft cs d f (.node [] e l r)).reference := by
    cases f <;> rfl
  have lab : ∀ lo, (graft cs d f (fork l r)).labels lo = (graft cs d f (.node [] e l r)).labels lo := by
    cases f <;> intro lo <;> rfl
  have physical : (graft cs d f (fork l r)).tree = (graft cs d f (.node [] e l r)).tree := by
    rw [graft_tree, graft_tree]
    have child : (fork l r).tree = (Hand.node [] e l r).tree := by
      change (Tendon.State.ofPath []).tree _ = e.tree _
      rw [empty_tendon_tree]
      simp only [Tendon.State.tree, empty.1, Pointer.plug]
    rw [child]
  have phi : (graft cs d f (fork l r)).potential = (graft cs d f (.node [] e l r)).potential := by
    simp only [graft_potential, fork, potential, empty_tendon_potential, empty.2]
  obtain ⟨afterValid, reference, suppression, k, trace, cost⟩ :=
    suppress_bottom_under fs cs d f l r marks (Context.plug_valid outside (graft_valid f parts.1 normalized))
  refine ⟨afterValid, ?_, ?_, k, ?_, ?_⟩
  · simpa only [Context.plug_reference, ref] using reference
  · simpa only [Context.labels_congr fs ref lab] using suppression
  · simpa only [Context.plug_tree, physical] using trace
  · simpa only [Context.plug_potential, phi] using cost

end RotationBST.FingerHand.Hand
