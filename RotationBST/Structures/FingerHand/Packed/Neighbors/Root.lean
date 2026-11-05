module

public import RotationBST.Structures.FingerHand.Packed.Neighbors.Location
public import RotationBST.Structures.FingerHand.Packed.Updates.Endpoints
public import RotationBST.Structures.FingerHand.Packed.Neighbors.Definitions.Abstract

@[expose] public section
namespace RotationBST.FingerHand.Hand

theorem tree_nonempty {h : Hand} (valid : h.Valid) (nonempty : h.reference ≠ .nil) : h.tree ≠ .nil := by
  have size := tree_size valid
  intro empty
  rw [empty] at size
  cases eq : h.reference with
  | nil => exact nonempty eq
  | node l r => simp only [eq, Tree.size] at size; omega

/-- Expose the reference root of any nonempty hand region. A hidden root is
promoted by one expansion; an existing pseudofinger only needs normalization
of its empty tendon, leaving its physical tree and potential unchanged. -/
theorem expose_root (h : Hand) (valid : h.Valid) (nonempty : h.reference ≠ .nil) :
    ∃ (l r : Hand) (k : Nat), (fork l r).Valid ∧ (fork l r).reference = h.reference ∧
      ((∀ lo, (fork l r).labels lo = h.labels lo) ∨ Expansion h (fork l r)) ∧
      Pointer.Trace ⟨h.tree, []⟩ ⟨(fork l r).tree, []⟩ k ∧
      k + (fork l r).potential ≤ 132 + h.potential := by
  cases h with
  | knuckle t =>
    cases t with
    | nil => exact False.elim (nonempty rfl)
    | node l r =>
      have ex := exposeKnuckle l r
      exact ⟨.knuckle l, .knuckle r, 0, ex.after_valid, rfl, Or.inr ex, .refl,
        by simp [fork, potential, empty_tendon_potential]⟩
  | node cs d l r =>
    cases cs using List.reverseRecOn with
    | nil =>
      have empty := Tendon.State.represents_empty valid.1
      refine ⟨l, r, 0, ⟨Tendon.State.ofPath_represents [], valid.2⟩, rfl, Or.inl (fun _ => rfl), ?_, ?_⟩
      · simp only [tree, Tendon.State.tree, empty.1, Pointer.plug, fork]
        exact .refl
      · simp only [fork, potential, empty.2, empty_tendon_potential]
        omega
    | append_singleton cs f =>
      obtain ⟨e, k, ex, trace, cost⟩ := exposeTop cs d f l r valid
      cases f with
      | left g => exact ⟨.node cs e l r, .knuckle g, k, ex.after_valid, ex.reference, Or.inr ex, trace, cost⟩
      | right g => exact ⟨.knuckle g, .node cs e l r, k, ex.after_valid, ex.reference, Or.inr ex, trace, cost⟩

theorem Context.labels_congr (fs : List ContextFrame) {a b : Hand}
    (reference : a.reference = b.reference) (same : ∀ lo, a.labels lo = b.labels lo) :
    ∀ lo, (Context.plug fs a).labels lo = (Context.plug fs b).labels lo := by
  induction fs generalizing a b with
  | nil => exact same
  | cons f fs ih =>
    cases f <;> apply ih
    all_goals simp only [Hand.reference, reference, labels, same, implies_true]

/-- Root exposure inside an arbitrary enclosing hand pays for both directions
of navigation. It adds at most one pseudofinger and retains all previous keys. -/
theorem expose_root_under (fs : List ContextFrame) (h : Hand)
    (valid : (Context.plug fs h).Valid) (nonempty : h.reference ≠ .nil) :
    ∃ (l r : Hand) (k : Nat), (fork l r).reference = h.reference ∧ (Context.plug fs (fork l r)).Valid ∧
      (Context.plug fs (fork l r)).reference = (Context.plug fs h).reference ∧
      ((∀ lo, (Context.plug fs (fork l r)).labels lo = (Context.plug fs h).labels lo) ∨
        Expansion (Context.plug fs h) (Context.plug fs (fork l r))) ∧
      Pointer.Trace ⟨(Context.plug fs h).tree, []⟩ ⟨(Context.plug fs (fork l r)).tree, []⟩ k ∧
      k + (Context.plug fs (fork l r)).potential ≤
        132 + 10 * fs.length + (Context.plug fs h).potential := by
  obtain ⟨vh, vf⟩ := (Context.plug_valid_iff fs h).mp valid
  obtain ⟨l, r, j, after, reference, change, trace, cost⟩ := expose_root h vh nonempty
  obtain ⟨k, run, bound⟩ := Context.lift_trace fs trace (tree_nonempty vh nonempty)
    (by simp only [fork, tree, empty_tendon_tree]; simp) cost
  refine ⟨l, r, k, reference, Context.plug_valid vf after, ?_, ?_, run, bound⟩
  · simp only [Context.plug_reference, reference]
  · rcases change with same | ex
    · exact Or.inl (Context.labels_congr fs reference same)
    · exact Or.inr (ex.under fs vf)

theorem Exposure.of_change {a b : Hand} (valid : b.Valid) (reference : b.reference = a.reference)
    (change : (∀ lo, b.labels lo = a.labels lo) ∨ Expansion a b) (x : Nat)
    (member : x ∈ (b.labels 0).inorder) : Exposure a b x := by
  refine ⟨valid, reference, ?_, ?_, member⟩
  · intro lo
    rcases change with same | ex
    · rw [same lo]
    · exact ex.keys lo
  · rcases change with same | ex
    · have eq := congrArg (fun t : LabelledTree Nat => t.erase.size) (same 0)
      simp only [labels_size] at eq
      omega
    · have := ex.count
      omega

/-- Expose the root of any nonempty region at its global reference rank. -/
theorem expose_region (fs : List ContextFrame) (h : Hand)
    (valid : (Context.plug fs h).Valid) (nonempty : h.reference ≠ .nil) :
    ∃ (after : Hand) (k : Nat), Exposure (Context.plug fs h) after
        (Pointer.offset (Context.referencePath fs) + rootRank h.reference) ∧
      Pointer.Trace ⟨(Context.plug fs h).tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 132 + 10 * fs.length + (Context.plug fs h).potential := by
  obtain ⟨l, r, k, region, after, reference, change, trace, cost⟩ := expose_root_under fs h valid nonempty
  refine ⟨_, k, Exposure.of_change after reference change _ ?_, trace, cost⟩
  apply Context.member
  rw [← region]
  simp only [fork, Hand.reference, Pointer.plug, rootRank, labels, Pointer.offset, Nat.add_zero,
    Nat.zero_add, LabelledTree.inorder, List.mem_append, List.mem_cons]
  exact Or.inr (Or.inl trivial)

end RotationBST.FingerHand.Hand
