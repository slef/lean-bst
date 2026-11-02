module

public import RotationBST.Arboral.View.Execution
public import RotationBST.Pointer.Lazy.Projection
public import RotationBST.Model.Basic

@[expose] public section
namespace RotationBST.Arboral
open Pointer.Lazy

private theorem project_keys_component (color : Nat → Bool) (t : Tree) (lo : Nat) :
    Region.keys (project color (t.labelFrom lo)) lo =
      (componentKeys color true (t.labelFrom lo)).toFinset := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
    cases hc : color (lo + l.size) <;>
      simp [Tree.labelFrom, project, hc, Region.keys, componentKeys, project_tree,
        Representation.Bridge.erase_label, il, ir]

/-- The existing lazy normal form gives a small connected region, with all
other rotations postponed and charged when their component is used. -/
theorem access_to_region {s t : Tree} {x k : Nat} (h : Access s t x k) :
    ∃ q r d, ∃ step : RegionStep s q x, Rotations q t d ∧ r + d = k ∧
      step.before.size ≤ 2 * r + 1 := by
  cases s with
  | nil => have := h.in_range; simp [Tree.size] at this
  | node l r =>
    let s := Tree.node l r
    have hl := (Representation.Bridge.access_iff s t x k).mp h
    obtain ⟨ops, hlen, ht⟩ := trace_of_rotations hl.1
    have hd : (s.labelFrom 0).inorder.Nodup := by
      rw [Representation.Bridge.inorder_label]
      exact List.nodup_range'
    have source : rootKey? (s.labelFrom 0) = some l.size := by simp [s, Tree.labelFrom, rootKey?]
    have target : rootKey? (t.labelFrom 0) = some x := by
      cases t with
      | nil => exact False.elim h.2
      | node a b => simpa only [Tree.labelFrom, rootKey?, Nat.zero_add] using congrArg some h.2
    obtain ⟨color, q, hu, hcolor, covered, count, selected, _, pending, lengths⟩ :=
      rooted_normal_form ht hd source target
    have uniform := ht.root_color color hu
    rw [source, target] at uniform
    have hxcolor : color x = true := (Option.some.inj uniform).symm.trans hcolor
    have both : ∀ e ∈ ops.filter (fun e => color e.1),
        color e.1 = true ∧ color e.2 = true := by
      intro e he
      obtain ⟨he, hec⟩ := List.mem_filter.mp he
      exact ⟨hec, (hu e he).symm.trans hec⟩
    have fringe := selected.project_fringe color both hd covered
    let step : RegionStep s q.erase x := {
      before := project color (s.labelFrom 0)
      after := project color q
      source := by rw [project_tree, Representation.Bridge.erase_label]
      target := project_tree color q
      fringe := fringe
      visits := by rw [project_keys_component]; exact List.mem_toFinset.mpr (covered x hxcolor) }
    refine ⟨q.erase, (ops.filter fun e => color e.1).length,
      (ops.filter fun e => !(color e.1)).length, step, ?_, ?_, ?_⟩
    · simpa only [Representation.Bridge.erase_label] using Representation.Bridge.erase_rotations pending.forget
    · omega
    · simpa only [step, project_size] using count

theorem region_execution_pending {s t u : Tree} {xs : List Nat} {i k : Nat}
    (h : RotationBST.Execution t xs u k) (pending : Rotations s t i) :
    ∃ v cost deferred, RegionExecution s xs v cost ∧ Rotations v u deferred ∧
      cost + 2 * deferred ≤ 2 * (i + k) + xs.length := by
  induction h generalizing s i with
  | nil => exact ⟨s, 0, i, .nil, pending, by simp⟩
  | @cons t v x a xs u b ha _ ih =>
    have access : Access s v x (i + a) := ⟨pending.append ha.1, ha.2⟩
    obtain ⟨q, used, deferred, step, rest, count, bound⟩ := access_to_region access
    obtain ⟨w, cost, final, execution, suffix, charge⟩ := ih rest
    refine ⟨w, step.before.size + cost, final, .cons step execution, suffix, ?_⟩
    simp only [List.length_cons]
    omega

/-- Every rotation-only BST execution admits an ASS solution at constant cost.
The geometry forgets the final tree; deferred final rotations need not be drawn. -/
theorem rotations_to_offline {s t : Tree} {xs : List Nat} {rotations : Nat}
    (h : RotationBST.Execution s xs t rotations) :
    ∃ E : Offline s.size xs, E.points.card ≤ 2 * rotations + xs.length := by
  obtain ⟨_, cost, _, execution, _, bound⟩ := region_execution_pending h (Rotations.refl (t := s))
  obtain ⟨E, hcard⟩ := region_to_offline execution
  exact ⟨E, by omega⟩

end RotationBST.Arboral
