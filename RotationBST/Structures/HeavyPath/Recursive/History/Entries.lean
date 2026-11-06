module

public import RotationBST.Structures.HeavyPath.Recursive.History.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Recursive.Inorder
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History
open Paired LabelledCursor PopTart PopTart.WeightedTree

theorem lower_sources {α : Type} (es : List (Entry α)) :
    (lower es).map Entry.source = lowerFrames (es.map Entry.source) := by
  induction es with
  | nil => rfl
  | cons e es ih => cases h : e.source <;> simp [lower, h, lowerFrames, ih]

theorem upper_sources {α : Type} (es : List (Entry α)) :
    (upper es).map Entry.source = upperFrames (es.map Entry.source) := by
  induction es with
  | nil => rfl
  | cons e es ih => cases h : e.source <;> simp [upper, h, upperFrames, ih]

theorem lower_mem {α : Type} {es : List (Entry α)} {e : Entry α} (member : e ∈ lower es) : e ∈ es := by
  induction es with
  | nil => cases member
  | cons head es ih =>
    cases h : head.source <;> simp only [lower, h, List.mem_append, List.mem_singleton] at member
    · exact List.mem_cons_of_mem _ (ih member)
    · rcases member with member | rfl
      · exact List.mem_cons_of_mem _ (ih member)
      · exact List.mem_cons_self

theorem upper_mem {α : Type} {es : List (Entry α)} {e : Entry α} (member : e ∈ upper es) : e ∈ es := by
  induction es with
  | nil => cases member
  | cons head es ih =>
    cases h : head.source <;> simp only [upper, h, List.mem_cons] at member
    · rcases member with rfl | member
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih member)
    · exact List.mem_cons_of_mem _ (ih member)

theorem source_member {α : Type} {weight : α → ℝ} {es : List (Entry α)} {t : LabelledTree α}
    (context : es.map Entry.source = (extract weight t).context) {e : Entry α} (member : e ∈ es) :
    e.source ∈ (extract weight t).context := by
  rw [← context]
  exact List.mem_map_of_mem member

theorem entries_inorder {α : Type} {weight : α → ℝ} {es : List (Entry α)} {t : LabelledTree α} {endpoint : α}
    (context : es.map Entry.source = (extract weight t).context)
    (focus : (extract weight t).focus = .node .nil endpoint .nil) :
    t.inorder = (lower es).flatMap Entry.lowerBlock ++ [endpoint] ++ (upper es).flatMap Entry.upperBlock := by
  have original := Recursive.context_inorder (es.map Entry.source) (extract weight t).focus
  rw [context] at original
  change (extract weight t).tree.inorder = _ at original
  rw [HeavyPath.Results.extract_tree, focus, ← context, ← lower_sources, ← upper_sources] at original
  change t.inorder = (lower es).flatMap (fun e => Recursive.lowerBlock e.source) ++
    [endpoint] ++ (upper es).flatMap (fun e => Recursive.upperBlock e.source)
  simpa only [List.flatMap_map, Function.comp_def,
    LabelledTree.inorder, List.nil_append] using original

theorem split_sum {α : Type} {β : Type} [AddCommMonoid β] (f : Entry α → β) (es : List (Entry α)) :
    ((lower es).map f).sum + ((upper es).map f).sum = (es.map f).sum := by
  induction es with
  | nil => simp [lower, upper]
  | cons e es ih => cases h : e.source <;>
      simp [lower, upper, h, ← ih, add_assoc, add_comm, add_left_comm]

theorem path_mass {α : Type} {weight : α → ℝ} {es : List (Entry α)} {p : Stacks}
    (valid : PathValid weight es p) : p.mass = (es.map (fun e => frameMass weight e.source)).sum := by
  have l := fringe_mass p.lower.decode
  have r := fringe_mass p.upper.decode.mirror
  rw [valid.lower] at l
  rw [valid.upper] at r
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def, Entry.slot,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add, mirror_mass] at l r
  rw [Stacks.mass, ← l, ← r, split_sum]

theorem path_partition {α : Type} {weight : α → ℝ} {es : List (Entry α)} {p : Stacks}
    {t : LabelledTree α} {endpoint : α}
    (context : es.map Entry.source = (extract weight t).context)
    (valid : PathValid weight es p) (focus : (extract weight t).focus = .node .nil endpoint .nil) :
    weight endpoint + p.mass = mass weight t := by
  have total := HeavyPath.Results.extract_mass weight t
  rw [focus, ← context, List.map_map] at total
  simpa only [mass, zero_add, add_zero, path_mass valid, Function.comp_def] using total.symm

theorem path_mass_le {α : Type} {weight : α → ℝ} {es : List (Entry α)} {p : Stacks}
    {t : LabelledTree α} (positive : Positive weight t) (nonempty : t ≠ .nil)
    (context : es.map Entry.source = (extract weight t).context) (valid : PathValid weight es p) :
    p.mass ≤ mass weight t := by
  obtain ⟨endpoint, focus⟩ := HeavyPath.Results.extract_terminal positive nonempty
  have partition := path_partition context valid focus
  have own := (HeavyPath.Results.extract_positive positive).1
  rw [focus] at own
  have pos : 0 < weight endpoint := own.2.1
  linarith

/-- Block lengths count the payload's physical nodes and its source separator. -/
theorem blocks_span {α : Type} (weight : α → ℝ) (block : Entry α → List α) (es : List (Entry α))
    (sizes : ∀ e ∈ es, (block e).length = e.shape.size + 1) :
    fringeSpan (es.map (Entry.slot weight)) = (es.flatMap block).length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, List.flatMap_cons, List.length_append, fringeSpan, List.sum_cons, Entry.slot] at *
    rw [sizes e (by simp), ih (fun f hf => sizes f (by simp [hf]))]

/-- Enumerate every physical fringe occurrence without identifying equal
source frames or equal payload shapes. -/
theorem blocks_ranks {α : Type} (weight : α → ℝ) (block : Entry α → List α)
    (P : Nat → α → Prop) (shift : Nat) {whole : WeightedTree} (es : List (Entry α))
    (sizes : ∀ e ∈ es, (block e).length = e.shape.size + 1)
    (bound : ∀ e ∈ es, ∀ offset depth,
      LocatedSlot whole e.shape (frameMass weight e.source) offset depth →
      ∀ base, offset = base + shift → RanksSatisfy P base (block e))
    {before after : List (Tree × ℝ)} {base : Nat}
    (split : whole.fringe = before ++ es.map (Entry.slot weight) ++ after)
    (offset : fringeSpan before = base + shift) : RanksSatisfy P base (es.flatMap block) := by
  induction es generalizing before base with
  | nil => exact RanksSatisfy.nil _ _
  | cons e es ih =>
    have headSplit : whole.fringe = before ++ (e.shape, frameMass weight e.source) ::
        (es.map (Entry.slot weight) ++ after) := by
      simpa only [List.map_cons, List.append_assoc, List.cons_append, Entry.slot] using split
    obtain ⟨depth, located⟩ := locate_split headSplit
    apply RanksSatisfy.append (bound e (by simp) _ depth located base offset)
    apply ih (fun f hf => sizes f (by simp [hf]))
      (fun f hf => bound f (by simp [hf])) (before := before ++ [e.slot weight])
    · simpa only [List.map_cons, List.append_assoc, List.singleton_append] using split
    · rw [fringeSpan_append, offset, sizes e (by simp)]
      simp only [fringeSpan, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Entry.slot]
      omega

end RotationBST.HeavyPath.Recursive.History
