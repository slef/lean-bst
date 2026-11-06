module

public import RotationBST.Structures.HeavyPath.Recursive.DepthStep
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive
open Paired LabelledCursor PopTart PopTart.WeightedTree

theorem lowerFrames_mem {α : Type} {cs : List (Frame α)} {frame : Frame α}
    (member : frame ∈ lowerFrames cs) : frame ∈ cs := by
  induction cs with
  | nil => cases member
  | cons f cs ih =>
    cases f <;> simp only [lowerFrames, List.mem_append, List.mem_singleton] at member
    · exact List.mem_cons_of_mem _ (ih member)
    · rcases member with h | rfl
      · exact List.mem_cons_of_mem _ (ih h)
      · exact List.mem_cons_self

theorem upperFrames_mem {α : Type} {cs : List (Frame α)} {frame : Frame α}
    (member : frame ∈ upperFrames cs) : frame ∈ cs := by
  induction cs with
  | nil => cases member
  | cons f cs ih =>
    cases f <;> simp only [upperFrames, List.mem_cons] at member
    · rcases member with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)
    · exact List.mem_cons_of_mem _ (ih member)

/-- The split is by occurrences, so it requires neither ordering nor distinct labels. -/
theorem context_inorder {α : Type} (cs : List (Frame α)) (t : LabelledTree α) :
    (plug cs t).inorder = (lowerFrames cs).flatMap lowerBlock ++
      t.inorder ++ (upperFrames cs).flatMap upperBlock := by
  induction cs generalizing t with
  | nil => simp [plug, lowerFrames, upperFrames]
  | cons f cs ih =>
    cases f <;> simp [plug, ih, lowerFrames, upperFrames, lowerBlock, upperBlock,
      framePayload, frameKey, LabelledTree.inorder, List.append_assoc]

theorem lowerFrames_slots {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (cs : List (Frame α)) :
    (lowerFrames cs).map (fun f => (payload (framePayload f), frameMass weight f)) =
      (lowerSlotsWith weight payload cs).reverse := by
  induction cs with
  | nil => rfl
  | cons f cs ih =>
    cases f <;> simp only [lowerFrames, lowerSlotsWith, List.map_append,
      List.map_cons, List.map_nil, List.reverse_cons, ih]; rfl

theorem upperFrames_slots {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (cs : List (Frame α)) :
    (upperFrames cs).map (fun f => (payload (framePayload f), frameMass weight f)) =
      upperSlotsWith weight payload cs := by
  induction cs with
  | nil => rfl
  | cons f cs ih =>
    cases f <;> simp only [upperFrames, upperSlotsWith, List.map_cons, ih]; rfl

theorem RanksSatisfy.nil {α : Type} (P : Nat → α → Prop) (offset : Nat) :
    RanksSatisfy P offset [] := by
  intro before x after same
  have h := congrArg List.length same
  simp only [List.length_nil, List.length_append, List.length_cons] at h
  omega

theorem RanksSatisfy.singleton {α : Type} {P : Nat → α → Prop} {offset : Nat} {x : α}
    (h : P offset x) : RanksSatisfy P offset [x] := by
  intro before y after same
  cases before with
  | nil => simpa using (List.cons.inj same).1 ▸ h
  | cons z zs =>
    have length := congrArg List.length same
    simp only [List.length_cons, List.length_nil, List.length_append] at length
    omega

theorem RanksSatisfy.append {α : Type} {P : Nat → α → Prop} {offset : Nat} {xs ys : List α}
    (left : RanksSatisfy P offset xs) (right : RanksSatisfy P (offset + xs.length) ys) :
    RanksSatisfy P offset (xs ++ ys) := by
  intro before x after same
  rcases List.append_eq_append_iff.mp same with ⟨extra, hbefore, hright⟩ | ⟨extra, hleft, hafter⟩
  · have h := right extra x after hright
    simpa only [hbefore, List.length_append, Nat.add_assoc] using h
  · cases extra with
    | nil =>
      simp only [List.append_nil] at hleft
      simp only [List.nil_append] at hafter
      have h := right [] x after hafter.symm
      simpa only [hleft, List.length_nil, Nat.add_zero] using h
    | cons y rest =>
      have first := (List.cons.inj hafter).1
      subst y
      exact left before x rest hleft

theorem block_length {α : Type} (frame : Frame α) :
    (lowerBlock frame).length = (framePayload frame).erase.size + 1 ∧
    (upperBlock frame).length = (framePayload frame).erase.size + 1 := by
  simp [lowerBlock, upperBlock, Representation.Bridge.inorder_length, Nat.add_comm]

theorem fringe_blocks_span {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (block : Frame α → List α) (fs : List (Frame α))
    (sizes : ∀ f ∈ fs, (block f).length = (payload (framePayload f)).size + 1) :
    fringeSpan (fs.map (fun f => (payload (framePayload f), frameMass weight f))) =
      (fs.flatMap block).length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.map_cons, List.flatMap_cons, List.length_append, fringeSpan,
      List.sum_cons] at *
    rw [sizes f (by simp), ih (fun g hg => sizes g (by simp [hg]))]

theorem inorder_weight {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) {x : α} (member : x ∈ t.inorder) :
    0 < weight x ∧ weight x ≤ HeavyPath.mass weight t := by
  induction t with
  | nil => cases member
  | node l y r ihL ihR =>
    have left := mass_nonnegative (positive_nonnegative positive.1)
    have right := mass_nonnegative (positive_nonnegative positive.2.2)
    have own := positive.2.1
    change _ ∧ _ ≤ HeavyPath.mass weight l + weight y + HeavyPath.mass weight r
    simp only [LabelledTree.inorder, List.mem_append, List.mem_cons] at member
    rcases member with hl | rfl | hr
    · obtain ⟨pos, bound⟩ := ihL positive.1 hl
      exact ⟨pos, by linarith⟩
    · exact ⟨own, by linarith⟩
    · obtain ⟨pos, bound⟩ := ihR positive.2.2 hr
      exact ⟨pos, by linarith⟩

/-- Match every block to its exact fringe occurrence. `shift = 0` places a
separator after its payload; `shift = 1` places it before its payload. -/
theorem fringe_blocks_ranks {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (block : Frame α → List α) (P : Nat → α → Prop) (shift : Nat)
    {whole : WeightedTree} (fs : List (Frame α))
    (sizes : ∀ f ∈ fs, (block f).length = (payload (framePayload f)).size + 1)
    (bound : ∀ f ∈ fs, ∀ offset depth,
      LocatedSlot whole (payload (framePayload f)) (frameMass weight f) offset depth →
      ∀ base, offset = base + shift → RanksSatisfy P base (block f))
    {before after : List (Tree × ℝ)} {base : Nat}
    (split : whole.fringe = before ++
      fs.map (fun f => (payload (framePayload f), frameMass weight f)) ++ after)
    (offset : fringeSpan before = base + shift) :
    RanksSatisfy P base (fs.flatMap block) := by
  induction fs generalizing before base with
  | nil => exact RanksSatisfy.nil _ _
  | cons f fs ih =>
    have headSplit : whole.fringe = before ++ (payload (framePayload f), frameMass weight f) ::
        (fs.map (fun g => (payload (framePayload g), frameMass weight g)) ++ after) := by
      simpa only [List.map_cons, List.append_assoc, List.cons_append] using split
    obtain ⟨depth, located⟩ := locate_split headSplit
    apply RanksSatisfy.append (bound f (by simp) _ depth located base offset)
    apply ih (fun g hg => sizes g (by simp [hg]))
      (fun g hg => bound g (by simp [hg])) (before := before ++ [(payload (framePayload f), frameMass weight f)])
    · simpa only [List.map_cons, List.append_assoc, List.singleton_append] using split
    · rw [fringeSpan_append, offset, sizes f (by simp)]
      simp only [fringeSpan, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega

end RotationBST.HeavyPath.Recursive
