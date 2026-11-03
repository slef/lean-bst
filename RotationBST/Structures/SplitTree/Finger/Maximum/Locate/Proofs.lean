module

public import RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Defs
public import RotationBST.Structures.SplitTree.Finger.Locate.Proofs
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Context.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger
open Context

/-- The finger stores every ancestor and every off-path subtree exactly once. -/
theorem rightSpine_plug (t : Multiway) : plug (rightSpine t) .nil = t := by
  induction t <;> simp only [rightSpine, plug_append, plug, Frame.fill] <;> congr

theorem rightSpine_balanced {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Valid 0 (rightSpine t) ∧ (rightSpine t).length = h := by
  induction valid with
  | nil => exact ⟨trivial, rfl⟩
  | two ha hb ia ib =>
    refine ⟨valid_append ib.1 ?_, ?_⟩
    · rw [ib.2, Nat.zero_add]
      exact ⟨ha, trivial⟩
    · simp [rightSpine, ib.2]
  | three ha hb hc ia ib ic =>
    refine ⟨valid_append ic.1 ?_, ?_⟩
    · rw [ic.2, Nat.zero_add]
      exact ⟨⟨ha, hb⟩, trivial⟩
    · simp [rightSpine, ic.2]
  | four ha hb hc hd ia ib ic id =>
    refine ⟨valid_append id.1 ?_, ?_⟩
    · rw [id.2, Nat.zero_add]
      exact ⟨⟨ha, hb, hc⟩, trivial⟩
    · simp [rightSpine, id.2]

theorem locateMaximum_reconstruct (t : Multiway) (rank : Nat) :
    plug (locateMaximum t rank).outer (locateMaximum t rank).focus = t := by
  simp only [locateMaximum]
  rw [← plug_append, List.take_append_drop, rightSpine_plug]

theorem locateMaximum_balance {h : Nat} {t : Multiway} (valid : Balanced h t) (rank : Nat) :
    Balanced (locateMaximum t rank).height (locateMaximum t rank).focus ∧
      Valid (locateMaximum t rank).height (locateMaximum t rank).outer := by
  have spine := (rightSpine_balanced valid).1
  have enough := ascend_length (rightSpine t) .nil rank
  change ascend (rightSpine t) .nil rank ≤ (rightSpine t).length at enough
  have initial := plug_balanced _ (valid_take spine (ascend (rightSpine t) .nil rank)) Balanced.nil
  have suffix := valid_drop spine (ascend (rightSpine t) .nil rank) enough
  simp only [List.length_take, Nat.min_eq_left enough, Nat.zero_add] at initial suffix
  exact ⟨initial, suffix⟩

theorem locateMaximum_contains (t : Multiway) (distance : Nat) (existsKey : distance < t.size) :
    distance < (locateMaximum t distance).focus.size := by
  apply ascend_contains
  rwa [rightSpine_plug]

theorem locateMaximum_height {h : Nat} {t : Multiway} (valid : Balanced h t) (distance : Nat) :
    (locateMaximum t distance).height ≤ Nat.log2 (distance + 1) + 1 :=
  ascend_log (rightSpine t) distance (rightSpine_balanced valid).1 Balanced.nil (by omega)

theorem rightSpine_frames (t : Multiway) : ∀ f ∈ rightSpine t, IsRightFrame f := by
  induction t with
  | nil => simp [rightSpine]
  | two a b ia ib =>
    intro f member
    simp only [rightSpine, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact ib f member
    · trivial
  | three a b c ia ib ic =>
    intro f member
    simp only [rightSpine, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact ic f member
    · trivial
  | four a b c d ia ib ic id =>
    intro f member
    simp only [rightSpine, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact id f member
    · trivial

theorem locateMaximum_view (t : Multiway) (rank : Nat) :
    (maximumView t).tree = maximumEnclosingView (locateMaximum t rank).focus (locateMaximum t rank).outer := by
  calc
    (maximumView t).tree = (maximumView (plug (locateMaximum t rank).outer (locateMaximum t rank).focus)).tree :=
      congrArg (fun u => (maximumView u).tree) (locateMaximum_reconstruct t rank).symm
    _ = _ := maximumEnclosingView_eq _ _ (by
      intro f member
      exact rightSpine_frames t f (List.mem_of_mem_drop member))

end RotationBST.SplitTree.Multiway.Finger
