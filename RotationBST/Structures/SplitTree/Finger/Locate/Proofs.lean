module

public import RotationBST.Structures.SplitTree.Finger.Locate.Defs
public import RotationBST.Structures.SplitTree.Finger.Search

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Context

theorem valid_take {h : Nat} {fs : List Frame} (valid : Valid h fs) (n : Nat) : Valid h (fs.take n) := by
  induction n generalizing h fs with
  | zero => trivial
  | succ n ih =>
    cases fs with
    | nil => trivial
    | cons f fs => exact ⟨valid.1, ih valid.2⟩

theorem valid_drop {h : Nat} {fs : List Frame} (valid : Valid h fs) (n : Nat)
    (enough : n ≤ fs.length) : Valid (h + n) (fs.drop n) := by
  induction n generalizing h fs with
  | zero => exact valid
  | succ n ih =>
    cases fs with
    | nil => simp at enough
    | cons f fs =>
      have rest := ih valid.2 (by simpa using enough)
      simpa only [List.drop_succ_cons, Nat.add_assoc, Nat.add_comm 1 n] using rest

end RotationBST.Arboral.Split.Multiway.Context

namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

theorem locate_reconstruct (t : Multiway) (rank : Nat) :
    plug (locate t rank).outer (locate t rank).focus = t := by
  simp only [locate]
  rw [← plug_append, List.take_append_drop, leftSpine_plug]

theorem locate_balance {h : Nat} {t : Multiway} (valid : Balanced h t) (rank : Nat) :
    Balanced (locate t rank).height (locate t rank).focus ∧
      Valid (locate t rank).height (locate t rank).outer := by
  have spine := (leftSpine_balanced valid).1
  have enough := ascend_length (leftSpine t) .nil rank
  change searchLevels t rank ≤ (leftSpine t).length at enough
  have initial := plug_balanced _ (valid_take spine (searchLevels t rank)) Balanced.nil
  have suffix := valid_drop spine (searchLevels t rank) enough
  simp only [List.length_take, Nat.min_eq_left enough, Nat.zero_add] at initial suffix
  exact ⟨initial, suffix⟩

theorem locate_contains (t : Multiway) (rank : Nat) (existsKey : rank < t.size) :
    rank < (locate t rank).focus.size := searchLevels_contains t rank existsKey

theorem locate_height {h : Nat} {t : Multiway} (valid : Balanced h t) (rank : Nat) :
    (locate t rank).height ≤ Nat.log2 (rank + 1) + 1 := searchLevels_log valid rank

end RotationBST.Arboral.Split.Multiway.Finger
