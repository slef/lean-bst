module

public import RotationBST.Structures.SplitTree.Finger.Abstract
public import RotationBST.Structures.SplitTree.Multiway.Context.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Context

theorem plug_append (xs ys : List Frame) (t : Multiway) :
    plug (xs ++ ys) t = plug ys (plug xs t) := by
  induction xs generalizing t with
  | nil => rfl
  | cons f fs ih => exact ih _

theorem valid_append {h : Nat} {xs ys : List Frame} (first : Valid h xs)
    (rest : Valid (h + xs.length) ys) : Valid h (xs ++ ys) := by
  induction xs generalizing h with
  | nil => exact rest
  | cons f fs ih =>
    refine ⟨first.1, ih first.2 ?_⟩
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using rest

end RotationBST.SplitTree.Multiway.Context

namespace RotationBST.SplitTree.Multiway.Finger
open Context

/-- The finger stores every ancestor and every off-path subtree exactly once. -/
theorem leftSpine_plug (t : Multiway) : plug (leftSpine t) .nil = t := by
  induction t <;> simp only [leftSpine, plug_append, plug, Frame.fill] <;> congr

theorem leftSpine_balanced {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Valid 0 (leftSpine t) ∧ (leftSpine t).length = h := by
  induction valid with
  | nil => exact ⟨trivial, rfl⟩
  | two ha hb ia ib =>
    refine ⟨valid_append ia.1 ?_, ?_⟩
    · rw [ia.2, Nat.zero_add]
      exact ⟨hb, trivial⟩
    · simp [leftSpine, ia.2]
  | three ha hb hc ia ib ic =>
    refine ⟨valid_append ia.1 ?_, ?_⟩
    · rw [ia.2, Nat.zero_add]
      exact ⟨⟨hb, hc⟩, trivial⟩
    · simp [leftSpine, ia.2]
  | four ha hb hc hd ia ib ic id =>
    refine ⟨valid_append ia.1 ?_, ?_⟩
    · rw [ia.2, Nat.zero_add]
      exact ⟨⟨hb, hc, hd⟩, trivial⟩
    · simp [leftSpine, ia.2]

end RotationBST.SplitTree.Multiway.Finger
