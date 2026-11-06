module

public import RotationBST.Structures.TreeBuffer.Nodes.Initialization.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Nodes.Initialization
open LabelledCursor
open IntervalMetadata.Initialization (work)

theorem Run.append {α : Type} {s t u : State α} {a b : Nat} (first : Run s t a) (last : Run t u b) :
    Run s u (a + b) := by
  induction first with
  | refl => simpa using last
  | step first _ ih => simpa only [Nat.add_assoc] using Run.step first (ih last)

private theorem visit_left {α : Type} (l : Tree) (r : LabelledTree (Entry α))
    (cs : List (Frame (Entry α))) (fields : Nat → IntervalMetadata.Bounds) (data : Nat → α)
    (lo high : Nat) (pending : IntervalMetadata.Bounds)
    (child : l ≠ .nil → ∀ (lo : Nat) (cs : List (Frame (Entry α))), ∃ final,
      Run ⟨⟨raw fields data l lo, cs⟩, ⟨lo, lo + l.size⟩, .write⟩
        ⟨⟨label data l lo, cs⟩, final, .up⟩ (work l)) :
    ∃ final, Run ⟨⟨.node (raw fields data l lo) ⟨lo + l.size, ⟨lo, high⟩, data (lo + l.size)⟩ r, cs⟩, pending, .left⟩
      ⟨⟨.node (label data l lo) ⟨lo + l.size, ⟨lo, high⟩, data (lo + l.size)⟩ r, cs⟩, final, .right⟩
      (if l = .nil then 1 else 5 + work l) := by
  cases l with
  | nil => exact ⟨pending, .step rfl .refl⟩
  | node a b =>
    obtain ⟨final, run⟩ := child (by simp) lo (.left ⟨lo + (Tree.node a b).size, ⟨lo, high⟩, data (lo + (Tree.node a b).size)⟩ r :: cs)
    have leave : Run ⟨⟨label data (.node a b) lo, .left ⟨lo + (Tree.node a b).size, ⟨lo, high⟩, data (lo + (Tree.node a b).size)⟩ r :: cs⟩, final, .up⟩
        ⟨⟨.node (label data (.node a b) lo) ⟨lo + (Tree.node a b).size, ⟨lo, high⟩, data (lo + (Tree.node a b).size)⟩ r, cs⟩, final, .right⟩ 1 :=
      .step rfl .refl
    refine ⟨final, ?_⟩
    have cost : 4 + (work (.node a b) + 1) = 5 + work (.node a b) := by omega
    simpa only [reduceCtorEq, ↓reduceIte, cost] using Run.step (cost := 4) rfl (run.append leave)

private theorem visit_right {α : Type} (l : LabelledTree (Entry α)) (r : Tree)
    (cs : List (Frame (Entry α))) (fields : Nat → IntervalMetadata.Bounds) (data : Nat → α)
    (lo key : Nat) (pending : IntervalMetadata.Bounds)
    (child : r ≠ .nil → ∀ (lo : Nat) (cs : List (Frame (Entry α))), ∃ final,
      Run ⟨⟨raw fields data r lo, cs⟩, ⟨lo, lo + r.size⟩, .write⟩
        ⟨⟨label data r lo, cs⟩, final, .up⟩ (work r)) :
    ∃ final, Run ⟨⟨.node l ⟨key, ⟨lo, key + 1 + r.size⟩, data key⟩ (raw fields data r (key + 1)), cs⟩, pending, .right⟩
      ⟨⟨.node l ⟨key, ⟨lo, key + 1 + r.size⟩, data key⟩ (label data r (key + 1)), cs⟩, final, .up⟩
      (if r = .nil then 1 else 5 + work r) := by
  cases r with
  | nil => exact ⟨pending, .step rfl .refl⟩
  | node a b =>
    obtain ⟨final, run⟩ := child (by simp) (key + 1) (.right l ⟨key, ⟨lo, key + 1 + (Tree.node a b).size⟩, data key⟩ :: cs)
    have leave : Run ⟨⟨label data (.node a b) (key + 1), .right l ⟨key, ⟨lo, key + 1 + (Tree.node a b).size⟩, data key⟩ :: cs⟩, final, .up⟩
        ⟨⟨.node l ⟨key, ⟨lo, key + 1 + (Tree.node a b).size⟩, data key⟩ (label data (.node a b) (key + 1)), cs⟩, final, .up⟩ 1 :=
      .step rfl .refl
    refine ⟨final, ?_⟩
    have cost : 4 + (work (.node a b) + 1) = 5 + work (.node a b) := by omega
    simpa only [reduceCtorEq, ↓reduceIte, cost] using Run.step (cost := 4) rfl (run.append leave)

/-- The proof recurses over the tree; the executed machine uses only its
cursor, mode, and two bound registers and returns through parent links. -/
theorem traversal {α : Type} (tree : Tree) (nonempty : tree ≠ .nil)
    (fields : Nat → IntervalMetadata.Bounds) (data : Nat → α) (lo : Nat) (cs : List (Frame (Entry α))) :
    ∃ final, Run ⟨⟨raw fields data tree lo, cs⟩, ⟨lo, lo + tree.size⟩, .write⟩
      ⟨⟨label data tree lo, cs⟩, final, .up⟩ (work tree) := by
  induction tree generalizing lo cs with
  | nil => exact False.elim (nonempty rfl)
  | node l r il ir =>
    obtain ⟨middle, leftRun⟩ := visit_left l (raw fields data r (lo + l.size + 1)) cs fields data lo
      (lo + (Tree.node l r).size) ⟨lo, lo + (Tree.node l r).size⟩ il
    obtain ⟨final, rightRun⟩ := visit_right (label data l lo) r cs fields data lo (lo + l.size) middle ir
    have high : lo + (Tree.node l r).size = lo + l.size + 1 + r.size := by simp only [Tree.size]; omega
    rw [← high] at rightRun
    refine ⟨final, ?_⟩
    simpa only [work, raw, label, Nat.add_assoc] using
      Run.step (cost := 2) (s := ⟨⟨raw fields data (.node l r) lo, cs⟩, ⟨lo, lo + (Tree.node l r).size⟩, .write⟩)
        rfl (leftRun.append rightRun)

end RotationBST.TreeBuffer.Nodes.Initialization
