module

public import RotationBST.Models.Pointer.Traces

@[expose] public section
namespace RotationBST.Pointer

theorem plug_append (cs ds : List Frame) (t : Tree) :
    plug (cs ++ ds) t = plug ds (plug cs t) := by
  induction cs generalizing t with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [List.cons_append, plug, ih]

theorem offset_append (cs ds : List Frame) : offset (cs ++ ds) = offset cs + offset ds := by
  induction cs with
  | nil => simp [offset]
  | cons c cs ih => cases c <;> simp [offset, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem plug_size_congr (cs : List Frame) {s t : Tree} (h : s.size = t.size) :
    (plug cs s).size = (plug cs t).size := by
  induction cs generalizing s t with
  | nil => exact h
  | cons c cs ih =>
    cases c <;> apply ih <;> simp only [Tree.size, h]

/-- Navigate to any existing focused node without changing the tree. -/
theorem descend (cs : List Frame) (l r : Tree) :
    Trace ⟨plug cs (.node l r), []⟩ ⟨.node l r, cs⟩ cs.length := by
  induction cs generalizing l r with
  | nil => exact .refl
  | cons c cs ih =>
    cases c with
    | left b =>
      exact (ih (.node l r) b).append (.step .downLeft .refl)
    | right a =>
      exact (ih a (.node l r)).append (.step .downRight .refl)

/-- Return to the root with one parent move per ancestor. -/
theorem ascend (cs : List Frame) (l r : Tree) :
    Trace ⟨.node l r, cs⟩ ⟨plug cs (.node l r), []⟩ cs.length := by
  induction cs generalizing l r with
  | nil => exact .refl
  | cons c cs ih =>
    cases c with
    | left b => exact .step .upLeft (ih (.node l r) b)
    | right a => exact .step .upRight (ih a (.node l r))

theorem plug_ne_nil (cs : List Frame) {t : Tree} (h : t ≠ .nil) : plug cs t ≠ .nil := by
  induction cs generalizing t with
  | nil => exact h
  | cons c cs ih => cases c <;> exact ih (by simp)

theorem moveUp (f : Frame) (cs : List Frame) {t : Tree} (h : t ≠ .nil) :
    Trace ⟨t, f :: cs⟩ ⟨plug [f] t, cs⟩ 1 := by
  cases t with
  | nil => exact False.elim (h rfl)
  | node l r => cases f <;> exact .step (by constructor) .refl

theorem moveDown (f : Frame) (cs : List Frame) {t : Tree} (h : t ≠ .nil) :
    Trace ⟨plug [f] t, cs⟩ ⟨t, f :: cs⟩ 1 := by
  cases t with
  | nil => exact False.elim (h rfl)
  | node l r => cases f <;> exact .step (by constructor) .refl

/-- Execute a root-to-root trace in an embedded nonempty subtree, charging the
descent and return explicitly. -/
theorem Trace.inContext {s t : Tree} {k : Nat}
    (h : Trace ⟨s, []⟩ ⟨t, []⟩ k) (hs : s ≠ .nil) (ht : t ≠ .nil) (cs : List Frame) :
    Trace ⟨plug cs s, []⟩ ⟨plug cs t, []⟩ (cs.length + k + cs.length) := by
  cases s with
  | nil => exact False.elim (hs rfl)
  | node a b =>
    cases t with
    | nil => exact False.elim (ht rfl)
    | node c d => exact ((descend cs a b).append (h.under cs)).append (ascend cs c d)

end RotationBST.Pointer
