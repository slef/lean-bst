module

public import RotationBST.Models.Pointer.Model

@[expose] public section

namespace RotationBST.Pointer

variable {a b c : Config} {k m : Nat}

def Config.under (c : Config) (ds : List Frame) : Config := ⟨c.focus, c.context ++ ds⟩

theorem Step.under (h : Step a b) (ds : List Frame) : Step (a.under ds) (b.under ds) := by
  cases h <;> simp only [Config.under, List.cons_append]
  · exact .downLeft
  · exact .downRight
  · exact .upLeft
  · exact .upRight
  · exact .rotateLeftChild
  · exact .rotateRightChild

theorem Trace.under (h : Trace a b k) (ds : List Frame) : Trace (a.under ds) (b.under ds) k := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (h.under ds) ih

theorem Trace.append (h : Trace a b k) (g : Trace b c m) : Trace a c (k + m) := by
  induction h with
  | refl => simpa using g
  | step h _ ih => simpa only [Nat.add_assoc, Nat.add_comm 1 m] using Trace.step h (ih g)

end RotationBST.Pointer

