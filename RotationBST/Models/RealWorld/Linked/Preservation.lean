module

public import RotationBST.Models.RealWorld.Linked.Rotation
import Mathlib.Tactic.FinCases

@[expose] public section
namespace RotationBST.RealWorld.Linked
open Cslib.PointerMachine (Pointer)
variable {w e regs : Nat}

set_option maxHeartbeats 800000 in
theorem pivot_left {h : List (Record w e regs)} {a b c : Tree w e} {x y : Label w e} {g : Pointer}
    (rx : Represents h (some y.1) (.node a x b))
    (ry : h[y.1]? = some (node (some x.1) (root c) g y))
    (rc : Represents h (some y.1) c)
    (nd : (addresses a ++ x.1 :: addresses b ++ y.1 :: addresses c).Nodup) :
    Represents (pivot h x.1 y.1 (root b) g 0 1) g (.node a x (.node b y c)) := by
  have hn := nd
  simp only [List.nodup_append, List.nodup_cons, List.mem_append, List.mem_cons] at hn
  have xy : x.1 ≠ y.1 := by grind
  have bx : root b ≠ some x.1 := by intro hb; have := root_mem hb; grind
  have byy : root b ≠ some y.1 := by intro hb; have := root_mem hb; grind
  refine ⟨?_, ?_, ?_⟩
  · simp [pivot, rx.1, Ne.symm xy, bx, node]
    funext i; fin_cases i <;> simp
  · apply represents_congr rx.2.1
    intro z hz
    have xz : x.1 ≠ z := by grind
    have yz : y.1 ≠ z := by grind
    have bz : root b ≠ some z := by intro hb; have := root_mem hb; grind
    simp [pivot_other _ _ _ _ _ _ _ _ xz yz, bz]
  · refine ⟨?_, ?_, ?_⟩
    · simp [pivot, ry, xy, byy, node]
      funext i; fin_cases i <;> simp
    · apply represents_reparent rx.2.2
      · intro z hz
        have xz : x.1 ≠ z := by grind
        have yz : y.1 ≠ z := by grind
        simpa only [eq_comm (a := some z) (b := root b)] using pivot_other h x.1 y.1 z (root b) g 0 1 xz yz
      · grind
    · apply represents_congr rc
      intro z hz
      have xz : x.1 ≠ z := by grind
      have yz : y.1 ≠ z := by grind
      have bz : root b ≠ some z := by intro hb; have := root_mem hb; grind
      simp [pivot_other _ _ _ _ _ _ _ _ xz yz, bz]

set_option maxHeartbeats 800000 in
theorem pivot_right {h : List (Record w e regs)} {a b c : Tree w e} {x y : Label w e} {g : Pointer}
    (rx : Represents h (some y.1) (.node b x c))
    (ry : h[y.1]? = some (node (root a) (some x.1) g y))
    (ra : Represents h (some y.1) a)
    (nd : (addresses a ++ y.1 :: addresses b ++ x.1 :: addresses c).Nodup) :
    Represents (pivot h x.1 y.1 (root b) g 1 0) g (.node (.node a y b) x c) := by
  have hn := nd
  simp only [List.nodup_append, List.nodup_cons, List.mem_append, List.mem_cons] at hn
  have xy : x.1 ≠ y.1 := by grind
  have bx : root b ≠ some x.1 := by intro hb; have := root_mem hb; grind
  have byy : root b ≠ some y.1 := by intro hb; have := root_mem hb; grind
  refine ⟨?_, ?_, ?_⟩
  · simp [pivot, rx.1, Ne.symm xy, bx, node]
    funext i; fin_cases i <;> simp
  · refine ⟨?_, ?_, ?_⟩
    · simp [pivot, ry, xy, byy, node]
      funext i; fin_cases i <;> simp
    · apply represents_congr ra
      intro z hz
      have xz : x.1 ≠ z := by grind
      have yz : y.1 ≠ z := by grind
      have bz : root b ≠ some z := by intro hb; have := root_mem hb; grind
      simp [pivot_other _ _ _ _ _ _ _ _ xz yz, bz]
    · apply represents_reparent rx.2.1
      · intro z hz
        have xz : x.1 ≠ z := by grind
        have yz : y.1 ≠ z := by grind
        simpa only [eq_comm (a := some z) (b := root b)] using
          pivot_other h x.1 y.1 z (root b) g 1 0 xz yz
      · grind
  · apply represents_congr rx.2.2
    intro z hz
    have xz : x.1 ≠ z := by grind
    have yz : y.1 ≠ z := by grind
    have bz : root b ≠ some z := by intro hb; have := root_mem hb; grind
    simp [pivot_other _ _ _ _ _ _ _ _ xz yz, bz]

def reconnected (h : List (Record w e regs)) (x y : Nat) (beta : Pointer)
    (cs : List (LabelledCursor.Frame (Label w e))) (side other : Fin 3) :=
  write (pivot h x y beta (parent cs) side other) (parent cs) (contextSide cs) (some x)

/-- Reconnect the locally rotated tree to its arbitrary ancestor context. -/
theorem reconnect {h : List (Record w e regs)} {t : Tree w e}
    {cs : List (LabelledCursor.Frame (Label w e))} {x y : Nat} {beta : Pointer}
    {side other : Fin 3}
    (localRep : Represents (pivot h x y beta (parent cs) side other) (parent cs) t)
    (ctx : Context h (some y) cs) (nd : (addresses t ++ outside cs).Nodup)
    (xm : x ∈ addresses t) (ym : y ∈ addresses t)
    (bm : ∀ z, beta = some z → z ∈ addresses t) (rt : root t = some x) :
    Represents (reconnected h x y beta cs side other) (parent cs) t ∧
    Context (reconnected h x y beta cs side other) (root t) cs := by
  have hn := nd
  simp only [List.nodup_append] at hn
  constructor
  · apply represents_congr localRep
    intro z hz
    exact write_other _ _ _ _ z (by
      intro heq; have := parent_mem heq; grind)
  · rw [rt]
    apply context_reconnect (p := some y) ?_ hn.2.1
    apply context_congr ctx
    intro z hz
    have xz : x ≠ z := by grind
    have yz : y ≠ z := by grind
    have bz : beta ≠ some z := by intro heq; have := bm z heq; grind
    simp [pivot_other _ _ _ _ _ _ _ _ xz yz, bz]

end RotationBST.RealWorld.Linked
