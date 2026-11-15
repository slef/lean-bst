module

public import RotationBST.Models.RealWorld.Linked.Execution
import Mathlib.Tactic.FinCases

@[expose] public section
namespace RotationBST.RealWorld.Linked
open Cslib.PointerMachine (Pointer)
variable {w e regs : Nat}

@[simp] theorem root_node (l r : Tree w e) (x : Label w e) :
    root (.node l x r) = some x.1 := rfl


/-- Addresses belonging to the ancestors and siblings, excluding the focus. -/
def outside : List (LabelledCursor.Frame (Label w e)) → List Nat
  | [] => []
  | .left x r :: cs => x.1 :: addresses r ++ outside cs
  | .right l x :: cs => x.1 :: addresses l ++ outside cs

@[simp] theorem addresses_node (a b : Tree w e) (x : Label w e) :
    addresses (.node a x b) = addresses a ++ x.1 :: addresses b := by
  simp [addresses, LabelledTree.inorder]

theorem represents_congr {h k : List (Record w e regs)} {t : Tree w e} {p : Pointer}
    (rep : Represents h p t) (agree : ∀ a ∈ addresses t, k[a]? = h[a]?) :
    Represents k p t := by
  induction t generalizing p with
  | nil => trivial
  | node l x r il ir =>
    refine ⟨?_, il rep.2.1 ?_, ir rep.2.2 ?_⟩
    · rw [agree x.1 (by simp), rep.1]
    · intro a ha; exact agree a (by simp [ha])
    · intro a ha; exact agree a (by simp [ha])

theorem context_congr {h k : List (Record w e regs)}
    {cs : List (LabelledCursor.Frame (Label w e))} {p : Pointer}
    (rep : Context h p cs) (agree : ∀ a ∈ outside cs, k[a]? = h[a]?) : Context k p cs := by
  induction cs generalizing p with
  | nil => trivial
  | cons f cs ih =>
    cases f with
    | left x r =>
      refine ⟨?_, represents_congr rep.2.1 ?_, ih rep.2.2 ?_⟩
      · rw [agree x.1 (by simp [outside]), rep.1]
      · intro a ha; exact agree a (by simp [outside, ha])
      · intro a ha; exact agree a (by simp [outside, ha])
    | right l x =>
      refine ⟨?_, represents_congr rep.2.1 ?_, ih rep.2.2 ?_⟩
      · rw [agree x.1 (by simp [outside]), rep.1]
      · intro a ha; exact agree a (by simp [outside, ha])
      · intro a ha; exact agree a (by simp [outside, ha])

/-- Changing only the root's parent field reparents a subtree. -/
theorem represents_reparent {h k : List (Record w e regs)} {t : Tree w e} {p q : Pointer}
    (rep : Represents h p t)
    (change : ∀ a ∈ addresses t,
      k[a]? = (h[a]?).map (fun n => if some a = root t then
        { n with ptr := Function.update n.ptr 2 q } else n))
    (distinct : (addresses t).Nodup) : Represents k q t := by
  cases t with
  | nil => trivial
  | node l x r =>
    have nd := distinct
    simp only [addresses_node, List.nodup_append, List.nodup_cons] at nd
    refine ⟨?_, represents_congr rep.2.1 ?_, represents_congr rep.2.2 ?_⟩
    · rw [change x.1 (by simp), rep.1]
      simp [root, node]
      funext f
      fin_cases f <;> simp
    · intro a ha
      have ne : a ≠ x.1 := by grind
      simpa [root, ne] using change a (by simp [ha])
    · intro a ha
      have ne : a ≠ x.1 := by grind
      simpa [root, ne] using change a (by simp [ha])

theorem nodup_plug (cs : List (LabelledCursor.Frame (Label w e))) (t : Tree w e) :
    (addresses (LabelledCursor.plug cs t)).Nodup ↔ (addresses t ++ outside cs).Nodup := by
  induction cs generalizing t with
  | nil => simp [LabelledCursor.plug, outside]
  | cons f cs ih =>
    cases f <;>
      simp only [LabelledCursor.plug, ih, outside, addresses_node, List.nodup_append,
        List.nodup_cons, List.mem_append, List.mem_cons] <;> grind

theorem root_mem {t : Tree w e} {a : Nat} (h : root t = some a) : a ∈ addresses t := by
  cases t <;> simp_all [root]

theorem parent_mem {cs : List (LabelledCursor.Frame (Label w e))} {a : Nat}
    (h : parent cs = some a) : a ∈ outside cs := by
  cases cs with
  | nil => simp [parent] at h
  | cons f cs => cases f <;> simp_all [parent, outside]

def contextSide : List (LabelledCursor.Frame (Label w e)) → Fin 3
  | .right .. :: _ => 1
  | _ => 0

end RotationBST.RealWorld.Linked
