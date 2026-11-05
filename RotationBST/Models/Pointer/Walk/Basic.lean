module

public import RotationBST.Models.Pointer.Walk.Definitions.Abstract
public import RotationBST.Models.Pointer.Search
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Pointer

theorem Move.step {a b : Config} (move : Move a b) : Step a b := by cases move <;> constructor

theorem Move.tree_eq {a b : Config} (move : Move a b) : a.tree = b.tree := by cases move <;> rfl

theorem Move.symm {a b : Config} (move : Move a b) : Move b a := by cases move <;> constructor

theorem Move.under {a b : Config} (move : Move a b) (cs : List Frame) : Move (a.under cs) (b.under cs) := by
  cases move <;> simp only [Config.under, List.cons_append] <;> constructor

theorem Walk.trace {a b : Config} {k : Nat} (walk : Walk a b k) : Trace a b k := by
  induction walk with
  | refl => exact .refl
  | step move _ ih => exact .step move.step ih

theorem Walk.tree_eq {a b : Config} {k : Nat} (walk : Walk a b k) : a.tree = b.tree := by
  induction walk with
  | refl => rfl
  | step move _ ih => exact move.tree_eq.trans ih

theorem Walk.append {a b c : Config} {k h : Nat} (first : Walk a b k) (last : Walk b c h) : Walk a c (k + h) := by
  induction first with
  | refl => simpa using last
  | step move _ ih => simpa only [Nat.add_assoc, Nat.add_comm 1 h] using Walk.step move (ih last)

theorem Walk.under {a b : Config} {k : Nat} (walk : Walk a b k) (cs : List Frame) :
    Walk (a.under cs) (b.under cs) k := by
  induction walk with
  | refl => exact .refl
  | step move _ ih => exact .step (move.under cs) ih

theorem walk_descend (cs : List Frame) (l r : Tree) :
    Walk ⟨plug cs (.node l r), []⟩ ⟨.node l r, cs⟩ cs.length := by
  induction cs generalizing l r with
  | nil => exact .refl
  | cons c cs ih =>
    cases c with
    | left b => exact (ih (.node l r) b).append (.step .downLeft .refl)
    | right a => exact (ih a (.node l r)).append (.step .downRight .refl)

theorem walk_ascend (cs : List Frame) (l r : Tree) :
    Walk ⟨.node l r, cs⟩ ⟨plug cs (.node l r), []⟩ cs.length := by
  induction cs generalizing l r with
  | nil => exact .refl
  | cons c cs ih =>
    cases c with
    | left b => exact .step .upLeft (ih (.node l r) b)
    | right a => exact .step .upRight (ih a (.node l r))

theorem search_readonly (t : Tree) (x : Nat) (valid : x < t.size) :
    ∃ c : Config, c.tree = t ∧ c.key? = some x ∧
      Walk ⟨t, []⟩ c (Tree.depth t x) ∧ Walk c ⟨t, []⟩ (Tree.depth t x) := by
  obtain ⟨l, r, cs, tree, key, depth⟩ := search_location t x valid
  exact ⟨⟨.node l r, cs⟩, tree, congrArg some key,
    by simpa only [tree, depth] using walk_descend cs l r,
    by simpa only [tree, depth] using walk_ascend cs l r⟩

end RotationBST.Pointer
