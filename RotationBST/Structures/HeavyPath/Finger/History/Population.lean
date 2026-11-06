module

public import RotationBST.Structures.HeavyPath.Finger.History.Preservation
public import RotationBST.Structures.HeavyPath.Finger.Population.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History
open LabelledCursor

theorem focus_size_le {α : Type} (cs : List (Frame α)) (t : LabelledTree α) :
    t.erase.size ≤ (plug cs t).erase.size := by
  induction cs generalizing t with
  | nil => exact le_rfl
  | cons f cs ih =>
    cases f with
    | left key sibling =>
      have bound := ih (.node t key sibling)
      change t.erase.size ≤ (plug cs (.node t key sibling)).erase.size
      simp only [LabelledTree.erase, Tree.size] at bound
      omega
    | right sibling key =>
      have bound := ih (.node sibling key t)
      change t.erase.size ≤ (plug cs (.node sibling key t)).erase.size
      simp only [LabelledTree.erase, Tree.size] at bound
      omega

end RotationBST.HeavyPath.Finger.History
