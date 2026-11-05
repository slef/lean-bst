module

public import RotationBST.Models.Pointer.Lazy.Skeleton

@[expose] public section
namespace RotationBST.Pointer.Lazy.Skeleton

theorem fillMin_fringe (s t : Skeleton) :
    (s.fillMin t).fringe = t.fringe ++ s.fringe.tail := by
  induction s with
  | hole => simp [fillMin, fringe]
  | node l r ih _ =>
    have h := l.fringe_ne_nil
    cases hf : l.fringe with
    | nil => exact False.elim (h hf)
    | cons a as => simp [fillMin, fringe, ih, hf, List.append_assoc]

theorem fillMax_fringe (s t : Skeleton) :
    (s.fillMax t).fringe = s.fringe.dropLast ++ t.fringe := by
  induction s with
  | hole => simp [fillMax, fringe]
  | node l r _ ih =>
    simp [fillMax, fringe, ih, List.dropLast_append_of_ne_nil r.fringe_ne_nil,
      List.append_assoc]

theorem fillMin_size (s t : Skeleton) : (s.fillMin t).size = s.size + t.size := by
  induction s with
  | hole => simp [fillMin, size]
  | node l r ih _ => simp [fillMin, size, ih]; omega

theorem fillMax_size (s t : Skeleton) : (s.fillMax t).size = s.size + t.size := by
  induction s with
  | hole => simp [fillMax, size]
  | node l r _ ih => simp [fillMax, size, ih, Nat.add_assoc]

theorem under_tree (s : Skeleton) (cs : List Frame) : (s.under cs).tree = plug cs s.tree := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [under, plug, ih, tree]

theorem under_size (s : Skeleton) (cs : List Frame) : (s.under cs).size = s.size + cs.length := by
  induction cs generalizing s with
  | nil => simp [under]
  | cons c cs ih => cases c <;> simp [under, size, ih] <;> omega

end RotationBST.Pointer.Lazy.Skeleton
