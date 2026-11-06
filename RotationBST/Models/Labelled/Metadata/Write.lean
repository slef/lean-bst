module

public import RotationBST.Models.Labelled.Metadata.Pointer
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Metadata

theorem Write.member {α : Type} {s t : LabelledTree (Nat × α)} {key : Nat} {value : α}
    (write : Write s key value t) : key ∈ s.inorder.map Prod.fst := by
  induction write <;> simp_all [LabelledTree.inorder]

/-- Unique keys make replacing one named node's payload deterministic. -/
theorem Write.unique {α : Type} {s t u : LabelledTree (Nat × α)} {key : Nat} {value : α}
    (first : Write s key value t) (second : Write s key value u)
    (unique : (s.inorder.map Prod.fst).Nodup) : t = u := by
  induction first generalizing u with
  | root l r x old value =>
    cases second with
    | root => rfl
    | left write =>
      simp only [LabelledTree.inorder, List.map_append, List.map_cons, List.nodup_append] at unique
      exact False.elim (unique.2.2 x write.member x (List.mem_cons_self ..) rfl)
    | right write =>
      simp only [LabelledTree.inorder, List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at unique
      exact False.elim (unique.2.1.1 write.member)
  | @left l l' r entry x value write ih =>
    cases second with
    | root =>
      simp only [LabelledTree.inorder, List.map_append, List.map_cons, List.nodup_append] at unique
      exact False.elim (unique.2.2 x write.member x (List.mem_cons_self ..) rfl)
    | left other =>
      simp only [LabelledTree.inorder, List.map_append, List.map_cons, List.nodup_append] at unique
      rw [ih other unique.1]
    | right other =>
      simp only [LabelledTree.inorder, List.map_append, List.map_cons, List.nodup_append] at unique
      exact False.elim (unique.2.2 x write.member x (List.mem_cons_of_mem _ other.member) rfl)
  | @right l r r' entry x value write ih =>
    cases second with
    | root =>
      simp only [LabelledTree.inorder, List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at unique
      exact False.elim (unique.2.1.1 write.member)
    | left other =>
      simp only [LabelledTree.inorder, List.map_append, List.map_cons, List.nodup_append] at unique
      exact False.elim (unique.2.2 x other.member x (List.mem_cons_of_mem _ write.member) rfl)
    | right other =>
      simp only [LabelledTree.inorder, List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at unique
      rw [ih other unique.2.1.2]

theorem Write.erase {α : Type} {s t : LabelledTree (Nat × α)} {key : Nat} {value : α}
    (write : Write s key value t) : s.erase = t.erase := by
  induction write <;> simp_all only [LabelledTree.erase]

theorem write_result {α : Type} (data : Nat → α) {s t : LabelledTree (Nat × α)} {key : Nat} {value : α}
    (write : Write s key value t) (stored : s = label data s.erase 0) :
    t = label (Function.update data key value) t.erase 0 := by
  have keys : s.inorder.map Prod.fst = List.range' 0 s.erase.size := by
    conv_lhs => rw [stored]
    simp [label_inorder, List.map_map, Function.comp_def]
  have present := write.member
  rw [keys] at present
  have valid : key < s.erase.size := by simpa using present
  have expected := label_write data value s.erase 0 key (Nat.zero_le _) (by simpa using valid)
  rw [← stored] at expected
  have unique : (s.inorder.map Prod.fst).Nodup := by rw [keys]; exact List.nodup_range'
  have result := write.unique expected unique
  simpa only [write.erase] using result

theorem Write.plug {α : Type} {s t : LabelledTree (Nat × α)} {key : Nat} {value : α}
    (write : Write s key value t) (cs : List (LabelledCursor.Frame (Nat × α))) :
    Write (LabelledCursor.plug cs s) key value (LabelledCursor.plug cs t) := by
  induction cs generalizing s t with
  | nil => exact write
  | cons frame cs ih => cases frame with
    | left entry r => exact ih (.left write)
    | right l entry => exact ih (.right write)

theorem cursor_write {α : Type} {s t : LabelledCursor.Config (Nat × α)} {key : Nat} {old value : α}
    (read : s.read = some (key, old)) (write : s.write (key, value) = some t) :
    Write s.tree key value t.tree := by
  rcases s with ⟨focus, cs⟩
  cases focus with
  | nil => simp [LabelledCursor.Config.read] at read
  | node l entry r =>
    cases Option.some.inj read
    cases Option.some.inj write
    exact (Write.root l r key old value).plug cs

theorem At.plug {α : Type} {tree : LabelledTree (Nat × α)} {key : Nat} {value : α}
    (atNode : At tree key value) (cs : List (LabelledCursor.Frame (Nat × α))) :
    At (LabelledCursor.plug cs tree) key value := by
  induction cs generalizing tree with
  | nil => exact atNode
  | cons frame cs ih => cases frame with
    | left entry r => exact ih (.left atNode)
    | right l entry => exact ih (.right atNode)

theorem cursor_read {α : Type} {c : LabelledCursor.Config (Nat × α)} {key : Nat} {value : α}
    (read : c.read = some (key, value)) : At c.tree key value := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => simp [LabelledCursor.Config.read] at read
  | node l entry r =>
    cases Option.some.inj read
    exact (At.root l r key value).plug cs

end RotationBST.Metadata
