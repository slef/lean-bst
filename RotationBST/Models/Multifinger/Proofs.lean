module

public import RotationBST.Models.Multifinger.Definitions.Abstract
public import RotationBST.Models.Pointer.Keys
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Multifinger

theorem initial_valid (fingers : Nat) (t : Tree) (ht : 0 < t.size) : (initial fingers t).Valid := by
  intro i
  cases t with
  | nil => simp [Tree.size] at ht
  | node l r => simp [initial, Tree.size]; omega

theorem Step.size_eq {k : Nat} {s t : State k} {i : Fin k} (h : Step s i t) :
    s.tree.size = t.tree.size := by
  cases h with
  | execute ht _ hs _ => rw [← ht]; exact hs.size_eq

theorem Step.inactive {k : Nat} {s t : State k} {i : Fin k} (h : Step s i t)
    (j : Fin k) (hj : j ≠ i) : t.position j = s.position j := by
  cases h
  simp [Function.update, hj]

theorem Step.valid {k : Nat} {s t : State k} {i : Fin k} (h : Step s i t)
    (valid : s.Valid) : t.Valid := by
  have hsize := h.size_eq
  cases h with
  | execute _ _ hs hx =>
    intro j
    by_cases he : j = i
    · subst j
      simpa using Pointer.Config.key_lt_size _ _ hx
    · have hj := valid j
      simpa [Function.update, he, hsize] using hj

/-- The multifinger instruction relation contains every ordinary pointer step;
with one finger there are no inactive cursor positions to update. -/
theorem pointer_step {a b : Pointer.Config} {x y : Nat} (h : Pointer.Step a b)
    (ha : a.key? = some x) (hb : b.key? = some y) :
    Step (⟨a.tree, fun _ : Fin 1 => x⟩ : State 1) 0 ⟨b.tree, fun _ => y⟩ := by
  have he : Function.update (fun _ : Fin 1 => x) 0 y = (fun _ => y) := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp
  have hs : Step (⟨a.tree, fun _ : Fin 1 => x⟩ : State 1) 0
      ⟨b.tree, Function.update (fun _ => x) 0 y⟩ := .execute rfl ha h hb
  simpa only [he] using hs

theorem Trace.append {k : Nat} {s t u : State k} {xs ys : List Nat}
    (h : Trace s xs t) (g : Trace t ys u) : Trace s (xs ++ ys) u := by
  induction h with
  | refl => exact g
  | step hs _ ih => exact .step hs (ih g)

theorem Trace.size_eq {k : Nat} {s t : State k} {xs : List Nat} (h : Trace s xs t) :
    s.tree.size = t.tree.size := by
  induction h with
  | refl => rfl
  | step hs _ ih => exact hs.size_eq.trans ih

theorem Trace.valid {k : Nat} {s t : State k} {xs : List Nat} (h : Trace s xs t)
    (valid : s.Valid) : t.Valid := by
  induction h with
  | refl => exact valid
  | step hs _ ih => exact ih (hs.valid valid)

theorem Trace.touches_valid {k : Nat} {s t : State k} {xs : List Nat} (h : Trace s xs t)
    (valid : s.Valid) : ∀ x ∈ xs, x < s.tree.size := by
  induction h with
  | refl => simp
  | @step s t u i xs hs _ ih =>
    intro x hx
    have ht := hs.valid valid
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hs.size_eq]; exact ht i
    · have h := ih ht x hx
      rwa [← hs.size_eq] at h

theorem Serves.valid {k : Nat} {s t : State k} {x cost : Nat} (h : Serves s t x cost)
    (valid : s.Valid) : t.Valid ∧ x < s.tree.size ∧ 1 ≤ cost := by
  obtain ⟨visited, before, after, i, hb, hx, ha, hc⟩ := h
  have hv := hb.valid valid
  refine ⟨ha.valid hv, ?_, by omega⟩
  rw [← hx, hb.size_eq]
  exact hv i

theorem Execution.valid {k : Nat} {s t : State k} {xs : List Nat} {cost : Nat}
    (h : Execution s xs t cost) (valid : s.Valid) : t.Valid ∧ xs.length ≤ cost := by
  induction h with
  | nil => exact ⟨valid, Nat.zero_le _⟩
  | cons hs _ ih =>
    obtain ⟨hv, _, hc⟩ := hs.valid valid
    obtain ⟨ht, hlen⟩ := ih hv
    exact ⟨ht, by simp only [List.length_cons]; omega⟩

end RotationBST.Multifinger
