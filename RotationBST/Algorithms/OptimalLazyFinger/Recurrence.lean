module

public import RotationBST.Algorithms.OptimalLazyFinger.Definitions.Abstract
public import RotationBST.Bounds.LazyFinger.Edges.Sequence
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.OptimalLazyFinger
open LazyFinger

theorem minimum_property (P : Entry → Prop) (initial : Entry) (cs : List Entry)
    (hi : P initial) (hc : ∀ c ∈ cs, P c) : P (minimum initial cs) := by
  induction cs with
  | nil => exact hi
  | cons c cs ih =>
    have hp := hc c (by simp)
    have hq := ih (fun d hd => hc d (by simp [hd]))
    change P (choose c (minimum initial cs))
    unfold choose
    split <;> assumption

theorem minimum_le_initial (initial : Entry) (cs : List Entry) :
    (minimum initial cs).2 ≤ initial.2 := by
  induction cs with
  | nil => exact le_rfl
  | cons c cs ih =>
    change (choose c (minimum initial cs)).2 ≤ initial.2
    unfold choose
    split
    · rename_i h; exact h.trans ih
    · exact ih

theorem minimum_le_mem (initial : Entry) (cs : List Entry) (c : Entry) (hc : c ∈ cs) :
    (minimum initial cs).2 ≤ c.2 := by
  induction cs with
  | nil => simp at hc
  | cons d ds ih =>
    change (choose d (minimum initial ds)).2 ≤ c.2
    rcases List.mem_cons.mp hc with rfl | hc
    · unfold choose
      split
      · exact le_rfl
      · rename_i h; omega
    · have hb := ih hc
      unfold choose
      split
      · rename_i h; exact h.trans hb
      · exact hb

/-- The recurrence constructs a shape of the requested size, reports its exact
cost, and minimizes the boundary objective over every shape of that size. -/
theorem solve_spec (w : Nat → Nat → Nat) (n lo : Nat) :
    (solve w n lo).1.size = n ∧
      intervalCost w (solve w n lo).1 lo = (solve w n lo).2 ∧
      ∀ t : Tree, t.size = n → (solve w n lo).2 ≤ intervalCost w t lo := by
  induction n using Nat.strong_induction_on generalizing lo with
  | ind n ih =>
    cases n with
    | zero =>
      simp only [solve, Tree.size, intervalCost, true_and]
      intro t _
      exact Nat.zero_le _
    | succ n =>
      let candidate (k : Fin (n + 1)) : Entry :=
        let l := solve w k.val lo
        let r := solve w (n - k.val) (lo + k.val + 1)
        (.node l.1 r.1, w lo (lo + n + 1) + l.2 + r.2)
      have hs : solve w (n + 1) lo =
          minimum (candidate ⟨0, Nat.zero_lt_succ n⟩) ((List.finRange (n + 1)).map candidate) := by
        rw [solve]
      have hc (k : Fin (n + 1)) : (candidate k).1.size = n + 1 ∧
          intervalCost w (candidate k).1 lo = (candidate k).2 := by
        obtain ⟨hl, hlc, _⟩ := ih k.val k.isLt lo
        obtain ⟨hr, hrc, _⟩ := ih (n - k.val) (by omega) (lo + k.val + 1)
        dsimp [candidate]
        constructor
        · simp only [Tree.size, hl, hr]; omega
        · simp only [intervalCost, Tree.size, hl, hr, hlc, hrc]
          have he : lo + (k.val + 1 + (n - k.val)) = lo + n + 1 := by omega
          rw [he]
      have hm := minimum_property
        (fun c : Entry => c.1.size = n + 1 ∧ intervalCost w c.1 lo = c.2)
        (candidate ⟨0, Nat.zero_lt_succ n⟩) ((List.finRange (n + 1)).map candidate)
        (hc _) (by
          intro c hmem
          obtain ⟨k, _, rfl⟩ := List.mem_map.mp hmem
          exact hc k)
      rw [← hs] at hm
      refine ⟨hm.1, hm.2, ?_⟩
      intro t ht
      cases t with
      | nil => simp [Tree.size] at ht
      | node l r =>
        have hk : l.size < n + 1 := by simp only [Tree.size] at ht; omega
        have hr : n - l.size = r.size := by simp only [Tree.size] at ht; omega
        let k : Fin (n + 1) := ⟨l.size, hk⟩
        have hmem : candidate k ∈ (List.finRange (n + 1)).map candidate :=
          List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
        have hb := minimum_le_mem (candidate ⟨0, Nat.zero_lt_succ n⟩) _ _ hmem
        rw [← hs] at hb
        have hleft := (ih l.size hk lo).2.2 l rfl
        have hright := (ih (n - l.size) (by omega) (lo + l.size + 1)).2.2 r hr.symm
        dsimp [candidate, k] at hb
        simp only [intervalCost, ht, ← Nat.add_assoc]
        omega

end RotationBST.OptimalLazyFinger
