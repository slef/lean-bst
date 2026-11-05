module

public import RotationBST.Models.Pointer.Basic
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Pointer

theorem offset_add_size_le_plug (cs : List Frame) (t : Tree) :
    offset cs + t.size ≤ (plug cs t).size := by
  induction cs generalizing t with
  | nil => simp [offset, plug]
  | cons c cs ih =>
    cases c with
    | left r =>
      have h := ih (.node t r)
      simp only [offset, plug, Tree.size] at *
      omega
    | right l =>
      have h := ih (.node l t)
      simp only [offset, plug, Tree.size] at *
      omega

theorem Config.key_lt_size (c : Config) (x : Nat) (hx : c.key? = some x) : x < c.tree.size := by
  rcases c with ⟨t, cs⟩
  cases t with
  | nil => simp [Config.key?] at hx
  | node l r =>
    have h := offset_add_size_le_plug cs (.node l r)
    have he : offset cs + l.size = x := Option.some.inj hx
    simp only [Tree.size] at h
    change x < (plug cs (.node l r)).size
    omega

theorem Step.size_eq {a b : Config} (h : Step a b) : a.tree.size = b.tree.size := by
  obtain ⟨_, _, hr⟩ := h.rotations
  exact hr.size_eq

theorem Step.keys_exist {a b : Config} (h : Step a b) :
    (∃ x, a.key? = some x) ∧ ∃ y, b.key? = some y := by
  cases h <;> simp [Config.key?]

end RotationBST.Pointer
