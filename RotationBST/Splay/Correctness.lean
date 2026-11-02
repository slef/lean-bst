module

public import RotationBST.Splay.Algorithm
public import RotationBST.Pointer.Basic

@[expose] public section

namespace RotationBST.Splay
open Pointer

theorem splayAt_correct (l r : Tree) (cs : List Frame) :
    Access (plug cs (.node l r)) (splayAt l r cs) (offset cs + l.size) cs.length := by
  induction l, r, cs using splayAt.induct with
  | case1 l r => exact ⟨.refl, by simp [splayAt, offset]⟩
  | case2 l r b => exact ⟨.step .right .refl, by simp [splayAt, offset]⟩
  | case3 l r a =>
      exact ⟨.step .left .refl, by simp [splayAt, offset, Tree.size, Nat.add_assoc]⟩
  | case4 l r b c cs ih =>
      refine ⟨.step (Rotate.plug .right cs) (.step (Rotate.plug .right cs) ih.1), ?_⟩
      exact ih.2
  | case5 l r a b cs ih =>
      refine ⟨.step (Rotate.plug .left cs) (.step (Rotate.plug .left cs) ih.1), ?_⟩
      simpa only [splayAt, offset, Tree.size, Nat.add_assoc] using ih.2
  | case6 l r a b cs ih =>
      refine ⟨.step (Rotate.plug (.inLeft .left) cs)
        (.step (Rotate.plug .right cs) ih.1), ?_⟩
      simpa only [splayAt, offset, Tree.size, Nat.add_assoc] using ih.2
  | case7 l r b a cs ih =>
      refine ⟨.step (Rotate.plug (.inRight .right) cs)
        (.step (Rotate.plug .left cs) ih.1), ?_⟩
      simpa only [splayAt, offset, Tree.size, Nat.add_assoc] using ih.2

theorem plug_append (cs ds : List Frame) (t : Tree) :
    plug (cs ++ ds) t = plug ds (plug cs t) := by
  induction cs generalizing t with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [List.cons_append, plug, ih]

theorem offset_append (cs ds : List Frame) : offset (cs ++ ds) = offset ds + offset cs := by
  induction cs with
  | nil => simp [offset]
  | cons c cs ih => cases c <;> simp [offset, ih, Nat.add_assoc]

/-- Search reconstructs the input, identifies the requested key, and uses fewer
than `n` ancestor links. The key condition rules out an empty focus. -/
theorem locate_correct (t : Tree) (x : Nat) (hx : x < t.size) :
    (locate t x).tree = t ∧ (locate t x).key? = some x ∧
      (locate t x).context.length < t.size := by
  induction t generalizing x with
  | nil => simp [Tree.size] at hx
  | node l r il ir =>
      by_cases hl : x < l.size
      · obtain ⟨ht, hk, hd⟩ := il x hl
        simp only [locate, ite_eq_left hl]
        refine ⟨?_, ?_, ?_⟩
        · simpa only [Config.tree, plug_append, plug] using congrArg (Tree.node · r) ht
        · cases he : (locate l x).focus with
          | nil => simp [Config.key?, he] at hk
          | node a b =>
              simpa only [Config.key?, he, offset_append, offset, Nat.zero_add] using hk
        · simp only [List.length_append, List.length_singleton, Tree.size]; omega
      · by_cases he : x = l.size
        · simp [locate, he, Config.tree, Config.key?, plug, offset, Tree.size]; omega
        · have hr : x - l.size - 1 < r.size := by simp only [Tree.size] at hx; omega
          obtain ⟨ht, hk, hd⟩ := ir (x - l.size - 1) hr
          simp only [locate, ite_eq_right hl, ite_eq_right he]
          refine ⟨?_, ?_, ?_⟩
          · simpa only [Config.tree, plug_append, plug] using congrArg (Tree.node l) ht
          · cases hf : (locate r (x - l.size - 1)).focus with
            | nil => simp [Config.key?, hf] at hk
            | node a b =>
                simp only [Config.key?, hf, Option.some.injEq] at hk ⊢
                simp only [offset_append, offset]
                omega
          · simp only [List.length_append, List.length_singleton, Tree.size]; omega

theorem run_correct (t : Tree) (x : Nat) (hx : x < t.size) :
    Access t (run t x).1 x (run t x).2 ∧ (run t x).2 < t.size := by
  obtain ⟨ht, hk, hd⟩ := locate_correct t x hx
  generalize hc : locate t x = c at ht hk hd ⊢
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => simp [Config.key?] at hk
  | node l r =>
      have ha := splayAt_correct l r cs
      have hk' : offset cs + l.size = x := Option.some.inj hk
      rw [hk'] at ha
      change plug cs (.node l r) = t at ht
      rw [ht] at ha
      simpa only [run, hc] using And.intro ha hd

end RotationBST.Splay
