module

public import RotationBST.Splay.Online.Abstract

public import RotationBST.Pointer.Traces

@[expose] public section

namespace RotationBST.Splay
open Pointer

/-- Bottom-up splaying uses at most two pointer instructions per rotation.
A zig-zig needs an up/down pair in addition to its two rotations. -/
theorem splayAt_trace (l r : Tree) (cs : List Frame) :
    ∃ k, k ≤ 2 * cs.length ∧ Trace ⟨.node l r, cs⟩ ⟨splayAt l r cs, []⟩ k := by
  induction l, r, cs using splayAt.induct with
  | case1 l r => exact ⟨0, by simp, .refl⟩
  | case2 l r b => exact ⟨1, by simp, .step .rotateLeftChild .refl⟩
  | case3 l r a => exact ⟨1, by simp, .step .rotateRightChild .refl⟩
  | case4 l r b c cs ih =>
      obtain ⟨k, hk, ht⟩ := ih
      refine ⟨k + 4, ?_, .step .upLeft (.step .rotateLeftChild
        (.step .downLeft (.step .rotateLeftChild ht)))⟩
      simp only [List.length_cons]; omega
  | case5 l r a b cs ih =>
      obtain ⟨k, hk, ht⟩ := ih
      refine ⟨k + 4, ?_, .step .upRight (.step .rotateRightChild
        (.step .downRight (.step .rotateRightChild ht)))⟩
      simp only [List.length_cons]; omega
  | case6 l r a b cs ih =>
      obtain ⟨k, hk, ht⟩ := ih
      refine ⟨k + 2, ?_, .step .rotateRightChild (.step .rotateLeftChild ht)⟩
      simp only [List.length_cons]; omega
  | case7 l r b a cs ih =>
      obtain ⟨k, hk, ht⟩ := ih
      refine ⟨k + 2, ?_, .step .rotateLeftChild (.step .rotateRightChild ht)⟩
      simp only [List.length_cons]; omega

/-- Rank search is an actual pointer path, with cost equal to the number of ancestors. -/
theorem locate_trace (t : Tree) (x : Nat) (hx : x < t.size) :
    Trace ⟨t, []⟩ (locate t x) (locate t x).context.length := by
  induction t generalizing x with
  | nil => simp [Tree.size] at hx
  | node l r il ir =>
      by_cases hl : x < l.size
      · have ht := (il x hl).under [.left r]
        cases l with
        | nil => simp [Tree.size] at hl
        | node a b =>
            simpa only [locate, ite_eq_left hl, Config.under, List.length_append,
              List.length_singleton] using Trace.step Step.downLeft ht
      · by_cases he : x = l.size
        · simp only [locate, ite_eq_right hl, ite_eq_left he]
          exact .refl
        · have hr : x - l.size - 1 < r.size := by simp only [Tree.size] at hx; omega
          have ht := (ir (x - l.size - 1) hr).under [.right l]
          cases r with
          | nil => simp [Tree.size] at hr
          | node a b =>
              simpa only [locate, ite_eq_right hl, ite_eq_right he, Config.under,
                List.length_append, List.length_singleton] using Trace.step Step.downRight ht

/-- The implemented splay access is realizable in the conventional pointer model,
with the same final tree and at most `1 + 3 * rotations` total cost. -/
theorem run_pointer (t : Tree) (x : Nat) (hx : x < t.size) :
    ∃ k, k ≤ 1 + 3 * (run t x).2 ∧ Serves t (run t x).1 x k := by
  have hsearch := locate_trace t x hx
  have hkey := (locate_correct t x hx).2.1
  generalize hc : locate t x = c at hsearch hkey
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => simp [Config.key?] at hkey
  | node l r =>
      obtain ⟨k, hk, hsplay⟩ := splayAt_trace l r cs
      refine ⟨1 + cs.length + k, ?_, ?_⟩
      · simp only [run, hc]; omega
      · refine ⟨⟨.node l r, cs⟩, ⟨splayAt l r cs, []⟩, cs.length, k,
          hsearch, hkey, hsplay, ?_, rfl⟩
        simp only [Config.tree, plug, run, hc]

/-- The entire online splay run has a conventional pointer execution, preserving
all search boundaries and the final tree. -/
theorem runFrom_pointer (past : List Nat) (t : Tree) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < t.size) :
    ∃ k, k ≤ xs.length + 3 * (algorithm.runFrom past t xs).2 ∧
      Pointer.Execution t xs (algorithm.runFrom past t xs).1 k := by
  induction xs generalizing past t with
  | nil => exact ⟨0, by simp [Algorithm.runFrom], .nil⟩
  | cons x xs ih =>
      have hx := valid x (by simp)
      have hs := (run_correct t x hx).1.1.size_eq
      obtain ⟨k, hk, ht⟩ := run_pointer t x hx
      have hv : ∀ y ∈ xs, y < (run t x).1.size := by
        intro y hy
        rw [← hs]
        exact valid y (by simp [hy])
      obtain ⟨m, hm, hu⟩ := ih (past ++ [x]) (run t x).1 hv
      refine ⟨k + m, ?_, ?_⟩
      · change k + m ≤ xs.length + 1 + 3 * ((run t x).2 +
          (algorithm.runFrom (past ++ [x]) (run t x).1 xs).2)
        omega
      · exact Pointer.Execution.cons ht hu

end RotationBST.Splay
