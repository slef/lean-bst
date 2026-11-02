module

public import RotationBST.Splay.LocalPotential
public import RotationBST.Splay.ContextPotential

@[expose] public section

namespace RotationBST.Splay
open Pointer

/-- The weighted Sleator--Tarjan access lemma for a focused node.
The cost is rotations; the additive one pays for the possible final zig. -/
theorem access_lemma_at (w : Nat → ℝ) (hw : ∀ i, 0 < w i)
    (l r : Tree) (cs : List Frame) (lo : Nat) :
    (cs.length : ℝ) + potential w (splayAt l r cs) lo - potential w (plug cs (.node l r)) lo ≤
      3 * (Real.logb 2 (mass w (plug cs (.node l r)) lo) -
        Real.logb 2 (mass w (.node l r) (lo + offset cs))) + 1 := by
  induction l, r, cs using splayAt.induct with
  | case1 l r => simp [splayAt, plug, offset]
  | case2 l r b => simpa only [splayAt, plug, offset, List.length_singleton,
      Nat.cast_one, Nat.add_zero] using zig_left w hw l r b lo
  | case3 l r a => simpa only [splayAt, plug, offset, List.length_singleton,
      Nat.cast_one, Nat.zero_add, Nat.add_assoc] using zig_right w hw a l r lo
  | case4 l r b c cs ih =>
      have hr : Rotations (.node (.node (.node l r) b) c)
          (.node l (.node r (.node b c))) 2 := .step .right (.step .right .refl)
      have h := compose_access w _ _ _ cs lo _ hr (zigzig_left w hw l r b c (lo + offset cs)) ih
      simpa only [splayAt, plug, offset, List.length_cons, Nat.cast_add, Nat.cast_one,
        Nat.add_assoc, add_assoc, one_add_one_eq_two, Nat.cast_ofNat] using h
  | case5 l r a b cs ih =>
      have hr : Rotations (.node b (.node a (.node l r)))
          (.node (.node (.node b a) l) r) 2 := .step .left (.step .left .refl)
      have h := compose_access w _ _ _ cs lo _ hr (zigzig_right w hw b a l r (lo + offset cs)) ih
      simpa only [splayAt, plug, offset, List.length_cons, Nat.cast_add, Nat.cast_one,
        Nat.add_assoc, add_assoc, one_add_one_eq_two, Nat.cast_ofNat] using h
  | case6 l r a b cs ih =>
      have hr : Rotations (.node (.node a (.node l r)) b)
          (.node (.node a l) (.node r b)) 2 := .step (.inLeft .left) (.step .right .refl)
      have h := compose_access w _ _ _ cs lo _ hr (zigzag_left w hw a l r b (lo + offset cs)) ih
      simpa only [splayAt, plug, offset, List.length_cons, Nat.cast_add, Nat.cast_one,
        Nat.add_assoc, add_assoc, one_add_one_eq_two, Nat.cast_ofNat] using h
  | case7 l r b a cs ih =>
      have hr : Rotations (.node a (.node (.node l r) b))
          (.node (.node a l) (.node r b)) 2 := .step (.inRight .right) (.step .left .refl)
      have h := compose_access w _ _ _ cs lo _ hr (zigzag_right w hw a l r b (lo + offset cs)) ih
      simpa only [splayAt, plug, offset, List.length_cons, Nat.cast_add, Nat.cast_one,
        Nat.add_assoc, add_assoc, one_add_one_eq_two, Nat.cast_ofNat] using h

/-- The accessed key's own weight is at most its initial subtree mass. -/
theorem weight_le_mass (w : Nat → ℝ) (hw : ∀ i, 0 < w i) (l r : Tree) (lo : Nat) :
    w (lo + l.size) ≤ mass w (.node l r) lo := by
  have := mass_nonneg w hw l lo
  have := mass_nonneg w hw r (lo + l.size + 1)
  simp only [mass]
  linarith

/-- The original access lemma, using the whole initial subtree of the accessed
node, before weakening its mass to that node's individual weight. -/
theorem access_lemma_subtree (w : Nat → ℝ) (hw : ∀ i, 0 < w i)
    (t : Tree) (x : Nat) (hx : x < t.size) :
    ((run t x).2 : ℝ) + potential w (run t x).1 0 - potential w t 0 ≤
      3 * (Real.logb 2 (mass w t 0) -
        Real.logb 2 (mass w (locate t x).focus (offset (locate t x).context))) + 1 := by
  obtain ⟨ht, hk, _⟩ := locate_correct t x hx
  generalize hc : locate t x = c at ht hk ⊢
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => simp [Config.key?] at hk
  | node l r =>
      have h := access_lemma_at w hw l r cs 0
      change plug cs (.node l r) = t at ht
      rw [ht] at h
      simpa only [run, hc, Nat.zero_add] using h

/-- A convenient, slightly weaker access lemma stated using the weight of the
requested rank itself rather than the mass of its initial subtree. -/
theorem access_lemma (w : Nat → ℝ) (hw : ∀ i, 0 < w i)
    (t : Tree) (x : Nat) (hx : x < t.size) :
    ((run t x).2 : ℝ) + potential w (run t x).1 0 - potential w t 0 ≤
      3 * (Real.logb 2 (mass w t 0) - Real.logb 2 (w x)) + 1 := by
  obtain ⟨ht, hk, _⟩ := locate_correct t x hx
  generalize hc : locate t x = c at ht hk
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => simp [Config.key?] at hk
  | node l r =>
      have h := access_lemma_at w hw l r cs 0
      have hk' : offset cs + l.size = x := Option.some.inj hk
      have hweight := weight_le_mass w hw l r (offset cs)
      rw [hk'] at hweight
      have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (hw x) hweight
      change plug cs (.node l r) = t at ht
      rw [ht] at h
      simp only [Nat.zero_add] at h
      simp only [run, hc]
      linarith

end RotationBST.Splay
