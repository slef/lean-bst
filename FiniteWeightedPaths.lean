import Std

/-! Cycle erasure for integer-weighted paths. This is independent of the BST
model. When used on a product graph, restrict vertices to the reachable part. -/
namespace FiniteWeightedPaths

variable {α : Type} (edge : α → α → Int → Prop)

inductive Trace : α → α → List (α × Int) → Prop
  | nil : Trace s s []
  | cons : edge s t w → Trace t u rest → Trace s u ((s, w) :: rest)

def weight (xs : List (α × Int)) : Int := (xs.map Prod.snd).sum

def nodes (xs : List (α × Int)) (t : α) : List α := xs.map Prod.fst ++ [t]

theorem weight_append (xs ys : List (α × Int)) :
    weight (xs ++ ys) = weight xs + weight ys := by
  simp [weight, List.sum_append]

theorem Trace.append (h : Trace edge s t xs) (g : Trace edge t u ys) :
    Trace edge s u (xs ++ ys) := by
  induction h with
  | nil => exact g
  | cons he _ ih => exact .cons he (ih g)

theorem Trace.split_visit (h : Trace edge s t xs) (hx : v ∈ nodes xs t) :
    ∃ pre post, xs = pre ++ post ∧ Trace edge s v pre ∧ Trace edge v t post := by
  induction h with
  | @nil s =>
      have hv : v = s := by simpa [nodes] using hx
      subst v
      exact ⟨[], [], rfl, .nil, .nil⟩
  | @cons s u w t rest he ht ih =>
      have hm : v = s ∨ v ∈ nodes rest t := by simpa [nodes] using hx
      rcases hm with hv | hm
      · subst v
        exact ⟨[], (s,w) :: rest, rfl, .nil, .cons he ht⟩
      · obtain ⟨pre, post, hp, hpre, hpost⟩ := ih hm
        exact ⟨(s,w) :: pre, post, by simp [hp], .cons he hpre, hpost⟩

/-- Erasing nonpositive loops never decreases a path's weight. -/
theorem erase_cycles
    (noPositive : ∀ s xs, Trace edge s s xs → weight xs ≤ 0)
    (h : Trace edge s t xs) :
    ∃ ys, Trace edge s t ys ∧ (nodes ys t).Nodup ∧ weight xs ≤ weight ys := by
  induction h with
  | nil => exact ⟨[], .nil, by simp [nodes], by simp⟩
  | @cons s u w t rest he ht ih =>
      obtain ⟨ys, hy, hn, hw⟩ := ih
      by_cases hm : s ∈ nodes ys t
      · obtain ⟨pre, post, heq, hpre, hpost⟩ := Trace.split_visit edge hy hm
        have loop : Trace edge s s ((s,w) :: pre) := .cons he hpre
        have hl := noPositive s _ loop
        have hnp : (nodes post t).Nodup := by
          rw [heq] at hn
          simp only [nodes, List.map_append, List.append_assoc] at hn ⊢
          exact (List.nodup_append.mp hn).2.1
        refine ⟨post, hpost, hnp, ?_⟩
        rw [heq, weight_append] at hw
        simp only [weight, List.map_cons, List.sum_cons] at hl ⊢
        change weight rest ≤ weight pre + weight post at hw
        change w + weight pre ≤ 0 at hl
        change w + weight rest ≤ weight post
        omega
      · refine ⟨(s,w) :: ys, .cons he hy, ?_, ?_⟩
        · simpa [nodes] using List.nodup_cons.mpr ⟨hm, hn⟩
        · change w + weight rest ≤ w + weight ys
          omega

theorem Trace.weight_bound (M : Nat)
    (bound : ∀ s t w, edge s t w → w ≤ (M : Int))
    (h : Trace edge s t xs) : weight xs ≤ (xs.length : Int) * M := by
  induction h with
  | nil => simp [weight]
  | @cons s u w t rest he ht ih =>
      have hb := bound s u w he
      simp only [weight, List.map_cons, List.sum_cons]
      change w + weight rest ≤ _
      simp only [List.length_cons, Int.natCast_add, Int.natCast_one, Int.add_mul,
        Int.one_mul]
      omega

theorem Trace.nodes_in (states : List α)
    (closed : ∀ s t w, edge s t w → t ∈ states)
    (h : Trace edge s t xs) (hs : s ∈ states) : nodes xs t ⊆ states := by
  induction h with
  | nil => simpa [nodes] using hs
  | @cons s u w t rest he ht ih =>
      intro v hv
      have hm : v = s ∨ v ∈ nodes rest t := by simpa [nodes] using hv
      rcases hm with rfl | hm
      · exact hs
      · exact ih (closed s u w he) hm

/-- A finite reachable region with nonpositive loops has uniformly bounded
path weights. The enumeration need not be duplicate-free. -/
theorem finite_path_bound (states : List α)
    (closed : ∀ s t w, edge s t w → t ∈ states)
    (M : Nat) (bound : ∀ s t w, edge s t w → w ≤ (M : Int))
    (noPositive : ∀ s xs, Trace edge s s xs → weight xs ≤ 0)
    (h : Trace edge s t xs) (hs : s ∈ states) :
    weight xs ≤ (states.length : Int) * M := by
  obtain ⟨ys, hy, hn, hw⟩ := erase_cycles edge noPositive h
  have hl := hn.length_le_of_subset (Trace.nodes_in edge states closed hy hs)
  have hlen : ys.length ≤ states.length := by
    have hlen1 : ys.length + 1 ≤ states.length := by simpa [nodes] using hl
    omega
  have hb := Trace.weight_bound edge M bound hy
  have hc : (ys.length : Int) ≤ states.length := by omega
  have hm := Int.mul_le_mul_of_nonneg_right hc (show (0 : Int) ≤ M by omega)
  omega

/-- info: 'FiniteWeightedPaths.finite_path_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_path_bound
end FiniteWeightedPaths
