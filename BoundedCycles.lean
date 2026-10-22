import FiniteWeightedPaths

/-! Positive closed walks contain a positive simple cycle. Together with a
finite vertex cover this bounds the period needed for a cycle obstruction. -/
namespace FiniteWeightedPaths
variable {α : Type} (edge : α → α → Int → Prop)

theorem Trace.source_mem (h : Trace edge s t xs) : s ∈ nodes xs t := by
  cases h with
  | nil => simp [nodes]
  | cons => simp [nodes]

theorem erase_with_simple_loops
    (noPositive : ∀ s xs, Trace edge s s xs → (xs.map Prod.fst).Nodup → weight xs ≤ 0)
    (h : Trace edge s t xs) :
    ∃ ys, Trace edge s t ys ∧ (nodes ys t).Nodup ∧ weight xs ≤ weight ys := by
  induction h with
  | nil => exact ⟨[],.nil,by simp [nodes],by simp⟩
  | @cons s u w t rest he ht ih =>
    obtain ⟨ys,hy,hn,hw⟩ := ih
    by_cases hm : s ∈ nodes ys t
    · obtain ⟨pre,post,heq,hpre,hpost⟩ := Trace.split_visit edge hy hm
      have loop : Trace edge s s ((s,w)::pre) := .cons he hpre
      have hsplit : (pre.map Prod.fst).Nodup ∧ (nodes post t).Nodup ∧
          ∀ a ∈ pre.map Prod.fst, ∀ b ∈ nodes post t, a ≠ b := by
        rw [heq] at hn
        simp only [nodes,List.map_append,List.append_assoc] at hn
        exact List.nodup_append.mp hn
      have hsimple : (((s,w)::pre).map Prod.fst).Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨?_,hsplit.1⟩
        intro hin
        exact hsplit.2.2 s hin s (Trace.source_mem edge hpost) rfl
      have hl := noPositive s _ loop hsimple
      refine ⟨post,hpost,hsplit.2.1,?_⟩
      rw [heq,weight_append] at hw
      change w+weight pre ≤ 0 at hl
      change w+weight rest ≤ weight post
      omega
    · refine ⟨(s,w)::ys,.cons he hy,?_,?_⟩
      · simpa [nodes] using List.nodup_cons.mpr ⟨hm,hn⟩
      · change w+weight rest ≤ w+weight ys
        omega

theorem Trace.simple_closed_empty (h : Trace edge s s xs) (hn : (nodes xs s).Nodup) :
    xs = [] := by
  cases h with
  | nil => rfl
  | @cons s u w _ rest he ht =>
    have hnot : s ∉ nodes rest s := (List.nodup_cons.mp hn).1
    exact (hnot (by simp [nodes])).elim

/-- A positive closed trace implies a positive trace with no repeated departure
vertex. Its base vertex may differ from the original closed trace's base. -/
theorem positive_simple_cycle (h : Trace edge s s xs) (hw : 0 < weight xs) :
    ∃ v ys, Trace edge v v ys ∧ (ys.map Prod.fst).Nodup ∧ 0 < weight ys := by
  apply Classical.byContradiction
  intro hn
  have noPositive : ∀ v ys, Trace edge v v ys → (ys.map Prod.fst).Nodup → weight ys ≤ 0 := by
    intro v ys hy hs
    apply Classical.byContradiction
    intro hpos
    exact hn ⟨v,ys,hy,hs,by omega⟩
  obtain ⟨ys,hy,hs,hbound⟩ := erase_with_simple_loops edge noPositive h
  have he := Trace.simple_closed_empty edge hy hs
  rw [he] at hbound
  change weight xs ≤ 0 at hbound
  omega

/-- With a finite cover, the positive-cycle period is at most the cover size. -/
theorem bounded_positive_cycle (states : List α)
    (sources : ∀ s t w, edge s t w → s ∈ states)
    (closed : ∀ s t w, edge s t w → t ∈ states)
    (h : Trace edge s s xs) (hw : 0 < weight xs) :
    ∃ v ys, Trace edge v v ys ∧ 0 < weight ys ∧ ys.length ≤ states.length := by
  obtain ⟨v,ys,hy,hn,hpos⟩ := positive_simple_cycle edge h hw
  have hv : v ∈ states := by
    cases hy with
    | nil => simp [weight] at hpos
    | cons he _ => exact sources _ _ _ he
  have hsubset := Trace.nodes_in edge states closed hy hv
  have hmap : ys.map Prod.fst ⊆ states := by
    intro a ha
    exact hsubset (List.mem_append_left _ ha)
  have hlen := hn.length_le_of_subset hmap
  exact ⟨v,ys,hy,hpos,by simpa using hlen⟩

/-- Reachability alone admits loop erasure, regardless of edge weights. -/
theorem simple_reaching_path (h : Trace edge s t xs) :
    ∃ ys, Trace edge s t ys ∧ (nodes ys t).Nodup := by
  induction h with
  | nil => exact ⟨[],.nil,by simp [nodes]⟩
  | @cons s u w t rest he ht ih =>
    obtain ⟨ys,hy,hn⟩ := ih
    by_cases hm : s ∈ nodes ys t
    · obtain ⟨pre,post,heq,_,hpost⟩ := Trace.split_visit edge hy hm
      refine ⟨post,hpost,?_⟩
      rw [heq] at hn
      simp only [nodes,List.map_append,List.append_assoc] at hn ⊢
      exact (List.nodup_append.mp hn).2.1
    · exact ⟨(s,w)::ys,.cons he hy,by simpa [nodes] using List.nodup_cons.mpr ⟨hm,hn⟩⟩

theorem bounded_reaching_path (states : List α)
    (closed : ∀ s t w, edge s t w → t ∈ states)
    (h : Trace edge s t xs) (hs : s ∈ states) :
    ∃ ys, Trace edge s t ys ∧ ys.length < states.length := by
  obtain ⟨ys,hy,hn⟩ := simple_reaching_path edge h
  have hl := hn.length_le_of_subset (Trace.nodes_in edge states closed hy hs)
  have hl' : ys.length+1 ≤ states.length := by simpa [nodes] using hl
  exact ⟨ys,hy,by omega⟩

/-- In a reachable finite graph, a positive loop has a lasso witness: a prefix
shorter than the state cover and a positive period no longer than that cover. -/
theorem bounded_lasso (states : List α) (start : α) (hs : start ∈ states)
    (sources : ∀ s t w, edge s t w → s ∈ states)
    (closed : ∀ s t w, edge s t w → t ∈ states)
    (reachable : ∀ s t w, edge s t w → ∃ pre, Trace edge start s pre)
    (h : Trace edge s s xs) (hw : 0 < weight xs) :
    ∃ v pre cycle, Trace edge start v pre ∧ Trace edge v v cycle ∧
      0 < weight cycle ∧ pre.length < states.length ∧ cycle.length ≤ states.length := by
  obtain ⟨v,cycle,hcycle,hpos,hlen⟩ := bounded_positive_cycle edge states sources closed h hw
  have reach : ∃ pre, Trace edge start v pre := by
    cases hcycle with
    | nil => simp [weight] at hpos
    | cons he _ => exact reachable _ _ _ he
  obtain ⟨pre,hpre⟩ := reach
  obtain ⟨short,hshort,hbound⟩ := bounded_reaching_path edge states closed hpre hs
  exact ⟨v,short,cycle,hshort,hcycle,hpos,hbound,hlen⟩

/-- info: 'FiniteWeightedPaths.bounded_lasso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bounded_lasso
end FiniteWeightedPaths
