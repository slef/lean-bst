import PeriodicLearning

/-! Least consistent selection from a countable family of finite candidate
lists, avoiding any numerical encoding of finite words. -/
namespace FiniteCoverLearning
variable {α : Type}

private theorem least_nat (p : Nat → Prop) (h : ∃ n, p n) :
    ∃ k, p k ∧ ∀ m, p m → k ≤ m := by
  obtain ⟨n,hn⟩ := h
  have aux : ∀ n, p n → ∃ k, p k ∧ ∀ m, p m → k ≤ m := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hp
      by_cases hs : ∃ m, m<n ∧ p m
      · obtain ⟨m,hm,hp⟩ := hs; exact ih m hm hp
      · refine ⟨n,hp,?_⟩
        intro m hm
        apply Classical.byContradiction
        intro hn
        exact hs ⟨m,by omega,hm⟩
  exact aux n hn

structure Pick (covers : Nat → List α) (P : α → Prop) where
  bucket : Nat
  index : Nat
  value : α
  at_index : (covers bucket)[index]? = some value
  consistent : P value
  bucket_min : ∀ b a, a ∈ covers b → P a → bucket ≤ b
  index_min : ∀ i a, (covers bucket)[i]? = some a → P a → index ≤ i

theorem pick_exists (covers : Nat → List α) (P : α → Prop)
    (h : ∃ b a, a ∈ covers b ∧ P a) : Nonempty (Pick covers P) := by
  obtain ⟨b,⟨a,ha,hpa⟩,hb⟩ := least_nat (fun b => ∃ a, a ∈ covers b ∧ P a) h
  obtain ⟨i,hi⟩ := List.getElem?_of_mem ha
  obtain ⟨j,⟨v,hv,hpv⟩,hj⟩ := least_nat (fun j => ∃ v, (covers b)[j]? = some v ∧ P v)
    ⟨i,a,hi,hpa⟩
  exact ⟨⟨b,j,v,hv,hpv,fun b a ha hp => hb b ⟨a,ha,hp⟩,
    fun i a ha hp => hj i ⟨a,ha,hp⟩⟩⟩

noncomputable def pick (covers : Nat → List α) (P : α → Prop)
    (h : ∃ b a, a ∈ covers b ∧ P a) : Pick covers P :=
  Classical.choice (pick_exists covers P h)

/-- First the least feasible bucket stabilizes; then the least consistent
index within that fixed finite list stabilizes. -/
theorem stabilizes (covers : Nat → List α) (compatible : Nat → α → Prop)
    (selected : ∀ i, Pick covers (compatible i))
    (shrinks : ∀ i j a, i ≤ j → compatible j a → compatible i a)
    (b : Nat) (truth : α) (hin : truth ∈ covers b)
    (htruth : ∀ i, compatible i truth) :
    ∃ cutoff, ∀ i, cutoff ≤ i → (selected i).value = (selected cutoff).value := by
  have hb : ∀ i, (selected i).bucket ≤ b :=
    fun i => (selected i).bucket_min b truth hin (htruth i)
  have hm : ∀ i j, i ≤ j → (selected i).bucket ≤ (selected j).bucket := by
    intro i j hij
    exact (selected i).bucket_min _ _
      (List.mem_iff_getElem?.mpr ⟨_,(selected j).at_index⟩)
      (shrinks i j _ hij (selected j).consistent)
  obtain ⟨N,hN⟩ := RotationBST.bounded_monotone_stabilizes
    (fun i => (selected i).bucket) b hb hm
  have heq : ∀ i, (selected (N+i)).bucket = (selected N).bucket :=
    fun i => hN (N+i) (by omega)
  have hi : ∀ i, (selected (N+i)).index ≤ (covers (selected N).bucket).length := by
    intro i
    have h := (selected (N+i)).at_index
    rw [heq i] at h
    obtain ⟨hlt,_⟩ := List.getElem?_eq_some_iff.mp h
    omega
  have hmono : ∀ i j, i ≤ j →
      (selected (N+i)).index ≤ (selected (N+j)).index := by
    intro i j hij
    apply (selected (N+i)).index_min _ (selected (N+j)).value
    · rw [heq i, ← heq j]; exact (selected (N+j)).at_index
    · exact shrinks (N+i) (N+j) _ (by omega) (selected (N+j)).consistent
  obtain ⟨M,hM⟩ := RotationBST.bounded_monotone_stabilizes
    (fun i => (selected (N+i)).index) _ hi hmono
  refine ⟨N+M,?_⟩
  intro i hi
  have hbi := hN i (by omega)
  have hbm := heq M
  have hidx : (selected i).index = (selected (N+M)).index := by
    have hh := hM (i-N) (by omega)
    have he : N+(i-N) = i := by omega
    change (selected (N+(i-N))).index = (selected (N+M)).index at hh
    rw [he] at hh
    exact hh
  have h1 := (selected i).at_index
  have h2 := (selected (N+M)).at_index
  rw [hbi,hidx] at h1
  rw [hbm] at h2
  exact Option.some.inj (h1.symm.trans h2)

/-- info: 'FiniteCoverLearning.stabilizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stabilizes
end FiniteCoverLearning
