module

public import RotationBST.Arboral.Offline.Abstract
public import RotationBST.Arboral.Online.Proofs

@[expose] public section
namespace RotationBST.Arboral

theorem mem_keysAt (P : Finset Point) (time x : Nat) :
    x ∈ keysAt P time ↔ (x, time) ∈ P := by
  constructor
  · intro h
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp h
    obtain ⟨hp, hpt⟩ := Finset.mem_filter.mp hp
    have heq : p = (x, time) := Prod.ext hpx hpt
    simpa only [heq] using hp
  · intro h
    exact Finset.mem_image.mpr ⟨(x, time), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩

theorem prefix_succ (P : Finset Point) (time : Nat) :
    pastPoints P (time + 1) = pastPoints P time ∪ row time (keysAt P time) := by
  ext p
  simp only [pastPoints, Finset.mem_filter, Finset.mem_union, mem_row, mem_keysAt]
  constructor
  · rintro ⟨hp, ht⟩
    by_cases h : p.2 < time
    · exact Or.inl ⟨hp, h⟩
    · have he : p.2 = time := by omega
      exact Or.inr ⟨by simpa only [← he, Prod.eta] using hp, he⟩
  · rintro (⟨hp, ht⟩ | ⟨hp, ht⟩)
    · exact ⟨hp, by omega⟩
    · exact ⟨by simpa only [← ht, Prod.eta] using hp, by omega⟩

theorem offline_completion {n time request : Nat} {P : Finset Point}
    (bounded : ∀ p ∈ P, p.1 < n) (sat : ASS P) (req : (request, time) ∈ P) :
    Completion n time request (pastPoints P time) (keysAt P time) := by
  refine ⟨(mem_keysAt P time request).mpr req, ?_, ?_⟩
  · intro x hx
    exact Finset.mem_range.mpr (bounded (x, time) ((mem_keysAt P time x).mp hx))
  · rw [← prefix_succ]
    exact ass_prefix sat (time + 1)

theorem prefix_cost (P : Finset Point) (time : Nat) :
    (pastPoints P time).card = scheduleCost P time := by
  induction time with
  | zero => simp [pastPoints, scheduleCost]
  | succ time ih =>
    rw [prefix_succ, Finset.card_union_of_disjoint]
    · rw [ih]
      congr 1
      exact Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
    · rw [Finset.disjoint_left]
      intro p hp hr
      have ht := (Finset.mem_filter.mp hp).2
      have he := ((mem_row p time _).mp hr).2
      omega

theorem bounded_schedule_cost {n m : Nat} {P : Finset Point} (h : History n m P) :
    scheduleCost P m = P.card := by
  rw [← prefix_cost]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro p hp
  exact (h p hp).2

theorem offline_of_online {n : Nat} (A : OnlineAlgorithm n) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < n) :
    ∃ E : Offline n xs, E.points = fill A.step 0 ∅ xs ∧
      E.points.card = rowCost A.step 0 ∅ xs := by
  have hist : History n 0 ∅ := by simp [History]
  obtain ⟨sat, bound, cost⟩ := fill_spec A 0 ∅ xs hist ass_empty valid
  exact ⟨⟨⟨fill A.step 0 ∅ xs, fill_contains A 0 ∅ xs hist ass_empty valid, sat⟩,
    by simpa using bound⟩, rfl, by simpa using cost⟩

end RotationBST.Arboral
