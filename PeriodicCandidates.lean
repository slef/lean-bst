import FiniteCoverLearning
import InfinitePlan

namespace RotationBST
namespace PeriodicCandidates
open InfinitePlanning

abbrev Candidate := List Nat × List Nat

def atRank (xs : List Nat) (i : Nat) : Nat := xs[i]?.getD 0

/-- An empty period denotes the constant-zero tail. -/
def forecast (p : Candidate) (i : Nat) : Nat :=
  if i < p.1.length then atRank p.1 i else atRank p.2 ((i-p.1.length) % p.2.length)

def words (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | b+1 => [] :: (List.range n).flatMap (fun x => (words n b).map (List.cons x))

def covers (n b : Nat) : List Candidate :=
  (words n b).flatMap (fun pre => (words n b).map (fun per => (pre,per)))

def Valid (n : Nat) (p : Candidate) : Prop :=
  (∀ x ∈ p.1, x<n) ∧ (∀ x ∈ p.2, x<n)

theorem words_complete (xs : List Nat) (n b : Nat)
    (hv : ∀ x ∈ xs, x<n) (hl : xs.length ≤ b) : xs ∈ words n b := by
  induction b generalizing xs with
  | zero => have he : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst xs; simp [words]
  | succ b ih =>
    cases xs with
    | nil => simp [words]
    | cons x xs =>
      apply List.mem_cons.mpr
      right
      apply List.mem_flatMap.mpr
      refine ⟨x,List.mem_range.mpr (hv x (by simp)),?_⟩
      apply List.mem_map.mpr
      refine ⟨xs,ih xs (fun y hy => hv y (by simp [hy])) (by simpa using Nat.le_of_succ_le_succ hl),rfl⟩

theorem words_valid (xs : List Nat) (h : xs ∈ words n b) : ∀ x ∈ xs, x<n := by
  induction b generalizing xs with
  | zero => have he : xs = [] := by simpa [words] using h
            subst xs; simp
  | succ b ih =>
    rcases List.mem_cons.mp h with he | h
    · subst xs; simp
    · obtain ⟨x,hx,hmap⟩ := List.mem_flatMap.mp h
      obtain ⟨ys,hys,he⟩ := List.mem_map.mp hmap
      subst xs
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact List.mem_range.mp hx
      · exact ih ys hys y hy

theorem covers_complete (p : Candidate) (h : Valid n p) :
    p ∈ covers n (max p.1.length p.2.length) := by
  apply List.mem_flatMap.mpr
  refine ⟨p.1,words_complete _ _ _ h.1 (Nat.le_max_left _ _),?_⟩
  exact List.mem_map.mpr ⟨p.2,words_complete _ _ _ h.2 (Nat.le_max_right _ _),rfl⟩

theorem covers_valid (h : p ∈ covers n b) : Valid n p := by
  obtain ⟨pre,hpre,hmap⟩ := List.mem_flatMap.mp h
  obtain ⟨per,hper,he⟩ := List.mem_map.mp hmap
  subst p
  exact ⟨words_valid pre hpre,words_valid per hper⟩

theorem atRank_valid (xs : List Nat) (hn : 0<n) (hv : ∀ x ∈ xs, x<n) :
    atRank xs i < n := by
  cases he : xs[i]? with
  | none => simpa [atRank,he] using hn
  | some x =>
    have hx := hv x (List.mem_iff_getElem?.mpr ⟨i,he⟩)
    simpa [atRank,he] using hx

theorem forecast_valid (p : Candidate) (hn : 0<n) (hp : Valid n p) :
    ∀ i, forecast p i < n := by
  intro i
  unfold forecast
  split
  · exact atRank_valid _ hn hp.1
  · exact atRank_valid _ hn hp.2

def Compatible (history : List Nat) (p : Candidate) : Prop :=
  ∀ i, i < history.length → forecast p i = atRank history i

theorem finite_extension (history : List Nat) (hv : ∀ x ∈ history, x<n) :
    ∃ b p, p ∈ covers n b ∧ Compatible history p := by
  refine ⟨max history.length 0,(history,[]),covers_complete _ ⟨hv,by simp⟩,?_⟩
  intro i hi
  simp [forecast,hi]

noncomputable def selected (history : List Nat) (hv : ∀ x ∈ history, x<n) :
    FiniteCoverLearning.Pick (covers n) (Compatible history) :=
  FiniteCoverLearning.pick _ _ (finite_extension history hv)

theorem segment_length (word : Nat → Nat) (start len : Nat) :
    (segment word start len).length = len := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih => simp [segment,ih]

theorem segment_atRank (word : Nat → Nat) (start len i : Nat) (hi : i<len) :
    atRank (segment word start len) i = word (start+i) := by
  induction len generalizing start i with
  | zero => omega
  | succ len ih =>
    cases i with
    | zero => simp [segment,atRank]
    | succ i =>
      have hh := ih (start+1) i (by omega)
      simpa [segment,atRank,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem compatible_segment (word : Nat → Nat) (time : Nat) (p : Candidate) :
    Compatible (segment word 0 time) p ↔ ∀ i, i<time → forecast p i = word i := by
  unfold Compatible
  simp only [segment_length]
  constructor
  · intro h i hi
    have hh := h i hi
    simpa only [segment_atRank word 0 time i hi,Nat.zero_add] using hh
  · intro h i hi
    rw [segment_atRank word 0 time i hi,Nat.zero_add]
    exact h i hi

theorem segment_values (word : Nat → Nat) (valid : ∀ i, word i<n) (start len : Nat) :
    ∀ x ∈ segment word start len, x<n := by
  induction len generalizing start with
  | zero => simp [segment]
  | succ len ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact valid start
    · exact ih (start+1) x hx

theorem selected_stabilizes (word : Nat → Nat) (valid : ∀ i, word i<n)
    (truth : Candidate) (hv : Valid n truth) (heq : ∀ i, forecast truth i = word i) :
    ∃ cutoff, ∀ i, cutoff ≤ i →
      (selected (segment word 0 i) (segment_values word valid 0 i)).value =
      (selected (segment word 0 cutoff) (segment_values word valid 0 cutoff)).value := by
  let picks : ∀ i, FiniteCoverLearning.Pick (covers n) (Compatible (segment word 0 i)) :=
    fun i => selected _ (segment_values word valid 0 i)
  have hs := FiniteCoverLearning.stabilizes (covers n)
    (fun i p => Compatible (segment word 0 i) p) picks
    (by
      intro i j p hij hp
      apply (compatible_segment word i p).mpr
      intro k hk
      exact (compatible_segment word j p).mp hp k (by omega))
    (max truth.1.length truth.2.length) truth (covers_complete truth hv)
    (fun i => (compatible_segment word i truth).mpr (fun k _ => heq k))
  exact hs

theorem selected_eventually_correct (word : Nat → Nat) (valid : ∀ i, word i<n)
    (truth : Candidate) (hv : Valid n truth) (heq : ∀ i, forecast truth i = word i) :
    ∃ cutoff p, Valid n p ∧ (∀ k, forecast p k = word k) ∧ ∀ i, cutoff ≤ i →
      (selected (segment word 0 i) (segment_values word valid 0 i)).value = p := by
  obtain ⟨cutoff,hc⟩ := selected_stabilizes word valid truth hv heq
  let p := (selected (segment word 0 cutoff) (segment_values word valid 0 cutoff)).value
  refine ⟨cutoff,p,?_,?_,hc⟩
  · exact covers_valid (List.mem_iff_getElem?.mpr
      ⟨_,(selected (segment word 0 cutoff) (segment_values word valid 0 cutoff)).at_index⟩)
  · intro k
    let i := max cutoff (k+1)
    have hp := (selected (segment word 0 i) (segment_values word valid 0 i)).consistent
    have hh := (compatible_segment word i _).mp hp k (by dsimp [i]; omega)
    rw [hc i (Nat.le_max_left _ _)] at hh
    exact hh

/-- info: 'RotationBST.PeriodicCandidates.selected_eventually_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms selected_eventually_correct
end PeriodicCandidates
end RotationBST
