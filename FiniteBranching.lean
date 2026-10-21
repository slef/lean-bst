import Std

/-! Elementary finite-branching compactness, with no Mathlib dependency. -/
namespace FiniteBranching

variable {α : Type}

/-- One member of a finite cover supports arbitrarily long extensions.
Downward closure upgrades unbounded support to support at every length. -/
theorem finite_cover (choices : List α) (P : α → Nat → Prop)
    (down : ∀ a m n, m ≤ n → P a n → P a m)
    (cover : ∀ n, ∃ a, a ∈ choices ∧ P a n) :
    ∃ a, a ∈ choices ∧ ∀ n, P a n := by
  induction choices with
  | nil => obtain ⟨a,ha,_⟩ := cover 0; simp at ha
  | cons a rest ih =>
      by_cases ha : ∀ n, P a n
      · exact ⟨a, by simp, ha⟩
      · have fail : ∃ n, ¬ P a n := Classical.not_forall.mp ha
        obtain ⟨n,hn⟩ := fail
        have tailCover : ∀ m, ∃ b, b ∈ rest ∧ P b m := by
          intro m
          obtain ⟨b,hb,hp⟩ := cover (max n m)
          rcases List.mem_cons.mp hb with rfl | hb
          · exact (hn (down b n (max n m) (Nat.le_max_left _ _) hp)).elim
          · exact ⟨b,hb,down b m (max n m) (Nat.le_max_right _ _) hp⟩
        obtain ⟨b,hb,hp⟩ := ih tailCover
        exact ⟨b, by simp [hb], hp⟩

variable (children : α → List α)

inductive Extension : α → Nat → Prop
  | zero : Extension s 0
  | succ : t ∈ children s → Extension t n → Extension s (n+1)

theorem Extension.down (h : Extension children s n) (hm : m ≤ n) :
    Extension children s m := by
  induction h generalizing m with
  | zero =>
      have he : m = 0 := by omega
      subst m
      exact .zero
  | succ he ht ih =>
      cases m with
      | zero => exact .zero
      | succ m => exact .succ he (ih (by omega))

def Unbounded (s : α) : Prop := ∀ n, Extension children s n

theorem unbounded_child (s : α) (h : Unbounded children s) :
    ∃ t, t ∈ children s ∧ Unbounded children t := by
  apply finite_cover (children s) (fun t n => Extension children t n)
  · intro t m n hmn he
    exact he.down children hmn
  · intro n
    cases h (n+1) with
    | succ ht he => exact ⟨_,ht,he⟩

noncomputable def next (s : {s : α // Unbounded children s}) :
    {t : α // Unbounded children t} :=
  ⟨Classical.choose (unbounded_child children s.1 s.2),
    (Classical.choose_spec (unbounded_child children s.1 s.2)).2⟩

theorem next_mem (s : {s : α // Unbounded children s}) :
    (next children s).1 ∈ children s.1 :=
  (Classical.choose_spec (unbounded_child children s.1 s.2)).1

/-- An explicit choice-based infinite branch through any finitely branching
node admitting extensions of every finite length. -/
theorem infinite_branch (s : α) (h : Unbounded children s) :
    ∃ path : Nat → α, path 0 = s ∧ ∀ n, path (n+1) ∈ children (path n) := by
  let walk : Nat → {s : α // Unbounded children s} :=
    fun n => Nat.rec ⟨s,h⟩ (fun _ t => next children t) n
  refine ⟨fun n => (walk n).1, rfl, ?_⟩
  intro n
  exact next_mem children (walk n)

/-- info: 'FiniteBranching.infinite_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infinite_branch
end FiniteBranching
