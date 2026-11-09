module

public import RotationBST.Classical.Static.Optimal.Quadrangle
import Mathlib.Tactic

@[expose] public section

/-! Knuth's algorithm computes the recurrence, and its root ranges telescope
to `O(n²)` examined roots. -/
namespace RotationBST.Classical.Static.Optimal

variable {W : Nat → Nat → Nat}

/-! ### The scan over a root range -/

/-- The fold of `scan`, for an arbitrary candidate function. -/
theorem scan_fold_spec (f : Nat → Nat) (lo : Nat) (k : Nat) :
    let res := (List.range' (lo + 1) k).foldl
      (fun best r => if f r ≤ best.1 then (f r, r) else best) (f lo, lo)
    lo ≤ res.2 ∧ res.2 ≤ lo + k ∧ f res.2 = res.1 ∧
      (∀ r, lo ≤ r → r ≤ lo + k → res.1 ≤ f r) ∧
      (∀ r, lo ≤ r → r ≤ lo + k → f r = res.1 → r ≤ res.2) := by
  induction k with
  | zero =>
    simp only [List.range'_zero, List.foldl_nil, Nat.add_zero]
    refine ⟨le_rfl, le_rfl, trivial, fun r h1 h2 => ?_, fun r h1 h2 _ => h2⟩
    rw [show r = lo by omega]
  | succ k ih =>
    simp only at ih ⊢
    rw [List.range'_concat, List.foldl_append]
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    set res := (List.range' (lo + 1) k).foldl
      (fun best r => if f r ≤ best.1 then (f r, r) else best) (f lo, lo)
    simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul]
    rw [show lo + 1 + k = lo + (k + 1) by omega]
    split
    · rename_i hle
      refine ⟨by omega, le_rfl, rfl, fun r hr1 hr2 => ?_, fun r _ hr2 _ => hr2⟩
      rcases Nat.lt_or_ge r (lo + (k + 1)) with hlt | hge
      · exact hle.trans (h4 r hr1 (by omega))
      · rw [show r = lo + (k + 1) by omega]
    · rename_i hgt
      refine ⟨h1, by omega, h3, fun r hr1 hr2 => ?_, fun r hr1 hr2 hr => ?_⟩
      · rcases Nat.lt_or_ge r (lo + (k + 1)) with hlt | hge
        · exact h4 r hr1 (by omega)
        · rw [show r = lo + (k + 1) by omega]; omega
      · rcases Nat.lt_or_ge r (lo + (k + 1)) with hlt | hge
        · exact h5 r hr1 (by omega) hr
        · rw [show r = lo + (k + 1) by omega] at hr; omega

theorem scan_spec (C : Nat → Nat → Nat) (i j lo hi : Nat) (h : lo ≤ hi) :
    let res := scan W C i j lo hi
    let f := fun r => W i j + C i r + C (r + 1) j
    lo ≤ res.2 ∧ res.2 ≤ hi ∧ f res.2 = res.1 ∧
      (∀ r, lo ≤ r → r ≤ hi → res.1 ≤ f r) ∧
      (∀ r, lo ≤ r → r ≤ hi → f r = res.1 → r ≤ res.2) := by
  have := scan_fold_spec (fun r => W i j + C i r + C (r + 1) j) lo (hi - lo)
  rw [show lo + (hi - lo) = hi by omega] at this
  exact this

/-! ### Correctness of the tables -/

/-- After `len` rounds, the tables hold the optimal costs and largest optimal
roots of every interval of `[0, n)` of length at most `len`. -/
def TablesCorrect (W : Nat → Nat → Nat) (n len : Nat)
    (t : (Nat → Nat → Nat) × (Nat → Nat → Nat) × Nat) : Prop :=
  ∀ i j, i ≤ j → j - i ≤ len → j ≤ n → t.1 i j = cost W i j ∧ (i < j → t.2.1 i j = root W i j)

theorem knuthEntry_correct (hQ : Quadrangle W) (hM : Monotone W) {n len : Nat}
    (C K : Nat → Nat → Nat)
    (hC : ∀ i j, i ≤ j → j - i ≤ len → j ≤ n → C i j = cost W i j)
    (hK : ∀ i j, i < j → j - i ≤ len → j ≤ n → K i j = root W i j)
    (i : Nat) (hi : i + len + 1 ≤ n) :
    (knuthEntry W C K i (i + len + 1)).1 = cost W i (i + len + 1) ∧
      (knuthEntry W C K i (i + len + 1)).2.1 = root W i (i + len + 1) ∧
      (knuthEntry W C K i (i + len + 1)).2.2 =
        if len = 0 then 1 else root W (i + 1) (i + len + 1) + 1 - root W i (i + len) := by
  set j := i + len + 1
  obtain ⟨hr1, hr2, hr3, hrmax⟩ := root_spec W (show i < j by omega)
  by_cases h0 : len = 0
  · subst h0
    have hroot : root W i j = i := by omega
    have hc : cost W i j = W i j := by
      rw [← hr3, hroot, candidate, cost_self, show i + 1 = j by omega, cost_self]; rfl
    simp [knuthEntry, j, hc, hroot]
  · have hne : ¬ j = i + 1 := by omega
    have hlo : K i (j - 1) = root W i (j - 1) := hK i (j - 1) (by omega) (by omega) (by omega)
    have hhi : K (i + 1) j = root W (i + 1) j := hK (i + 1) j (by omega) (by omega) (by omega)
    have k1 : root W i (j - 1) ≤ root W i j := by
      have := root_le_root_right hQ hM (i := i) (j := j - 1) (by omega)
      rwa [show j - 1 + 1 = j by omega] at this
    have k2 : root W i j ≤ root W (i + 1) j := root_le_root_left hQ hM (by omega)
    obtain ⟨hl1, _, _, _⟩ := root_spec W (show i < j - 1 by omega)
    obtain ⟨_, hh2, _, _⟩ := root_spec W (show i + 1 < j by omega)
    set lo := root W i (j - 1)
    set hi := root W (i + 1) j
    obtain ⟨s1, s2, s3, s4, s5⟩ := scan_spec (W := W) C i j lo hi (k1.trans k2)
    simp only at s3 s4 s5
    -- On the scanned range, the table candidates are the true candidates.
    have hf : ∀ r, lo ≤ r → r ≤ hi → W i j + C i r + C (r + 1) j = candidate W i j r := by
      intro r h1 h2
      rw [hC i r (by omega) (by omega) (by omega), hC (r + 1) j (by omega) (by omega) (by omega)]
      rfl
    set res := scan W C i j lo hi
    have hv : res.1 = cost W i j := by
      apply le_antisymm
      · have := s4 (root W i j) k1 k2; rw [hf _ k1 k2, hr3] at this; exact this
      · have := s3; rw [hf _ s1 s2] at this; rw [← this]
        exact cost_le_candidate W (by omega) (by omega)
    have ha : res.2 = root W i j := by
      apply le_antisymm
      · have := s3; rw [hf _ s1 s2, hv] at this
        exact hrmax _ (by omega) (by omega) this
      · exact s5 _ k1 k2 (by rw [hf _ k1 k2, hr3, hv])
    simp only [knuthEntry, hne, ↓reduceIte, hlo, hhi, h0]
    refine ⟨hv, ha, ?_⟩
    have hlo' : lo = root W i (i + len) := by simp only [lo, j, Nat.add_sub_cancel]
    rw [hlo']

theorem knuthTables_succ (W : Nat → Nat → Nat) (n len : Nat) :
    knuthTables W n (len + 1) =
      (fun i j => if j = i + len + 1 then (knuthEntry W (knuthTables W n len).1
          (knuthTables W n len).2.1 i (i + len + 1)).1 else (knuthTables W n len).1 i j,
       fun i j => if j = i + len + 1 then (knuthEntry W (knuthTables W n len).1
          (knuthTables W n len).2.1 i (i + len + 1)).2.1 else (knuthTables W n len).2.1 i j,
       (knuthTables W n len).2.2 + ((List.range (n - len)).map fun i => (knuthEntry W
          (knuthTables W n len).1 (knuthTables W n len).2.1 i (i + len + 1)).2.2).sum) := rfl

theorem knuthTables_correct (hQ : Quadrangle W) (hM : Monotone W) (n : Nat) :
    ∀ len, TablesCorrect W n len (knuthTables W n len) := by
  intro len
  induction len with
  | zero =>
    intro i j h1 h2 _
    have : j = i := by omega
    subst this
    exact ⟨by simp [knuthTables, cost_self], fun h => absurd h (lt_irrefl _)⟩
  | succ len ih =>
    intro i j h1 h2 h3
    rw [knuthTables_succ]
    simp only
    by_cases hj : j = i + len + 1
    · subst hj
      have e := knuthEntry_correct hQ hM (knuthTables W n len).1 (knuthTables W n len).2.1
        (fun a b ha hb hc => (ih a b ha hb hc).1) (fun a b ha hb hc => (ih a b ha.le hb hc).2 ha) i h3
      simp only [↓reduceIte]
      exact ⟨e.1, fun _ => e.2.1⟩
    · simp only [hj, ↓reduceIte]
      exact ih i j h1 (by omega) h3

/-! ### The step count -/

theorem telescope (a : Nat → Nat) (m : Nat) (mono : ∀ i < m, a i ≤ a (i + 1)) :
    ((List.range m).map fun i => a (i + 1) + 1 - a i).sum + a 0 = a m + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    have := ih (fun i hi => mono i (by omega))
    have hm := mono m (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem knuthTables_steps (hQ : Quadrangle W) (hM : Monotone W) (n : Nat) :
    ∀ len, len ≤ n → (knuthTables W n len).2.2 ≤ 2 * n * len := by
  intro len
  induction len with
  | zero => intro _; simp [knuthTables]
  | succ len ih =>
    intro hlen
    rw [knuthTables_succ]
    simp only
    have hprev := ih (by omega)
    have hc := knuthTables_correct hQ hM n len
    have hentry : ∀ i ∈ List.range (n - len),
        (knuthEntry W (knuthTables W n len).1 (knuthTables W n len).2.1 i (i + len + 1)).2.2 =
          if len = 0 then 1 else root W (i + 1) (i + len + 1) + 1 - root W i (i + len) := by
      intro i hi
      have hi' := List.mem_range.mp hi
      exact (knuthEntry_correct hQ hM (knuthTables W n len).1 (knuthTables W n len).2.1
        (fun a b ha hb hc' => (hc a b ha hb hc').1)
        (fun a b ha hb hc' => (hc a b ha.le hb hc').2 ha) i (by omega)).2.2
    rw [List.map_congr_left hentry]
    by_cases h0 : len = 0
    · subst h0
      simp only [↓reduceIte, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul,
        Nat.mul_one, Nat.sub_zero] at hprev ⊢
      omega
    · simp only [h0, ↓reduceIte]
      -- The roots `a i = R(i, i + len)` increase with `i` and stay below `n`.
      have hmono : ∀ i < n - len, root W i (i + len) ≤ root W (i + 1) (i + 1 + len) := by
        intro i hi
        have k1 := root_le_root_right hQ hM (i := i) (j := i + len) (by omega)
        have k2 := root_le_root_left hQ hM (i := i) (j := i + len + 1) (by omega)
        rw [show i + 1 + len = i + len + 1 by omega]
        exact k1.trans k2
      have ht := telescope (fun i => root W i (i + len)) (n - len) hmono
      have hlast := (root_spec W (show n - len < n - len + len by omega)).2.1
      have hsum : ((List.range (n - len)).map fun i =>
          root W (i + 1) (i + len + 1) + 1 - root W i (i + len)).sum ≤ 2 * n := by
        have e : ∀ i, root W (i + 1) (i + len + 1) = root W (i + 1) (i + 1 + len) := by
          intro i; rw [show i + len + 1 = i + 1 + len by omega]
        simp only [e]
        omega
      nlinarith

theorem knuth_cost (hQ : Quadrangle W) (hM : Monotone W) (n : Nat) :
    (knuth W n).1 = cost W 0 n :=
  ((knuthTables_correct hQ hM n n) 0 n (Nat.zero_le _) (by omega) le_rfl).1

theorem knuth_steps (hQ : Quadrangle W) (hM : Monotone W) (n : Nat) :
    (knuth W n).2 ≤ 2 * n ^ 2 :=
  (knuthTables_steps hQ hM n n le_rfl).trans (by rw [Nat.pow_two, Nat.mul_assoc])

end RotationBST.Classical.Static.Optimal
