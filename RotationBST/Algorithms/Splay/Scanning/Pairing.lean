module

public import RotationBST.Algorithms.Splay.Scanning.Exposure

@[expose] public section

namespace RotationBST.Splay.Scanning.Marked

def plug : List Marked → Marked → Marked
  | [], t => t
  | b :: bs, t => plug bs (.node t b)

/-- Pair consecutive red ancestors from the bottom. The last one or two roots
become black spine nodes, represented by their left subtrees. -/
def consume (t : Marked) : List Marked → List Marked
  | [] => [t]
  | [b] => [t, b]
  | b :: c :: cs => consume (.node t (.node b c)) cs

def totalPotential (ts : List Marked) : Nat := (ts.map potential).sum

def AllValid (ts : List Marked) : Prop := ∀ t ∈ ts, t.Valid

theorem plug_valid {cs : List Marked} {t : Marked} (h : (plug cs t).Valid) : t.Valid := by
  induction cs generalizing t with
  | nil => exact h
  | cons b cs ih => exact (ih h).1

theorem consume_bound (cs : List Marked) (old acc : Marked)
    (valid : (plug cs old).Valid) (ha : acc.Valid) (hr : acc.rank ≤ old.rank + 1) :
    AllValid (consume acc cs) ∧
      2 * cs.length + totalPotential (consume acc cs) + old.potential ≤
        (plug cs old).potential + acc.potential + 2 := by
  match cs with
  | [] =>
      exact ⟨by simpa [AllValid, consume] using ha, by simp [consume, plug, totalPotential]; omega⟩
  | [b] =>
      have hv : (.node old b : Marked).Valid := valid
      refine ⟨?_, ?_⟩
      · intro t ht
        simp only [consume, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact ha
        · exact hv.2.1
      · simp only [consume, plug, totalPotential, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, potential]
        omega
  | b :: c :: cs =>
      have hv : (.node (.node old b) c : Marked).Valid := plug_valid valid
      have hab : (.node acc (.node b c) : Marked).Valid := by
        refine ⟨ha, ⟨hv.1.2.1, hv.2.1, ?_⟩, ?_⟩
        · have hh := hv.2.2; simp only [rank] at hh; omega
        · have h₁ := hv.1.2.2
          have h₂ := hv.2.2
          simp only [rank] at *
          omega
      have hc := pair_credit old.rank b.rank c.rank acc.rank hv.1.2.2
        (by have hh := hv.2.2; simp only [rank] at hh; omega) hr
      obtain ⟨hi, hb⟩ := consume_bound cs (.node (.node old b) c) (.node acc (.node b c))
        valid hab (by simp [rank])
      refine ⟨hi, ?_⟩
      simp only [consume, List.length_cons, plug]
      simp only [potential, rank] at hb
      rw [show c.rank + 1 + 1 = c.rank + 2 by omega] at hb
      omega
termination_by cs.length

theorem plug_tree (cs : List Marked) (t : Marked) :
    (plug cs t).tree = Pointer.plug (cs.map fun b => Pointer.Frame.left b.tree) t.tree := by
  induction cs generalizing t with
  | nil => rfl
  | cons b cs ih => exact ih (.node t b)

end RotationBST.Splay.Scanning.Marked
