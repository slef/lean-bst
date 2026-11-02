module

public import RotationBST.Splay.Scanning.Bound
public import RotationBST.Splay.Pointer

@[expose] public section

namespace RotationBST.Splay.Scanning

theorem total_bound (t : Tree) : algorithm.totalCost t (List.range t.size) ≤ 14 * t.size := by
  have h := rotation_bound t
  simp only [Algorithm.totalCost, List.length_range]
  omega

theorem pointer_bound (t : Tree) :
    ∃ k, k ≤ 40 * t.size ∧
      Pointer.Execution t (List.range t.size) (algorithm.runFrom [] t (List.range t.size)).1 k := by
  obtain ⟨k, hk, he⟩ := runFrom_pointer [] t (List.range t.size)
    (by intro x hx; exact List.mem_range.mp hx)
  have hr := rotation_bound t
  simp only [List.length_range] at hk
  change algorithm.cost t (List.range t.size) ≤ 13 * t.size at hr
  exact ⟨k, by unfold Algorithm.cost at hr; omega, he⟩

end RotationBST.Splay.Scanning
