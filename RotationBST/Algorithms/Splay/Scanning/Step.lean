module

public import RotationBST.Algorithms.Splay.Scanning.Decomposition

@[expose] public section

namespace RotationBST.Splay.Scanning
open Marked

theorem successor_run (before : Tree) (l r : Marked) (cs rest : List Marked)
    (hl : l.tree ≠ .nil)
    (search : locate l.tree 0 = ⟨.node .nil r.tree, cs.map fun b => Pointer.Frame.left b.tree⟩) :
    Splay.run (.node before (spine (l :: rest))) (before.size + 1) =
      (.node (.node before .nil) (spine (consume r cs ++ rest)), cs.length + 2) := by
  have hn : ¬ before.size + 1 < before.size := by omega
  have he : ¬ before.size + 1 = before.size := by omega
  have hz : before.size + 1 - before.size - 1 = 0 := by omega
  have hp : 0 < l.tree.size := by cases hh : l.tree <;> simp_all [Tree.size]
  simp only [Splay.run, spine, locate, ite_eq_right hn, ite_eq_right he, hz,
    ite_eq_left hp, search]
  simp only [List.append_assoc, List.singleton_append, List.length_append,
    List.length_map, List.length_cons, List.length_nil, Nat.add_assoc]
  exact congrArg (fun t => (t, cs.length + 2)) (consume_splay r cs rest before)

/-- One successor access costs at most three rotations amortized against the
marked-tree potential (the displayed potential is doubled). -/
theorem step (before : Tree) (ls : List Marked) (valid : AllValid ls)
    (nonempty : spine ls ≠ .nil) :
    ∃ next k, AllValid next ∧
      Splay.run (.node before (spine ls)) (before.size + 1) =
        (.node (.node before .nil) (spine next), k) ∧
      2 * k + totalPotential next ≤ totalPotential ls + 6 ∧
      (spine next).size + 1 = (spine ls).size := by
  cases ls with
  | nil => exact False.elim (nonempty rfl)
  | cons l rest =>
      have hv : l.Valid := valid l (by simp)
      have hrest : AllValid rest := by intro t ht; exact valid t (by simp [ht])
      by_cases hl : l.tree = .nil
      · refine ⟨rest, 1, hrest, ?_, ?_, ?_⟩
        · have hn : ¬ before.size + 1 < before.size := by omega
          simp [Splay.run, spine, locate, hn, hl, Tree.size, splayAt]
        · change 2 * 1 + totalPotential rest ≤ l.potential + totalPotential rest + 6
          omega
        · simp [spine, hl, Tree.size, Nat.add_comm]
      · let e := l.expose
        have he : e.tree = l.tree := expose_tree l
        have hev : e.Valid := expose_valid l hv
        obtain ⟨r, cs, hp, hloc⟩ := decompose e (expose_ready l) (by rwa [he])
        have hc := consume_bound cs (.node (.hole .nil) r) r (by rwa [← hp])
          (plug_valid (by rwa [← hp] : (Marked.plug cs (.node (.hole .nil) r)).Valid)).2.1
          (by simp only [Marked.rank]; omega)
        have hexpose := expose_potential l
        have herank := (expose_rank l).1
        have hrun := successor_run before l r cs rest hl (by rwa [he] at hloc)
        refine ⟨consume r cs ++ rest, cs.length + 2, ?_, hrun, ?_, ?_⟩
        · intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact hc.1 t ht
          · exact hrest t ht
        · have hbound := hc.2
          rw [← hp] at hbound
          simp only [potential, Marked.rank, Tree.size] at hbound
          have hepot : e.potential ≤ l.potential := by dsimp [e]; omega
          simp only [totalPotential, List.map_append, List.sum_append,
            List.map_cons, List.sum_cons] at *
          omega
        · have hx : before.size + 1 < (Tree.node before (spine (l :: rest))).size := by
            simp only [spine, Tree.size]
            omega
          have hsize := (run_correct _ _ hx).1.1.size_eq
          rw [hrun] at hsize
          simp only [Tree.size] at hsize
          omega

end RotationBST.Splay.Scanning
