module

public import RotationBST.Structures.SplitTree.Multiway.Edges.Balance

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway

theorem repairFirst_cost (t : Multiway) : (t.repairFirst).2 ≤ 5 := by
  cases t with
  | nil => decide
  | two a b => exact Nat.le_trans (prepareLeft_cost _) (by decide)
  | three a b c => cases a <;> cases b <;> simp [repairFirst, prepareLeft]
  | four a b c d => cases a <;> cases b <;> simp [repairFirst, prepareLeft]

theorem repairLast_cost (t : Multiway) : (t.repairLast).2 ≤ 4 := by
  cases t with
  | nil => decide
  | two a b => exact prepareRight_cost _
  | three a b c => cases b <;> cases c <;> simp [repairLast, prepareRight]
  | four a b c d => cases c <;> cases d <;> simp [repairLast, prepareRight]

theorem repairFirst_nodes (t : Multiway) : (t.repairFirst).1.nodes ≤ t.nodes := by
  cases t with
  | nil => exact Nat.le_refl _
  | two a b => exact prepareLeft_nodes _
  | three a b c => cases a <;> cases b <;> simp only [repairFirst, prepareLeft, nodes] <;> omega
  | four a b c d => cases a <;> cases b <;> simp only [repairFirst, prepareLeft, nodes] <;> omega

theorem repairLast_nodes (t : Multiway) : (t.repairLast).1.nodes ≤ t.nodes := by
  cases t with
  | nil => exact Nat.le_refl _
  | two a b => exact prepareRight_nodes _
  | three a b c => cases b <;> cases c <;> simp only [repairLast, prepareRight, nodes] <;> omega
  | four a b c d => cases c <;> cases d <;> simp only [repairLast, prepareRight, nodes] <;> omega

/-- Unlike root contraction, merging inside a larger parent consumes one node. -/
theorem merge_first_three_nodes (a b c d e : Multiway) :
    (.two (.four a b c d) e : Multiway).nodes + 1 =
      (.three (.two a b) (.two c d) e : Multiway).nodes := by
  simp only [nodes]
  omega

theorem merge_first_four_nodes (a b c d e f : Multiway) :
    (.three (.four a b c d) e f : Multiway).nodes + 1 =
      (.four (.two a b) (.two c d) e f : Multiway).nodes := by
  simp only [nodes]
  omega

theorem merge_last_three_nodes (a b c d e : Multiway) :
    (.two a (.four b c d e) : Multiway).nodes + 1 =
      (.three a (.two b c) (.two d e) : Multiway).nodes := by
  simp only [nodes]
  omega

theorem merge_last_four_nodes (a b c d e f : Multiway) :
    (.three a b (.four c d e f) : Multiway).nodes + 1 =
      (.four a b (.two c d) (.two e f) : Multiway).nodes := by
  simp only [nodes]
  omega

end RotationBST.Arboral.Split.Multiway
