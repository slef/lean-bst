module

public import RotationBST.Structures.SplitTree.Multiway.Extract.Ready

@[expose] public section
namespace RotationBST.SplitTree.Multiway

private theorem descendFirst_balance (recur : Multiway → Multiway × Nat) {h : Nat} {t : Multiway}
    (valid : Balanced h t) (ready : firstChild t = .nil ∨ Wide (firstChild t))
    (recursive : ∀ child k, child.nodes < t.nodes → Balanced k child → Wide child → Balanced k (recur child).1) :
    (Balanced h (descendFirst recur t).1 ∨ ∃ k, h = k + 1 ∧ Balanced k (descendFirst recur t).1) ∧
      (Wide t ∨ firstChild t ≠ .nil → Balanced h (descendFirst recur t).1) := by
  cases valid with
  | nil => exact ⟨Or.inl .nil, fun _ => .nil⟩
  | @two k l r ha hb =>
    by_cases empty : l = .nil
    · subst l
      cases ha
      cases hb
      refine ⟨Or.inr ⟨0, rfl, .nil⟩, ?_⟩
      simp [Wide, firstChild]
    · have wide : Wide l := ready.resolve_left empty
      have child := recursive l k (by simp only [nodes]; omega) ha wide
      have result : Balanced (k + 1) (descendFirst recur (.two l r)).1 := by
        simpa only [descendFirst, ite_eq_right empty] using Balanced.two child hb
      exact ⟨Or.inl result, fun _ => result⟩
  | @three k l m r ha hb hc =>
    by_cases empty : l = .nil
    · subst l
      cases ha
      cases hb
      cases hc
      exact ⟨Or.inl (.two .nil .nil), fun _ => .two .nil .nil⟩
    · have wide : Wide l := ready.resolve_left empty
      have child := recursive l k (by simp only [nodes]; omega) ha wide
      have result : Balanced (k + 1) (descendFirst recur (.three l m r)).1 := by
        simpa only [descendFirst, ite_eq_right empty] using Balanced.three child hb hc
      exact ⟨Or.inl result, fun _ => result⟩
  | @four k a b c d ha hb hc hd =>
    by_cases empty : a = .nil
    · subst a
      cases ha
      cases hb
      cases hc
      cases hd
      exact ⟨Or.inl (.three .nil .nil .nil), fun _ => .three .nil .nil .nil⟩
    · have wide : Wide a := ready.resolve_left empty
      have child := recursive a k (by simp only [nodes]; omega) ha wide
      have result : Balanced (k + 1) (descendFirst recur (.four a b c d)).1 := by
        simpa only [descendFirst, ite_eq_right empty] using Balanced.four child hb hc hd
      exact ⟨Or.inl result, fun _ => result⟩

/-- Minimum extraction preserves balance. A wide root cannot lose height. -/
theorem extractMinAux_balance (fuel : Nat) {h : Nat} {t : Multiway}
    (valid : Balanced h t) (enough : t.nodes < fuel) :
    (Balanced h (extractMinAux fuel t).1 ∨ ∃ k, h = k + 1 ∧ Balanced k (extractMinAux fuel t).1) ∧
      (Wide t → Balanced h (extractMinAux fuel t).1) := by
  induction fuel generalizing h t with
  | zero => omega
  | succ fuel ih =>
    cases merged : t.rootMerge with
    | none =>
      obtain ⟨balanced, ready, wide⟩ := repairFirst_ready valid merged
      have reserve := repairFirst_nodes t
      have result := descendFirst_balance (extractMinAux fuel) balanced ready
        (fun child k smaller childBalance childWide =>
          (ih childBalance (by omega)).2 childWide)
      simpa only [extractMinAux, merged] using And.intro result.1 (fun hw => result.2 (wide hw))
    | some u =>
      have drop := (rootMerge_spec merged).2.1
      obtain ⟨k, height, balanced, wide⟩ := rootMerge_balance valid merged
      have result := (ih balanced (by omega)).2 wide
      refine ⟨Or.inr ⟨k, height, ?_⟩, ?_⟩
      · simpa only [extractMinAux, merged] using result
      · intro originalWide
        cases t <;> simp [Wide, rootMerge] at originalWide merged

end RotationBST.SplitTree.Multiway
