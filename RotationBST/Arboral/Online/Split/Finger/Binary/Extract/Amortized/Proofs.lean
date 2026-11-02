module

public import RotationBST.Arboral.Online.Split.Finger.Binary.Extract.Amortized.Local

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

theorem fingerHeight_eq {h : Nat} {t : Multiway} (valid : Balanced h t) : fingerHeight t = h := by
  induction valid <;> simp_all [fingerHeight]

theorem storedCredit_eq {h : Nat} {t : Multiway} (valid : Balanced h t) (root : Bool) :
    storedCredit root t = repairCredit h root t := by
  simp only [storedCredit, fingerHeight_eq valid]

private theorem descent_credit (recur : Multiway → Multiway × Nat) (cost : Multiway → Nat)
    {h : Nat} {t : Multiway} (valid : Balanced h t) (root : Bool)
    (ready : firstChild t = .nil ∨ Wide (firstChild t))
    (recursive : ∀ child k, child.nodes < t.nodes → Balanced k child → Wide child →
      Balanced k (recur child).1 ∧
        cost child + storedCredit true (recur child).1 ≤ storedCredit true child + 3) :
    (if firstChild t = .nil then 0 else cost (firstChild t)) +
      storedCredit root (descendFirst recur t).1 ≤ storedCredit root t + 3 := by
  cases valid with
  | nil => simp [firstChild, descendFirst, storedCredit, fingerHeight, repairCredit]
  | @two k l r ha hb =>
    by_cases empty : l = .nil
    · subst l; cases ha; cases hb
      cases root <;> simp [firstChild, descendFirst, storedCredit, fingerHeight, repairCredit]
    · obtain ⟨balanced, bound⟩ := recursive l k (by simp only [nodes]; omega) ha (ready.resolve_left empty)
      simp only [storedCredit_eq ha, storedCredit_eq balanced] at bound
      simp only [firstChild, descendFirst, empty, ite_false]
      rw [storedCredit_eq (.two balanced hb), storedCredit_eq (.two ha hb)]
      simp only [repairCredit, Nat.add_sub_cancel]
      omega
  | @three k l m r ha hb hc =>
    by_cases empty : l = .nil
    · subst l; cases ha; cases hb; cases hc
      cases root <;> simp [firstChild, descendFirst, storedCredit, fingerHeight, repairCredit]
    · obtain ⟨balanced, bound⟩ := recursive l k (by simp only [nodes]; omega) ha (ready.resolve_left empty)
      simp only [storedCredit_eq ha, storedCredit_eq balanced] at bound
      simp only [firstChild, descendFirst, empty, ite_false]
      rw [storedCredit_eq (.three balanced hb hc), storedCredit_eq (.three ha hb hc)]
      simp only [repairCredit, Nat.add_sub_cancel]
      omega
  | @four k a b c d ha hb hc hd =>
    by_cases empty : a = .nil
    · subst a; cases ha; cases hb; cases hc; cases hd
      cases root <;> simp [firstChild, descendFirst, storedCredit, fingerHeight, repairCredit]
    · obtain ⟨balanced, bound⟩ := recursive a k (by simp only [nodes]; omega) ha (ready.resolve_left empty)
      simp only [storedCredit_eq ha, storedCredit_eq balanced] at bound
      simp only [firstChild, descendFirst, empty, ite_false]
      rw [storedCredit_eq (.four balanced hb hc hd), storedCredit_eq (.four ha hb hc hd)]
      simp only [repairCredit, Nat.add_sub_cancel]
      omega

/-- Minimum extraction has amortized cost at most three, while retaining its
finger encoding. The potential is evaluated at the result's actual height. -/
theorem extractFingerAux_credit (fuel : Nat) {h : Nat} {t : Multiway}
    (valid : Balanced h t) (enough : t.nodes < fuel) (root : Bool) :
    extractOpenCost fuel t + storedCredit root (extractMinAux fuel t).1 ≤ storedCredit root t + 3 ∧
      extractViewCost fuel t + storedCredit root (extractMinAux fuel t).1 ≤ storedCredit root t + 3 := by
  induction fuel generalizing h t root with
  | zero => omega
  | succ fuel ih =>
    cases merged : t.rootMerge with
    | some u =>
      obtain ⟨k, height, balanced, wide⟩ := rootMerge_balance valid merged
      have drop := (rootMerge_spec merged).2.1
      have bound := ih balanced (by omega) root
      have positive : k ≠ 0 := by intro eq; subst k; cases balanced; contradiction
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero positive
      subst h
      have credit := rootMerge_credit j merged root
      have old := storedCredit_eq valid root
      have new := storedCredit_eq balanced root
      simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] at old new credit
      simp only [extractOpenCost, extractViewCost, extractMinAux, merged]
      constructor <;> omega
    | none =>
      obtain ⟨balanced, ready, _⟩ := repairFirst_ready valid merged
      have reserve := repairFirst_nodes t
      have descent := descent_credit (extractMinAux fuel) (extractOpenCost fuel) balanced root ready
        (fun child k smaller childBalance childWide =>
          ⟨(extractMinAux_balance _ childBalance (by omega)).2 childWide,
            (ih childBalance (by omega) true).1⟩)
      have credit := balanced_repair_credit valid root merged
      rw [← storedCredit_eq balanced root, ← storedCredit_eq valid root] at credit
      simp only [extractOpenCost, extractViewCost, extractMinAux, merged]
      constructor <;> omega

end RotationBST.Arboral.Split.Multiway.Finger
