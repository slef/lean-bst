module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Potential.PhaseOne.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.PhaseOne.Results
open Items Reference

/-- The cut query agrees with the existing blue potential at a search forest. -/
theorem forest_blue (t : Tree) (lo searched x : Nat) (valid : lo ≤ x ∧ x < lo + leaves t) :
    rootBlue (forest t lo searched) x = blue t lo searched x :=
  rootBlue_forest t lo searched x valid

/-- Intermediate selected values are exactly their finite natural-valued amounts. -/
theorem amount (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point)
    (roots : List Component) (x : Nat) : itemAt t lo searches P roots x = WithTop.some (amountAt t lo searches P roots x) :=
  amount_exact t lo searches P roots x

/-- The initial cut has exactly the old total item potential. -/
theorem initial (t : Tree) (lo : Nat) (prior : List Nat) (old : Nat)
    {n : Nat} {P : Finset Point} (history : History n (prior.length + 1) P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) (domain : Finset Nat) :
    totalAt t lo (prior ++ [old]) P (forest t lo old) domain = totalAmount t lo (prior ++ [old]) P domain :=
  total_initial t lo prior old history valid domain

/-- The final cut has exactly the next intermediate total item potential. -/
theorem final (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) (domain : Finset Nat) :
    totalAt t lo searches P (forest t lo searched) domain = totalAmount t lo (searches ++ [searched]) P domain :=
  total_final t lo searches searched history valid domain

/-- At most six active columns per actual reference subtree can gain on a merge. -/
theorem charges {t : Tree} {lo k : Nat} {c : Component}
    (occurrence : Distance.Occurs t lo c k) {P : Finset Point} (satisfied : ASS P) :
    (chargedKeys t lo P c).card ≤ 6 :=
  charged_count occurrence satisfied

/-- Splits add no item potential; merges add at most twelve. -/
theorem local_change (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point}
    (satisfied : ASS P) (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t)
    {roots next : List Component} {event : Transitions.Event}
    (cut : Transitions.Cut t lo roots) (step : Transitions.Step roots event next)
    (admissible : Transitions.Admissible t lo event) (domain : Finset Nat) :
    totalAt t lo searches P next domain ≤ totalAt t lo searches P roots domain +
      (if event.isMerge then 12 else 0) :=
  step_total t lo searches satisfied valid cut step admissible domain

/-- Only merge events consume item-potential credit along a certified trace. -/
theorem trace_change (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point}
    (satisfied : ASS P) (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t)
    {roots next : List Component} {events : List Transitions.Event}
    (trace : Transitions.Trace roots events next) (cut : Transitions.Cut t lo roots)
    (admissible : ∀ e ∈ events, Transitions.Admissible t lo e) (domain : Finset Nat) :
    totalAt t lo searches P next domain ≤ totalAt t lo searches P roots domain + 12 * Transitions.merges events :=
  trace_total t lo searches satisfied valid trace cut admissible domain

/-- The actual LCA plan bounds the old-to-intermediate item-potential change. -/
theorem items_change (t : Tree) (lo : Nat) (prior : List Nat) (old next : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n (prior.length + 1) P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) (domain : Finset Nat) :
    totalAmount t lo ((prior ++ [old]) ++ [next]) P domain ≤
      totalAmount t lo (prior ++ [old]) P domain + 12 * Transitions.merges (Transitions.plan t lo old next) :=
  plan_items t lo prior old next satisfied history valid domain

/-- Lemma 3.3: all item and virgin potential increases fit the 24-per-reference-edge bound. -/
theorem step (t : Tree) (lo : Nat) (prior : List Nat) (old next : Nat)
    (valid : ∀ x ∈ (prior ++ [old]) ++ [next], lo ≤ x ∧ x < lo + leaves t) (domain : Finset Nat) :
    totalAmount t lo ((prior ++ [old]) ++ [next]) (Virgin.points (prior ++ [old])) domain +
        Virgin.before t lo (prior ++ [old]) next ≤
      totalAmount t lo (prior ++ [old]) (Virgin.points (prior ++ [old])) domain +
        Virgin.after t lo prior old + 24 * Transitions.edges t lo old next :=
  PhaseOne.step t lo prior old next valid domain

end RotationBST.Geometric.GreedyASS.Potential.PhaseOne.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Potential.PhaseOne.Results`: 9 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Potential.PhaseOne.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Models.Geometric.Offline.Abstract,
  RotationBST.Algorithms.GreedyASS.Algorithm.Abstract,
  RotationBST.Algorithms.GreedyASS.Items.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Transitions.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Potential.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Potential.PhaseOne.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Virgin.Definitions.Abstract]
