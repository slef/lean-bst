module

public import RotationBST.Structures.FingerHand.Packed.Updates.Shapes
public import RotationBST.Structures.Tendon.RemoveTop
public import RotationBST.Structures.Tendon.RemoveBottom

@[expose] public section
namespace RotationBST.FingerHand.Hand

theorem exposeTop (cs : List Pointer.Frame) (d : Tendon.State) (f : Pointer.Frame) (l r : Hand)
    (valid : (Hand.node (cs ++ [f]) d l r).Valid) :
    ∃ (e : Tendon.State) (k : Nat),
      Expansion (.node (cs ++ [f]) d l r) (graft [] (Tendon.State.ofPath []) f (.node cs e l r)) ∧
      Pointer.Trace ⟨(Hand.node (cs ++ [f]) d l r).tree, []⟩
        ⟨(graft [] (Tendon.State.ofPath []) f (.node cs e l r)).tree, []⟩ k ∧
      k + (graft [] (Tendon.State.ofPath []) f (.node cs e l r)).potential ≤
        132 + (Hand.node (cs ++ [f]) d l r).potential := by
  obtain ⟨e, k, rep, bound, trace⟩ := Tendon.State.removeTop f valid.1 (.node l.tree r.tree)
  refine ⟨e, k, ?_, ?_, ?_⟩
  · exact ⟨valid, graft_valid f (Tendon.State.ofPath_represents []) ⟨rep, valid.2⟩,
      top_reference cs d e f l r, by simp [graft_count, count], top_keys cs d e f l r⟩
  · simpa only [graft_tree, tree, empty_tendon_tree] using trace
  · simp only [graft_potential, potential, empty_tendon_potential]
    omega

theorem suppressTop (cs : List Pointer.Frame) (d : Tendon.State) (f : Pointer.Frame) (l r : Hand)
    (valid : (Hand.node cs d l r).Valid) :
    Expansion (.node (cs ++ [f]) (d.addTop f) l r)
      (graft [] (Tendon.State.ofPath []) f (.node cs d l r)) ∧
    ∃ k, Pointer.Trace ⟨(graft [] (Tendon.State.ofPath []) f (.node cs d l r)).tree, []⟩
      ⟨(Hand.node (cs ++ [f]) (d.addTop f) l r).tree, []⟩ k ∧
      k + (Hand.node (cs ++ [f]) (d.addTop f) l r).potential ≤
        86 + (graft [] (Tendon.State.ofPath []) f (.node cs d l r)).potential := by
  constructor
  · exact ⟨⟨Tendon.State.addTop_represents valid.1 f, valid.2⟩,
      graft_valid f (Tendon.State.ofPath_represents []) valid,
      top_reference cs (d.addTop f) d f l r, by simp [graft_count, count],
      top_keys cs (d.addTop f) d f l r⟩
  · obtain ⟨k, bound, trace⟩ := d.addTop_amortized f (.node l.tree r.tree)
    refine ⟨k, ?_, ?_⟩
    · simpa only [graft_tree, tree, empty_tendon_tree] using trace
    · simp only [graft_potential, potential, empty_tendon_potential]
      omega

theorem exposeBottom (cs : List Pointer.Frame) (d : Tendon.State) (f : Pointer.Frame) (l r : Hand)
    (valid : (Hand.node (f :: cs) d l r).Valid) :
    ∃ (e : Tendon.State) (k : Nat),
      Expansion (.node (f :: cs) d l r) (graft cs e f (.node [] (Tendon.State.ofPath []) l r)) ∧
      Pointer.Trace ⟨(Hand.node (f :: cs) d l r).tree, []⟩
        ⟨(graft cs e f (.node [] (Tendon.State.ofPath []) l r)).tree, []⟩ k ∧
      k + (graft cs e f (.node [] (Tendon.State.ofPath []) l r)).potential ≤
        180 + (Hand.node (f :: cs) d l r).potential := by
  obtain ⟨e, k, rep, bound, trace⟩ := Tendon.State.removeBottom f valid.1 (.node l.tree r.tree)
  refine ⟨e, k, ?_, ?_, ?_⟩
  · exact ⟨valid, graft_valid f rep ⟨Tendon.State.ofPath_represents [], valid.2⟩,
      bottom_reference cs d e f l r, by simp [graft_count, count], bottom_keys cs d e f l r⟩
  · simpa only [graft_tree, tree, empty_tendon_tree] using trace
  · simp only [graft_potential, potential, empty_tendon_potential]
    omega

theorem suppressBottom (cs : List Pointer.Frame) (d : Tendon.State) (f : Pointer.Frame) (l r : Hand)
    (valid : (Hand.node cs d l r).Valid) :
    Expansion (.node (f :: cs) (d.addBottom f) l r)
      (graft cs d f (.node [] (Tendon.State.ofPath []) l r)) ∧
    ∃ k, Pointer.Trace ⟨(graft cs d f (.node [] (Tendon.State.ofPath []) l r)).tree, []⟩
      ⟨(Hand.node (f :: cs) (d.addBottom f) l r).tree, []⟩ k ∧
      k + (Hand.node (f :: cs) (d.addBottom f) l r).potential ≤
        134 + (graft cs d f (.node [] (Tendon.State.ofPath []) l r)).potential := by
  constructor
  · exact ⟨⟨Tendon.State.addBottom_represents valid.1 f, valid.2⟩,
      graft_valid f valid.1 ⟨Tendon.State.ofPath_represents [], valid.2⟩,
      bottom_reference cs (d.addBottom f) d f l r, by simp [graft_count, count],
      bottom_keys cs (d.addBottom f) d f l r⟩
  · obtain ⟨k, bound, trace⟩ := d.addBottom_amortized f (.node l.tree r.tree)
    refine ⟨k, ?_, ?_⟩
    · simpa only [graft_tree, tree, empty_tendon_tree] using trace
    · simp only [graft_potential, potential, empty_tendon_potential]
      omega

theorem exposeKnuckle (l r : Tree) :
    Expansion (.knuckle (.node l r)) (.node [] (Tendon.State.ofPath []) (.knuckle l) (.knuckle r)) := by
  refine ⟨trivial, ⟨Tendon.State.ofPath_represents [], trivial, trivial⟩, rfl, rfl, ?_⟩
  intro lo
  exact List.nil_sublist _

end RotationBST.FingerHand.Hand
