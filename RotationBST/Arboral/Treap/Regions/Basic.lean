module

public import RotationBST.Arboral.Treap.Regions.Abstract
public import RotationBST.Pointer.Lazy.Skeleton

@[expose] public section
namespace RotationBST.Arboral.Region
open Pointer.Lazy.Skeleton

theorem holes_fringe (s : Region) (lo : Nat) :
    (holes s lo).map Prod.snd = s.fringe := by
  induction s generalizing lo with
  | hole t => rfl
  | node l r il ir => simp [holes, fringe, il, ir]

theorem Same.fringe {s t : Region} {lo : Nat} (h : Same s t lo) : s.fringe = t.fringe := by
  have := congrArg (List.map Prod.snd) h.2.2
  simpa only [holes_fringe] using this

theorem Same.size {s t : Region} {lo : Nat} (h : Same s t lo) : s.size = t.size := by
  have := congrArg List.length h.fringe
  simp only [fringe_length] at this
  omega

theorem Same.refl (s : Region) (lo : Nat) : Same s s lo := ⟨rfl, rfl, rfl⟩

theorem Same.trans {s t u : Region} {lo : Nat} (h : Same s t lo) (h' : Same t u lo) :
    Same s u lo := ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

theorem same_node {l l' r r' : Region} {lo : Nat}
    (hl : Same l l' lo) (hr : Same r r' (lo + l.tree.size + 1)) :
    Same (.node l r) (.node l' r') lo := by
  obtain ⟨hls, hlk, hlh⟩ := hl
  obtain ⟨hrs, hrk, hrh⟩ := hr
  refine ⟨?_, ?_, ?_⟩
  · simp only [tree, Tree.size, hls, hrs]
  · simp only [keys, ← hls, hlk, hrk]
  · simp only [holes, ← hls, hlh, hrh]

theorem same_right (a b c : Region) (lo : Nat) :
    Same (.node (.node a b) c) (.node a (.node b c)) lo := by
  unfold Same
  simp only [tree, Tree.size, keys, holes]
  constructor
  · omega
  constructor
  · simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Finset.insert_union, Finset.union_insert, Finset.insert_comm, Finset.union_assoc]
  · simp only [List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Any active key can be promoted to the root without changing the fringe. -/
theorem expose (s : Region) (lo x : Nat) (hx : x ∈ keys s lo) :
    ∃ a b : Region, Same s (.node a b) lo ∧ lo + a.tree.size = x := by
  induction s generalizing lo x with
  | hole t => simp [keys] at hx
  | node l r il ir =>
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact ⟨l, r, Same.refl _ _, hx.symm⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨a, b, hl, hx⟩ := il lo x hx
      refine ⟨a, .node b r, ?_, hx⟩
      exact (same_node hl (Same.refl _ _)).trans (same_right a b r lo)
    · obtain ⟨a, b, hr, hx⟩ := ir (lo + l.tree.size + 1) x hx
      refine ⟨.node l a, b, ?_, ?_⟩
      · have hrot := same_right l a b lo
        have rev : Same (.node l (.node a b)) (.node (.node l a) b) lo :=
          ⟨hrot.1.symm, hrot.2.1.symm, hrot.2.2.symm⟩
        exact (same_node (Same.refl _ _) hr).trans rev
      · simp only [tree, Tree.size] at *; omega

end RotationBST.Arboral.Region
