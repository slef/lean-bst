module

public import RotationBST.Arboral.Online.Split.Finger.Locate.Embedding.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Locate.Proofs
public import RotationBST.Arboral.Online.Split.Finger.Binary.Rotations

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

theorem leftSpine_frames (t : Multiway) : ∀ f ∈ leftSpine t, IsLeftFrame f := by
  induction t with
  | nil => simp [leftSpine]
  | two a b ia ib =>
    intro f member
    simp only [leftSpine, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact ia f member
    · trivial
  | three a b c ia ib ic =>
    intro f member
    simp only [leftSpine, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact ia f member
    · trivial
  | four a b c d ia ib ic id =>
    intro f member
    simp only [leftSpine, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact ia f member
    · trivial

/-- Reassembling a first-child context only appends the retained larger keys
to the local finger view; no rotation is needed for this identity. -/
theorem enclosingView_eq (fs : List Frame) (focus : Multiway)
    (left : ∀ f ∈ fs, IsLeftFrame f) :
    (binaryView (plug fs focus)).tree = enclosingView focus fs := by
  induction fs generalizing focus with
  | nil => rfl
  | cons f fs ih =>
    have head := left f (List.mem_cons_self ..)
    have tail := ih (f.fill focus) (fun g hg => left g (List.mem_cons_of_mem _ hg))
    simp only [plug, tail, enclosingView, contextRemainder]
    cases rest : contextRemainder fs <;>
      cases f <;> simp only [IsLeftFrame] at head
    all_goals simp [frameRemainder, Frame.fill, binaryView,
      BinaryView.tree, openView, comb_append, comb]

/-- The located interval's view is literally the full input finger BST with
its untouched enclosing remainder, rather than a separately initialized tree. -/
theorem locate_view (t : Multiway) (rank : Nat) :
    (binaryView t).tree = enclosingView (locate t rank).focus (locate t rank).outer := by
  calc
    (binaryView t).tree = (binaryView (plug (locate t rank).outer (locate t rank).focus)).tree :=
      congrArg (fun u => (binaryView u).tree) (locate_reconstruct t rank).symm
    _ = _ := enclosingView_eq _ _ (by
      intro f member
      exact leftSpine_frames t f (List.mem_of_mem_drop member))

end RotationBST.Arboral.Split.Multiway.Finger
