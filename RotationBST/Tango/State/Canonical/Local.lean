module

public import RotationBST.Tango.State.Canonical.Proofs
public import RotationBST.Tango.Wilber.Normalization

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Subtree-local form of the canonical marking, used to verify the executable
preference log against the absolute-rank specification. -/
def localCanonical : Tree → List Nat → MarkedTree
  | .nil, _ => .nil
  | .node l r, past =>
      let left := localCanonical l (leftRequests l.size past)
      let right := localCanonical r (rightRequests l.size past)
      match (regions l.size (l.size + 1 + r.size) past).getLast? with
      | none => .node left right true true
      | some true => .node left right false true
      | some false => .node left right true false

@[simp] theorem localCanonical_tree (t : Tree) (past : List Nat) :
    (localCanonical t past).tree = t := by
  induction t generalizing past with
  | nil => rfl
  | node l r il ir =>
    simp only [localCanonical]
    split <;> simp only [tree, il, ir]

theorem canonical_eq_local (t : Tree) (lo : Nat) (past : List Nat) :
    canonical t lo past = localCanonical t (localRequests lo (lo + t.size) past) := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
    have he : lo + (l.size + 1 + r.size) = lo + l.size + 1 + r.size := by omega
    simp only [canonical, localCanonical, Tree.size, he, local_regions, local_left, local_right,
      ← il, ← ir]
    rfl

theorem localCanonical_eq (t : Tree) (past : List Nat) (valid : ∀ x ∈ past, x < t.size) :
    localCanonical t past = canonical t 0 past := by
  rw [canonical_eq_local]
  congr 1
  simp only [localRequests, Nat.zero_add, Nat.zero_le, true_and, Nat.sub_zero, List.map_id_fun']
  symm
  apply List.filter_eq_self.mpr
  intro x hx
  simpa using valid x hx

end RotationBST.Tango.MarkedTree
