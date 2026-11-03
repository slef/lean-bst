module

public import RotationBST.Algorithms.Simulation.Supernode.Policy.Defs
public import RotationBST.Algorithms.Simulation.Supernode.Simulation.Initial

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode

/-- Choose this request's certified root access before any continuation is
known. The choice depends only on the current machine and request. -/
theorem Machine.step_exists {n : Nat} (A : OnlineAlgorithm n) (before : Machine n)
    (request : Nat) (bound : request < n) : ∃ result, before.Step A request result := by
  have legal := A.correct before.time request before.points before.history before.satisfied bound
  obtain ⟨represented, served, cost, debt, access, restore, paid⟩ :=
    nextState_access before.history legal before.represented before.size
  have size : (nextState before.stored (A.step before.time request before.points)).tree.size = n := by
    have first := access.1.size_eq
    have second := restore.size_eq
    have old := before.size
    omega
  let after : Machine n := {
    time := before.time + 1
    points := before.points ∪ row before.time (A.step before.time request before.points)
    stored := nextState before.stored (A.step before.time request before.points)
    actual := served
    debt := debt
    history := history_extend before.history legal
    satisfied := legal.2.2
    represented := represented
    size := size
    restore := restore }
  refine ⟨(after, before.debt + cost), rfl, rfl, rfl,
    ⟨before.restore.append access.1, access.2⟩, ?_⟩
  dsimp only [after]
  omega

noncomputable def Machine.advance {n : Nat} (A : OnlineAlgorithm n) (before : Machine n)
    (request : Nat) (bound : request < n) : Machine n × Nat :=
  Classical.choose (before.step_exists A request bound)

theorem Machine.advance_spec {n : Nat} (A : OnlineAlgorithm n) (before : Machine n)
    (request : Nat) (bound : request < n) : before.Step A request (before.advance A request bound) :=
  Classical.choose_spec (before.step_exists A request bound)

theorem Machine.actual_size {n : Nat} (machine : Machine n) : machine.actual.size = n :=
  machine.restore.size_eq.trans machine.size

/-- Start from any BST, charging initialization once to its first access. -/
theorem Machine.initial_exists (tree : Tree) :
    ∃ machine : Machine tree.size, machine.actual = tree ∧ machine.time = 0 ∧ machine.points = ∅ ∧
      machine.debt + machine.stored.credit ≤ 6016 * tree.size := by
  obtain ⟨debt, restore, budget⟩ := initialNested_budget tree
  exact ⟨{
    time := 0
    points := ∅
    stored := initialNested tree.size
    actual := tree
    debt := debt
    history := by intro p member; simp at member
    satisfied := by intro p member; simp at member
    represented := initialNested_represents tree.size
    size := initialNested_size tree.size
    restore := restore }, rfl, rfl, rfl, budget⟩

noncomputable def Machine.initial (tree : Tree) : Machine tree.size :=
  Classical.choose (Machine.initial_exists tree)

theorem Machine.initial_spec (tree : Tree) :
    (Machine.initial tree).actual = tree ∧ (Machine.initial tree).time = 0 ∧
      (Machine.initial tree).points = ∅ ∧
      (Machine.initial tree).debt + (Machine.initial tree).stored.credit ≤ 6016 * tree.size :=
  Classical.choose_spec (Machine.initial_exists tree)

end RotationBST.Geometric.Online.Supernode
