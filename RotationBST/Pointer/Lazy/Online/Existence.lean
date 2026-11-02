module

public import RotationBST.Pointer.Lazy.Online.Definitions.Abstract
public import RotationBST.Pointer.Lazy.Simulation

@[expose] public section

namespace RotationBST.Pointer.Lazy.Online

theorem transition_exists (a : Algorithm) (past : List Nat) (s : State) (x : Nat)
    (valid : x < s.virtual.size) : ∃ result, Transition a past s x result := by
  have ha := a.correct past s.virtual x valid
  have hh : Access s.current (a.step past s.virtual x).1 x
      (s.pending + (a.step past s.virtual x).2) := ⟨s.certificate.append ha.1, ha.2⟩
  obtain ⟨q, r, d, c, hs, hd, hcount, hcost⟩ := Lazy.access_to_pointer hh
  exact ⟨(⟨q, (a.step past s.virtual x).1, d, hd⟩, c), hs, rfl, by dsimp; omega⟩

end RotationBST.Pointer.Lazy.Online
