module

import RotationBST
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Audit every imported declaration owned by this library, including generated
public helpers. This checks compiled axiom dependencies, not mathematical intent
or evaluation cost. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`RotationBST).isPrefixOf env.header.moduleNames[idx.toNat]! then
        count := count + 1
        for ax in ← collectAxioms name do
          unless allowed.contains ax do
            throwError "library axiom audit: {name} depends on {ax}"
  if count == 0 then throwError "library axiom audit: no declarations found"
  log m!"Library axiom audit passed for {count} imported declarations"
    (severity := .information) (isSilent := true)
