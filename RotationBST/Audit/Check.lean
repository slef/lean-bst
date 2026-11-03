/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module

public meta import Lean.Elab.Command
public meta import Lean.Util.FoldConsts
public meta import Lean.Util.CollectAxioms

/-!
# Mechanical audit for the local abstract reading interface

Adapted from Complexitylib's `abstracts/ComplexityAbstracts/Check.lean`,
blob `6e452da3b9e27768370ebfe817ca94676cb37993`, by Erik Demaine and
Samuel Schlesinger, itself adapted from `edemaine/lean-canny`.

Unlike the upstream namespace-wide command, this local command audits declarations
in the current file under the named namespace. Different result files may share
a namespace. It traverses theorem types, definition types and bodies, and
inductive constructors. Every local-project dependency must belong to an
explicitly allowlisted foundation module, and traversal continues through those
foundations. Proof bodies are checked for standard axiom dependencies but are
not part of the statement reading boundary.

This checks the dependency boundary, not mathematical intent. Readers must
still inspect the listed foundations and the absence of misleading syntax.
The upstream tool's copyright and Apache 2.0 license are retained in this
directory's LICENSE file.
-/

public meta section

namespace RotationBST.AbstractAudit

open Lean Elab Command

/-- Recover the user-facing name of a declaration, stripping any `_private.<mod>.0.` prefix
added by Lean for `private` definitions or equation-compiler matchers. -/
def userFacingName (name : Name) : Name :=
  privateToUserName name

/-- Determine whether `name` (after stripping any `_private` prefix) lies inside `ns`. -/
def inAbstractNamespace (ns name : Name) : Bool :=
  ns.isPrefixOf (userFacingName name)

/-- The constants that `info` mentions in its statement and, unless it is a theorem, in its
body; for an inductive type, also its constructors. -/
def statementDependencies (info : ConstantInfo) : Array Name := Id.run do
  let mut deps := info.type.getUsedConstants
  if let .inductInfo val := info then
    deps := deps ++ val.ctors.toArray
  if !info.isTheorem then
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
  return deps

/-- Audit all declarations in `abstractNamespace` as described in the module docstring:
select current-file roots, reject transitive dependencies on
non-allowlisted `RotationBST.*` or `RotationBSTTests.*` modules in
definitions and theorem statements, and reject non-standard axioms. On success, log the number of
audited roots and, as silent information not pinned by `#guard_msgs`, the number of transitive
dependencies checked. -/
def checkAbstract (abstractNamespace : Name) (allowedModules : Array Name := #[]) :
    CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  -- Sort the namespace's declarations so that the reported error does not depend on the
  -- iteration order of the environment.
  let members := (env.constants.toList.filter fun (name, _) =>
    inAbstractNamespace abstractNamespace name &&
      (env.getModuleIdxFor? name).isNone).toArray.qsort fun a b => a.1.lt b.1
  let mut pending : Array (Name × Name) := #[]
  for (name, info) in members do
    for ax in ← collectAxioms name do
      unless allowedAxioms.contains ax do
        throwError "abstract audit: `{userFacingName name}` depends on disallowed axiom `{ax}`"
    -- Generated helpers such as `_unsafe_rec` are exempt; `partial` and `unsafe` declarations
    -- themselves are caught through their user-facing names.
    unless (userFacingName name).isInternalDetail do
      if info.isUnsafe || info matches .opaqueInfo _ then
        throwError
          "abstract audit: `{userFacingName name}` is `opaque`, `partial`, or `unsafe`"
    -- Every member is a root, so private and internal-looking declarations are audited even
    -- when nothing else in the namespace refers to them.
    for c in statementDependencies info do
      pending := pending.push (name, c)
  let roots := members.size
  if roots == 0 then
    throwError "abstract audit: no declarations found in namespace `{abstractNamespace}`"
  -- Process roots in sorted order: `pending` is a stack.
  pending := pending.reverse
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let (root, name) := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    match env.getModuleIdxFor? name with
    | none =>
      unless inAbstractNamespace abstractNamespace name do
        throwError
          "abstract audit: `{userFacingName root}` depends on declaration `{userFacingName name}` \
           outside `{abstractNamespace}`"
      if let some info := env.find? name then
        if info.isUnsafe || info matches .opaqueInfo _ then
          throwError
            "abstract audit: `{userFacingName root}` depends on `opaque`, `partial`, or `unsafe` \
             declaration `{userFacingName name}`"
        for c in statementDependencies info do
          pending := pending.push (root, c)
    | some idx =>
      let owner := env.header.moduleNames[idx.toNat]!
      let isLocalRepo := (`RotationBST).isPrefixOf owner || (`RotationBSTTests).isPrefixOf owner
      if isLocalRepo then
        unless allowedModules.contains owner do
          throwError
            "abstract audit: `{userFacingName root}` depends on implementation declaration \
             `{userFacingName name}` from `{owner}`"
        -- An allowlisted declaration is part of what the reader inspects, so its own statement
        -- and body must again stay within the allowlist.
        if let some info := env.find? name then
          for c in statementDependencies info do
            pending := pending.push (root, c)
  logInfo m!"abstract audit passed for `{abstractNamespace}`: {roots} root declarations"
  log m!"abstract audit for `{abstractNamespace}`: {visited.size} dependencies checked"
    (severity := .information) (isSilent := true)

/-- `#check_bst_abstract Namespace` audits the current file's declarations in `Namespace`,
checking that their statements and (for non-theorems) bodies reference only that namespace and
the background libraries (`Init`, `Std`, `Lean`, `Batteries`, `Mathlib`, upstream `Cslib`), and that it
depends only on the standard axioms. On success it logs the number of audited roots and, as silent
information not pinned by `#guard_msgs`, the number of transitive dependencies checked.

`#check_bst_abstract Namespace allowing [Mod1, Mod2]` additionally permits references to the listed
`RotationBST.*` or `RotationBSTTests.*` modules. The audit traverses
allowlisted declarations too, so the list must be closed under their transitive statement and
definition dependencies. -/
syntax (name := checkAbstractCmd)
  "#check_bst_abstract " ident (" allowing " "[" ident,* "]")? : command

@[command_elab checkAbstractCmd, inherit_doc checkAbstractCmd]
def elabCheckAbstract : CommandElab
  | `(#check_bst_abstract $ns:ident) =>
    checkAbstract ns.getId #[]
  | `(#check_bst_abstract $ns:ident allowing [$[$mods:ident],*]) =>
    checkAbstract ns.getId (mods.map (·.getId))
  | _ => throwUnsupportedSyntax

end RotationBST.AbstractAudit

