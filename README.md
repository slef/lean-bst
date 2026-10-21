# lean-bst

A small Lean model of binary search trees with implicit inorder labels.

A tree stores only its shape. An access to rank `x` is a sequence of local
rotations that finishes with `x` at the root, meaning that the final left
subtree has exactly `x` nodes.

## Lean code

- [RotationBST.lean](RotationBST.lean): tree shapes, rotations, accesses,
  executions, online rules, dynamic optimality and the working-set bound.
- [RotationBSTTests.lean](RotationBSTTests.lean): concrete executions,
  boundary cases, working-set examples and a proof that valid online runs
  produce legal executions.

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake build --wfail
```

The project pins Lean **4.33.1** and uses only `Std`; it has no Mathlib dependency.
The core, the state-elimination development, and their checked examples are
default build targets.

## Explanation and figures

[docs/main.texlish](docs/main.texlish) explains every definition, with tree
figures and an introduction to its relationship with standard BST models.
It follows the prose-and-Lean-snippet presentation of the Lean section in
[Demaine and Langerman's translation-tiling paper](https://github.com/edemaine/translation-tiling-paper).
The documentation workflow builds a PDF available as a GitHub Actions artifact.

To build it locally, install [Texlish](https://texlish.org/) (`npm install -g texlish@0.2.0`), Python 3, and a TeX distribution with `latexmk`, TikZ,
`listings`, `tcolorbox`, Libertine, `newtxmath` and Inconsolata:

```sh
make -C docs
```

The PDF is `docs/build/main.pdf`. Displayed code is extracted from the Lean
source by `docs/extract_snippets.py`; edit `docs/main.texlish` for prose.
The CI workflow also checks that the committed snippets match the source.

## Model and current scope

The current cost is **rotations only**; an access to the current root can cost
zero. The standard normalization adds one per request: `m + rotations` for a
sequence of length `m`. These costs are not multiplicatively equivalent on
all inputs (consider repeated requests to a root).

The shape representation is in bijection with labelled BSTs on a fixed ordered
key set, and local rotations preserve those inorder identities. The connection
from root-access rotation executions to pointer-based BST executions additionally
needs a costed simulation, including treatment of rotations away from the access
path. See the document's opening discussion and [Derryberry's thesis,
Sections 2.2 and 3.4](https://www.cs.cmu.edu/~jonderry/thesis.pdf).

The core Lean file proves size preservation and that successful accesses
are in range. The additional state-elimination file proves access existence.
The representation correspondence and pointer-model simulation remain to be
formalized. Dynamic optimality and the working-set bound
are **definitions**, not proved guarantees for a supplied algorithm. In particular,
`DynamicallyOptimal` currently compares rotation counts; a conventional total-cost
competitive theorem must account explicitly for the additive `m` term.

The online interface returns an endpoint and a certified count, rather than an
explicit rotation program. Planning computation is uncharged.

## State elimination: proof attempt

[StateElimination.lean](StateElimination.lean) formalizes the question whether
auxiliary private state can be removed at constant-factor cost. **The general
statement is not proved or assumed.** It is recorded as the proposition
`StateElimination`, with constants uniform in tree size and input length.

`StatefulAlgorithm σ` has explicit initialization from the initial tree and
an online step receiving only private state, the current tree and the current
request. `TreeAlgorithm` is its `σ := Unit` special case. This file uses total
cost **requests + rotations**. The original history-based interface embeds
into it, with a proved equality of executions.

The following partial results are checked:

- `moveToRoot_correct` and `access_exists`: every existing rank can be brought
  to the root in fewer than `n` rotations, constructively.
- `StatefulAlgorithm.execution`: every valid run produces a legal execution.
- `size_factor_simulation`: a particular tree-only algorithm has cost at most
  `n` times that of any stateful algorithm. This factor depends on `n` and
  does **not** establish the conjecture.
- `StatefulAlgorithm.erase_totalCost`: exact state elimination is possible
  when the private state is recoverable from the current tree, initialization
  satisfies that invariant, and every valid step preserves it.
- `stateElimination_of_universal`: a universally competitive tree-only
  algorithm would imply the conjecture. No such algorithm is supplied here.

[StateEliminationTests.lean](StateEliminationTests.lean) checks concrete
executions, a recoverable size cache, and a private bit that toggles while
the tree stays fixed. The latter shows that exact state recovery is not
automatic. It is **not a counterexample to constant-factor state elimination**:
that bit does not influence the rotation choices. Named axiom guards cover
the main partial results.

The unresolved step is a cost-controlled way to replace genuinely
history-dependent choices by a tree-only rule. Equality of the legal move
sets at a tree does not establish this: two histories can leave the same
tree with different private states, and the requested theorem must compare
entire executions with a factor independent of `n`. Both a proof and a
counterexample to the general statement remain absent from this attempt.

[TreeReset.lean](TreeReset.lean) proves that any two equal-size trees can be
reconfigured in at most `2n` rotations. `reset_then_access` charges this reset
at the start of the next access, preserving the required root at its end.
This verifies the geometric ingredient of the proposed block-reset argument;
it does not remove the private memory used within or between blocks.

## Normalizing the additive term (conditional theorem)

[AdditiveNormalization.lean](AdditiveNormalization.lean) proves that if a
**tree-only** algorithm B already satisfies
`cost_B ≤ C * offline_cost + f(n)` against every legal execution, then another
tree-only algorithm satisfies the same bound with additive `(2 + 6*C)*n`.
The coefficient C is unchanged. The construction resets to a selected tree
when an amortized credit exceeds a threshold determined by the current shape.
It introduces no private state, but is noncomputable in this existence model.

[CompetitiveCredit.lean](CompetitiveCredit.lean) proves the credit's existence,
attainment, variation bound and one-step inequality.
[CostComposition.lean](CostComposition.lean) supplies execution composition and
changes of initial tree. [SimulationPotential.lean](SimulationPotential.lean)
provides a general potential criterion for simulation.

This theorem assumes offline competitiveness to start with; it does not prove
state elimination for an arbitrary online comparator.

## Purely additive simulation is impossible

[ThreeKeySeparation.lean](ThreeKeySeparation.lean) proves a separation on three
keys. One fixed online algorithm with a clock modulo eight serves
`(0,2,1,0,2,0,2,1)^m` from the balanced tree at total cost **19m**. Every
tree-only algorithm costs at least **20m** on the same inputs.

Consequently no bound `cost_B ≤ cost_A + f(n)` can hold for this A, for any
function f of tree size alone. The complete quantified theorem is
`ThreeKey.no_purely_additive_simulation`, including execution and legality proofs.
See the [short mathematical explanation](research/pure-additive-obstruction.md).

This rules out multiplicative coefficient **one**. The original question with
an arbitrary constant coefficient and additive O(n) remains unresolved.

## Development

```sh
lake build --wfail
python3 docs/extract_snippets.py
make -C docs
```

Contributions should keep the small core readable, use checked examples, and
state clearly which model and cost convention a result concerns. The initial
formalization, tests and explanatory document were prepared with OpenAI Codex.
