# Scope audit and computability route

## Quantifiers checked

The proved equivalence keeps one simulator B and one multiplicative constant for
all tree sizes and all finite valid inputs. Its additive allowance depends only
on n. All algorithms start from the same tree, initialized without future input.
The periodic learner is a single algorithm, not a different comparator chosen
after seeing B. Its private state is the observed request history. It receives
the current request before choosing a forecast; consistency includes that request.
A forecast plan may depend on its entire predicted word, but the selection of
that prediction depends only on observations. Incorrect forecasts are legal too.

Tree-only means Unit persistent state: neither a phase counter nor the original
algorithm's private state is silently retained. Proof potentials may inspect
additional data; the implemented tree-only rule cannot. The product-graph proof
uses only reachable pairs of endpoints, and repetition returns both endpoints.
The finite graph allowance can depend on B and n but not on input length.

All statements charge requests plus rotations. They do not charge planning.
In particular they are not running-time claims about executing the Lean code.
The small core permits rotations anywhere in a tree without charging travel.
A transfer to the usual pointer-cost model still needs a separate simulation.

## Related work does not directly erase all state

Iacono's [2013 survey](https://arxiv.org/pdf/1306.0207) distinguishes unrestricted
online planning from implementations with bounded registers and node annotations.
Its final construction combines epoch algorithms and resets to a canonical tree;
this supports the usefulness of resets, but does not supply a tree-only rule in
our sense. The survey also distinguishes existence questions for offline,
online, and implementable BST algorithms. These distinctions should remain
explicit when discussing our equivalence. (Sections 1 and 4.)

[Combining Binary Search Trees](https://arxiv.org/pdf/1304.7604) combines a constant
number of algorithms under conditions on their cost bounds. Its implementation
uses node annotations and saved tree-state buffers. Thus it does not directly
remove persistent information beyond the tree shape. This is a limitation of
applying that construction here, not a negative result about our conjecture.
(Sections 2–4.)

No novelty claim or exhaustive literature review is made.

## Computable periodic plans: a separate route

The Lean proof constructs good infinite plans by classical choice. For a fixed
ultimately periodic forecast, that particular choice construction can be avoided:

1. Enumerate all size-n tree shapes and their rotation distances by finite BFS.
2. For a period of length l, form vertices (phase, tree) where the tree has the
   root requested at the preceding phase. Each transition advances phase and
   chooses any endpoint with the new requested root. Its cost is one plus the
   shortest rotation distance.
3. Find a minimum-average directed cycle. A minimum cycle can be simple, so its
   length is at most the number of vertices; enumerate the finitely many possible
   rational cost/length values and test for negative cycles after subtracting
   each proposed mean. At the minimum mean, a feasible potential and a cycle
   of tight edges certify both directions of optimality.
4. Rotate the cycle to phase zero. Its length is a multiple of l. Reset into
   the phase-compatible cycle tree and repeat it. A finite preperiod and a
   partial final cycle contribute bounded cost.

The least-consistent learner is computable as well: finite covers can be
searched in order, and compatibility with finite history is decidable. Once the
correct periodic forecast stabilizes, the minimum-average schedule has no greater
long-run cost than any periodic serving witness. The fixed transient and cycle
remainder supply the PeriodicProbe constant K. This gives a mathematical route
to a computable probe, but it is NOT formalized as a computability theorem.
It does not make the normalization transformation effectively computable: that
transformation uses maximal credits over all finite continuations.

`periodic_cycle.py` implements the finite cycle calculation using exact rational
arithmetic and verifies potential inequalities and the returned cycle mean.
On the three-key counterexample period it returns total cost 19 per eight
requests. It also finds means 3 and 5/2 for two four-key periods. These tests
support the construction; they are not a uniform competitive theorem or a
Lean-checked proof of the Python implementation.

## Remaining obstacles

A reset every n requests can be charged at constant average cost, but the phase
counter, within-block decisions, and choice of a useful private starting state
remain memory. The checked normalization avoids those problems only after
assuming offline competitiveness. Our equivalence now shows that a general
resolution of the constant-factor state-elimination question resolves tree-only
dynamic optimality in this rotation model. Neither a positive construction nor
an unbounded-in-n lower bound has been found.

## A finite-memory-per-size probe may suffice (not Lean formalized)

The existing probe learns every ultimately periodic word and stores unbounded
history. To test a fixed size n, the product graph has at most S=Catalan(n)^2
vertices. Any reachable positive cycle has a witness with a simple reaching
path and a positive simple cycle; both lengths are bounded by S. Therefore it
should suffice to learn the finite collection of candidate words with preperiod
and period lengths at most S, rather than all ultimately periodic words.

For each n, a learner can store the subset of still-consistent candidates and
a finite phase counter: count up to the maximum preperiod, then use a common
multiple of the finitely many period and serving-cycle lengths. Once a candidate
is rejected it stays rejected. On a represented witness, one correct candidate
survives forever and selection stabilizes. If all are rejected, use a legal
fallback. The resulting state space is finite for each n, although enormous
and not bounded by a constant independent of n.

This suggests the hardness reduction survives a restriction to finite memory
whose bound may be an arbitrary function of n. It does not settle simulation
of algorithms with a fixed constant-size private state, nor give a small-memory
probe. The bounded simple-cycle witness and this finite-state implementation
have not been connected in Lean; the checked equivalence still uses the
unbounded-history probe.

The generic bounded-witness claim is now Lean checked in `BoundedCycles.lean`.
`bounded_lasso` gives a prefix of length strictly less than the finite state
cover and a positive period of length at most that cover. Instantiation with
the BST product graph and the finite-memory learner remain separate work; the
existing complete equivalence still uses the full periodic probe.
