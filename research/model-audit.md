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
probe. The bounded simple-cycle witness is now connected to request words in Lean;
the finite-state implementation is not yet formalized. The checked equivalence
still uses the unbounded-history probe.

The generic bounded-witness claim is now Lean checked in `BoundedCycles.lean`.
`bounded_lasso` gives a prefix of length strictly less than the finite state
cover and a positive period of length at most that cover. The BST instantiation is now checked in `BoundedBSTWitness.lean`: each edge
corresponds to exactly one request. `bounded_tests_suffice` proves that these
short paired loops suffice for offline competitiveness, and
`bounded_probe_domination` reduces the probe requirement to this finite family
of words. Constructing the finite-memory learner remains separate work.


### Explicit finite-memory construction on paper (not Lean checked)

Fix n and let S be the length of `pairCover n`. For n>0 enumerate all pairs
(pre, period) over keys 0,...,n-1 with |pre|<S and 1<=|period|<=S. Keep a bitset
of candidates not yet contradicted by an observed request. A finite clock
(count exactly until S, then modulo the least common multiple of 1,...,S)
suffices to predict every candidate's next request. Discard contradicted
candidates and use the first remaining candidate; if none remain, use
move-to-root forever. The empty-period case needs no learning: it places only
a constant-size prefix requirement on the probe bound.

For every candidate's periodic tail, precompute a minimum-mean serving cycle
in the finite (phase, tree) graph described above. Store the active candidate
and an index into that cycle. On changing candidates or entering a periodic
tail, reset to the appropriate pre-access cycle tree, then serve the current
request. The reset occurs before serving, so the access still ends with the
requested root. Candidate selection includes the current request, so executing
its predicted access is legal even when later predictions fail. During the
finite preperiod, ordinary move-to-root suffices. A phase-compatible entry
exists because a serving cycle advances phase by one on every edge and has
length divisible by the request period.

On a represented ultimately periodic input, a truthful candidate survives.
Only finitely many candidates can be discarded; hence the selected candidate
stabilizes and predicts the entire remaining tail correctly. Its serving cycle
then repeats without resets. Compare it to any periodic offline schedule for
the actual input: repeating a common multiple of the request and serving
periods embeds the offline schedule in the selected candidate's phase graph.
The minimum mean is no greater than this schedule's average. Initial accesses,
candidate changes, and incomplete final cycle contribute a fixed additive K.
Thus the construction has the bounded-probe property needed by the checked
`bounded_probe_domination` theorem.

This gives a detailed mathematical argument that per-size finite private
memory should suffice for the hardness reduction. The unformalized ingredient
is the finite minimum-mean-cycle construction and its connection to this finite
learner, not a uniform-in-n simulation bound. The number of private states
may grow enormously with n; nothing here addresses a fixed Fin K private
state space independent of n. For n=0 only the empty valid input exists.
