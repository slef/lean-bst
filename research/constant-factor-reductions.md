# Constant-factor reductions: verified equivalence and research history

## Current status: equivalence fully Lean checked

`PeriodicProbe.lean` completes the periodic online algorithm and proves
`state_elimination_iff_universal` and `arbitrary_iff_linear` without a remaining
probe hypothesis. The three existence statements in the combined implication
below are now proved equivalent in the repository's model. None is proved true.
The coefficient-one version is separately disproved in ThreeKeySeparation.

The initial minimum-mean-cycle construction below is historical mathematical
motivation. The checked proof uses the later compactness construction instead.
Earlier checkpoint notes saying an ingredient remains unformalized are superseded
by this status. The verified normalization constant is (2+6C)n, not the sharper
prose variant (2+4C)n. Algorithms are mathematical, possibly noncomputable rules,
with planning work uncharged. No pointer-model transfer or novelty claim is made.

## 1. An online probe for eventually periodic inputs

For each fixed n, enumerate all ultimately periodic infinite request words over
{0,...,n-1}. At each time choose the first enumerated word consistent with the
observed prefix. Every finite prefix has an ultimately periodic extension, so a
choice exists. On an actually ultimately periodic input, this hypothesis
stabilizes after finite time: the index of a correct hypothesis bounds the
indices considered, and each incorrect earlier hypothesis is eventually rejected.

A stateful online algorithm U can keep this hypothesis and a serving plan.
On a hypothesis change, discard the plan. For a stable predicted periodic tail,
form the finite graph whose vertices are (phase modulo period, tree shape), with
edge cost one plus the shortest rotation distance to a tree rooted at the current
request. Choose a minimum-mean cycle. Its length is a multiple of the period.
Use a reset at the start of an access to enter this cycle at the matching phase,
and follow it. Before the predicted tail starts, use move-to-root.

Every decision uses only observed history and a fixed enumeration; no future
input is queried. On mismatch, update the hypothesis and produce a fresh legal
access. Thus U is a single deterministic online algorithm defined on all finite
inputs and all n. Planning computation is uncharged in our model.

On any ultimately periodic input, U eventually repeats a minimum-mean serving
cycle. In particular, against ANY fixed legal eventually periodic serving
schedule E for that same input, cost_U on prefix plus m periods is at most
m*(E's per-period cost)+K, for a constant K depending on the input and n, not m.
Different cycle lengths cause only a bounded remainder. All phase-compatible
trees can be reached by a finite reset, so no cycle is inaccessible to U.

## 2. Why dominating this probe tests offline competitiveness

Suppose a tree-only B satisfies cost_B(T,X) <= C*cost_U(T,X)+f(n) for all inputs.
Fix n. B has finitely many physical states (tree shapes). Pair its tree with the
tree of an arbitrary offline execution. Each request yields an edge with weight
cost_B_step - C*cost_offline_step. It suffices to consider shortest rotations for
each offline endpoint. There are finitely many vertices and edges.

If a positive-weight cycle is reachable from a common initial tree, choose a
prefix reaching it and repeat its request word forever. B and the offline witness
return to their cycle states each period. U eventually costs no more per period
than this witness, up to a fixed transient constant. B's positive excess per
period then contradicts its assumed bound against U, since f(n) is fixed.

Hence there are no reachable positive cycles. Removing nonpositive cycles from
any path bounds its excess by the largest weight of a simple path. Maximizing
this finite bound over the finitely many initial trees gives g(n), independent
of input length. Therefore B is C-competitive against ALL offline executions,
with additive g(n).

This suggests that state elimination with arbitrary additive f(n), applied to
this one probe U, already entails a tree-only dynamically optimal algorithm with
some additive g(n). The converse is immediate: an offline-competitive B dominates
every online A. This is stronger than merely relating to the splay conjecture.
The construction and graph argument still need formal checking.

## 3. Upgrade an arbitrary additive allowance for a tree-only B to O(n)

This is a separate reduction for a B already competitive against offline OPT.
Fix n>0. Write c_B(s,X) for total cost from tree s and OPT(t,X) for minimum total
cost from t. Suppose for a fixed integer C and all s,X,

  c_B(s,X) <= C*OPT(s,X) + g(n).

Let R=2n, the proved reset bound. Define the nonnegative integer value

  V(s,t) = max_X [c_B(s,X) - C*OPT(t,X)],

where the empty word supplies zero. The maximum is finite and attained:
resetting before the first access gives OPT(s,X) <= OPT(t,X)+R, so the expression
is at most g(n)+C*R. This also gives the Lipschitz estimate

  V(s,t) <= V(s,u) + C*R.

Equivalently V is the maximum over finite paired executions of their excess.
For every legal offline step t --x,k--> t' and B step s --x,l--> s',

  (1+l) + V(s',t') <= C*(1+k) + V(s,t).

There exists a pair (s*,t*) with V(s*,t*)=0. Take a paired finite execution
attaining V from any starting pair. If its endpoint had positive V, concatenate
a positive-excess suffix, contradicting maximality. Therefore
V(s*,t) <= C*R for every t.

Let v(s)=min_t V(s,t), and H=R+C*R. Define a new TREE-ONLY rule B':

- If v(s)<=H, take B's ordinary action from s.
- If v(s)>H, reset s to s*, then take B's action from s* on the current request.

The condition depends only on n and the physical tree s. This is not a hidden
clock or auxiliary memory. Every reset is inside the next access, whose final
root is still the requested key. Existence definitions may be noncomputable;
the present Lean model allows arbitrary mathematical step functions.

Use the proof potential

  P(s,t) = V(s,t)                 if v(s)<=H,
           R+V(s*,t)             otherwise.

For every s,t, P(s,t)<=V(s,t): in the reset case V(s,t)>=v(s)>R+C*R,
whereas R+V(s*,t)<=R+C*R. For low states P(s,t)<=H+C*R=R+2*C*R by
Lipschitz continuity. For high states P(s,t)<=R+C*R. Thus P is uniformly
bounded above by R+2*C*R and is nonnegative.

An ordinary B' step obeys the V step inequality and P(next)<=V(next).
A reset step costs at most R plus the corresponding B step from s*, and its
potential is exactly R+V(s*,t), so it obeys the same C-amortized inequality.
Telescoping therefore gives

  cost_B'(T,X) <= C*OPT(T,X) + R+2*C*R
               = C*OPT(T,X) + (2+4C)*n.

For n=0 there are no valid nonempty inputs; use the trivial empty run.
The coefficient C is unchanged. This argument seems to show that allowing
arbitrary additive g(n) instead of O(n) does not weaken the existence question
for tree-only offline-competitive algorithms.

## Combined implication to audit

If all three constructions hold, the following existence statements are equivalent:
(1) every stateful A has a tree-only simulator with constant C_A and additive f_A(n);
(2) the same with additive O(n);
(3) a single tree-only algorithm is dynamically optimal against offline OPT,
    with constant coefficient and additive O(n).

The easy directions are (3)->(2)->(1). For (1)->(3), use the periodic probe and
positive-cycle argument, then the reset-potential normalization above. This is
a reduction, not a proof of any of these existence statements.

## Verified anchor-based variant

`AdditiveNormalization.normalize_additive` (in namespace RotationBST) is now
kernel checked. Rather than minimizing V(s,t) over t, it uses the fixed anchor
t* from a zero-credit pair and tests V(s,t*) <= R+2CR. In the low case,
V(s,t) <= R+3CR. In the high case, reverse variation gives V(s,t)>R+CR,
which pays for the reset potential R+V(s*,t). Thus the verified bound is
(2+6C)n. The potential handles n=0 directly. The stronger (2+4C)n constant
above remains a prose variant, unnecessary for the O(n) conclusion.

## Checked ingredients for the periodic reduction

`PeriodicLearning.lean` verifies stabilization of the least consistent index
under a permanently correct candidate, and that the stable candidate matches
all finite observed prefixes. `PeriodicComparison.lean` defines the precise
`PeriodicProbe` cost property and proves that domination of such a probe rules
out every reachable positive product loop. It also proves repetition formulas
for legal executions and tree-only runs. Neither construction of the probe nor
the finite-graph cycle-erasure implication has yet been formalized.

The generic finite-graph implication is now checked in `FiniteWeightedPaths.lean`:
nonpositive loops can be erased and all path weights are bounded by the finite
vertex count times a nonnegative upper bound on edge weight. `FiniteTrees.lean`
provides finite covers and one-step cost bounds for BSTs. The bridge instantiating
this graph with reachable BST/offline pairs remains to be formalized.

## Conditional reduction now fully checked

`ProbeReduction.lean` instantiates the graph argument with reachable pairs of
BST endpoints, proving the exact cost-difference identity in both directions.
`probe_domination_offline` and `probe_domination_linear` finish the reduction
assuming an explicit `PeriodicProbe` algorithm. The two equivalence theorems
state this hypothesis explicitly. Consequently the only missing ingredient in
this proposed equivalence is construction of a stateful periodic probe with
its full cost guarantee. This is still a reduction between existence questions,
not a proof of a dynamically optimal algorithm or of state elimination.

## Alternative probe construction under development

Minimum-mean cycle machinery can be replaced by compactness. An optimal plan
for any finite horizon has every prefix within 2n rotations of its independent
offline optimum: replacing the prefix and resetting before the suffix proves
this. Every action also costs at most 2n. A finitely branching tree of such
good finite plans therefore has an infinite branch for a known infinite input.
The branch is clairvoyant, which is permitted only as a plan for a predicted
word, not as the online algorithm itself.

Preselect a plan for each periodic hypothesis. When the least-consistent learner
changes hypothesis, reset to the selected plan's tree at the current absolute
time and perform its current action. Once the prediction stabilizes correctly,
the actual tree follows the plan forever. Finite earlier cost is absorbed in K.
The plan's uniform prefix guarantee then proves the desired PeriodicProbe bound.
`FiniteBranching.lean` checks the general infinite-branch lemma, and
`OptimalPrefixes.lean` checks the finite-optimal-plan estimates. Instantiating
the finite-branching tree and implementing the concrete learner remain work.

## Clairvoyant plan construction now checked

`InfinitePlan.lean` constructs a plan for every fixed valid infinite request
word. Its actions cost at most 2n rotations and every prefix costs at most the
cost of any offline execution from an equal-size initial tree plus 4n rotations.
It selects, among finitely many possible next actions, one that can still be
completed optimally at arbitrarily distant horizons. The whole word is an input
to this construction. It is therefore a clairvoyant plan, not an online algorithm.
The remaining probe work is the concrete periodic learner and its online wrapper,
including the eventual cost comparison after the learner stops changing plans.

## Concrete history-only learner now checked

`FiniteCoverLearning.lean` proves stabilization for least selection across
finite candidate lists. `PeriodicCandidates.lean` supplies the finite lists of
prefix/period words, validity and coverage, and a selection depending only on
observed history. `selected_eventually_correct` proves that on an input matching
a valid periodic candidate, selection eventually stays with a candidate whose
forecast matches the entire input. The actual BST wrapper and its cumulative
cost proof are still needed to finish PeriodicProbe existence.

## Online wrapper now checked

`ForecastAlgorithm.lean` defines a legal stateful online BST algorithm using the
observed history. It resets to the selected forecast's plan only when its tree
is not already synchronized. The first action aligns its endpoint with the
plan; a synchronized action pays precisely the plan's rotation count. The
cumulative-cost comparison and the final PeriodicProbe theorem remain unproved.

## Final probe bridge checked

`ForecastTracking.eventual_offline_bound` proves that on any valid represented
ultimately periodic input, the explicit online algorithm is within a finite
additive constant of EVERY offline execution on EVERY prefix. `PeriodicProbe.lean`
proves the segment/repetition identity, applies that bound to a repeated legal
schedule, and supplies `algorithm_is_probe`. The earlier conditional equivalence
then becomes unconditional. Empty repeated words are handled directly. Every
component is Lean checked with only the standard logical axioms.
