# Constant-factor reductions: candidate proof, not yet Lean checked

## Status

The arguments here are mathematical proof attempts for two reductions. They do
NOT prove the existence of a constant-factor tree-only algorithm. The additive-normalization reduction is now Lean checked, with bound
`(2+6C)n` from a simpler anchor-based threshold. The periodic-probe reduction
remains unformalized; audit its quantifiers and construction before promoting
it to a checked theorem.

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
