# Three keys obstruct purely additive state elimination

This concerns the stronger bound cost_B <= cost_A + f(n), with coefficient one.
It does not refute cost_B <= C cost_A + f(n) for a constant C > 1.

## Five tree shapes

Write a tree as root(left,right), omitting empty children. The five shapes on
keys 0,1,2 are:

| Name | Tree | Root |
| --- | --- | --- |
| a | 0(-,1(-,2)) | 0 |
| b | 0(-,2(1,-)) | 0 |
| c | 1(0,2) | 1 |
| d | 2(0(-,1),-) | 2 |
| e | 2(1(0,-),-) | 2 |

The rotation graph is the pentagon a-b-d-e-c-a. Its diameter is two.
Every request for 1 must end at c. In particular, serving 1 erases all persistent
memory of a tree-only algorithm on this universe.

Consider the two blocks U=021 and V=02021, both starting and ending at c.
U can be served in four rotations via c,a,e,c. V can be served in seven
rotations via c,b,d,b,d,c.

## Lower bound for a single tree-only policy

Fix any deterministic tree-only policy B. Replace each transition by a shortest
rotation path to its chosen endpoint. This can only decrease cost and cannot
change future endpoint decisions. Let u and v be its rotation costs on U and V.

If B does not serve U in four rotations, then u >= 5 and v >= 7, giving
u+v >= 12. The lower bound v >= 7 is a finite shortest-path calculation.

If B serves U in four rotations, it must choose c -> a on 0 and a -> e on 2.
On V, these same choices force the first two transitions c,a,e. The next 0
ends at either a or b. Ending at a forces the remaining path a,e,c; the
total is 1+2+2+2+1=8. Ending at b then going to d gives
1+2+2+1+2=8; going from b to e gives 1+2+2+2+1=8.
Thus v >= 8, again u+v >= 12.

An exhaustive calculation gives possible pairs (u,v):
(5,9), (5,7), (5,10), (4,8), (5,8).
The inequality u+v >= 12 is kernel checked in ThreeKeySeparation.lean for
every legal endpoint policy. That file also proves all size-three trees are
among these five shapes and that the distance table lower-bounds every actual
rotation trace, including traces with arbitrary extra rotations.

## One fixed online stateful algorithm

Define A with a clock modulo 8, initially zero. Its planned request sequence is
UV=02102021, repeated. At the eight phases it follows the endpoint schedule
a,e,c,b,d,b,d,c. It checks that both the current tree and current request match
the planned transition. On a match it uses the fixed rotation path above; on a
mismatch it serves the request using move-to-root and may reset the clock.
This is a valid deterministic ONLINE algorithm on every input: its choice
depends only on its clock, the current tree, and the current request.
It does not inspect future requests. On other tree sizes use move-to-root.

Starting at c, on X_m=(UV)^m it uses exactly 11m rotations and 8m requests,
so cost_A(c,X_m)=19m. Every tree-only B is back at c after every U and every V,
and therefore cost_B(c,X_m)>=20m by the preceding inequality.

Consequently, for every proposed finite f(3), choose m>f(3). Then
cost_B(c,X_m)>cost_A(c,X_m)+f(3). The same A and the same family X_m work
against every B. This rules out ANY sequence-length-independent additive
allowance at coefficient one. It also gives a required multiplicative ratio
of at least 20/19 for this particular A. The scaled rational statement is
now also Lean checked as `no_ratio_below_20_19`.

## Verification status

The complete theorem is now checked in Lean without sorry or extra axioms:
`ThreeKey.no_purely_additive_simulation`. This includes the modulo-eight online
algorithm and fallback correctness, every concrete rotation trace, classification
of all size-three trees, lower bounds for arbitrary rotation traces and arbitrary
tree-only algorithms, repeated-word execution induction, and the quantified
counterexample for every function f : Nat → Nat. An axiom guard lists only
Lean's standard propext, Classical.choice, and Quot.sound.

This example also shows why a repeated-tree argument cannot give exact additive
simulation: at c, A retains which of two phases it is in; B cannot. A constant
factor may still absorb this difference, so the main relaxed question remains.


## One bit suffices (Lean checked)

`OneBitSeparation.lean` replaces the eight-state clock by `Fin 2`. On the
repeated word, the bit flips after every access. The planned transitions are:

| Bit | Tree | Request | New tree | Rotations |
| --- | --- | --- | --- | --- |
| 0 | c | 0 | a | 1 |
| 1 | a | 2 | e | 2 |
| 0 | e | 1 | c | 1 |
| 1 | c | 0 | b | 2 |
| 0 | b | 2 | d | 1 |
| 1 | d | 0 | b | 1 |
| 1 | d | 1 | c | 2 |

All other inputs use a correct move-to-root fallback and reset the bit.
The tree/request pair distinguishes all required steps except the two visits
to (c,0); those are distinguished by the bit. Both blocks have odd length,
so their starting bits differ. The full eight-request period returns to
(tree c, bit0) with11 rotations. Lean checks correctness on every valid input,
exact repeated-period cost19m, failure of every purely additive simulation,
and failure of every rational coefficient below20/19.

This strengthens the negative result to a single bit independent of n. It
still does not refute simulation at a larger constant factor, even for this
particular algorithm. The earlier eight-state comparator remains available.


An additional exhaustive experiment (`python3 research/one_bit_simulation.py`)
finds the optimal tree-only simulation coefficient for this particular
three-key one-bit comparator is12/11, with a certificate
11*cost_B<=12*cost_A+6. All1024 shortest-endpoint policies are enumerated;
reachable product-cycle checks use exact rational arithmetic. This is
experimental, not a Lean lower-bound theorem. The checked uniform lower
bound remains20/19; deriving a small human-readable witness for12/11 is a
possible next step. It has no uniform-in-n consequence.
