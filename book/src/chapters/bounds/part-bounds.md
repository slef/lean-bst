# Bounds

Part I fixed what a BST execution is and what it costs. Part II asks how much a request sequence *must* or *may* cost, independently of any algorithm. Two kinds of statements live here. **Upper-bound benchmarks** are explicit functions of the sequence, such as the entropy of its access frequencies, that a good algorithm should match. **Lower bounds** hold for every execution, hence for the offline optimum. Algorithms enter only in [Part III](part-classical.html) and [Part IV](part-algorithms.html), where each is measured against both.

- [Chapter 12](bounds.html) defines the classical benchmarks of the splay-tree literature: the working set, static optimality, the static and dynamic finger sums, the unified charge, and comparison with a fixed tree. It proves the implications between them, and the entropy bounds that make "static optimality" mean what its name says.
- [Chapter 13](lazy-finger.html) studies a static tree searched with a *lazy finger*, where each search starts where the previous one ended, and proves that the best such tree costs, up to constant factors, the best weighted dynamic finger bound.
- [Chapter 14](lazy-finger-hierarchy.html) places the lazy finger between static trees searched from the root and dynamic BSTs, with unbounded gaps on both sides.
- [Chapter 15](wilber.html) proves Wilber's interleave lower bound, which holds for every execution in the rotation, pointer and geometric models. It is the tool behind the $O(\log\log n)$-competitive Tango trees.
- [Chapter 16](conditional-entropy.html) shows that the conditional entropy of the requests is not a benchmark any BST can meet, through Wilber's bound on a bit-reversal sequence.

## A map of the bounds

Two figures collect the relations between them: the first up to constant factors, with the algorithms that meet each bound, and the second with the constants the library proves. Each benchmark is a function of the request sequence $X$ of length $m$ on $n$ keys:

- $\mathrm{IB}$, Wilber's interleave quantity for a reference tree, [[RotationBST.Wilber.interleave]] ([Chapter 13](wilber.html));
- $\mathrm{OPT}$, the least cost of an [[RotationBST.Execution]] serving $X$, the offline optimum of [Chapter 5](online.html) (the pointer-machine optimum is the same up to constant factors, by [Chapter 9](equivalence.html));
- $m(1+H)$, the conditional-entropy benchmark [[ConditionalEntropy.cost]] ([Chapter 16](conditional-entropy.html));
- $\mathrm{LF}^*$, the cost of the best static tree searched with a lazy finger, [[LazyFinger.optimalCost]] ([Chapter 14](lazy-finger.html));
- $\mathrm{WDF}^*$, the best weighted dynamic finger bound, [[WeightedFinger.optimalCostFrom]] ([Chapter 14](lazy-finger.html));
- $\mathrm{RF}^*$, the cost of the best static tree searched from the root, the minimum of [[StaticTree.cost]] over trees;
- $\mathrm{SO}$, the entropy bound [[Bounds.staticCost]]; $\mathrm{WS}$, the working-set sum [[workingSetSum]]; $\mathrm{SF}$, the static finger sum [[Bounds.fingerCost]]; and $\mathrm{DF}$, the dynamic finger sum [[Bounds.dynamicFingerCostFrom]];
- $m(1 + \log n)$, what a balanced tree pays, about $\log_2 n$ per request whatever the sequence. It is the baseline of the classical trees of [Part III](part-classical.html), and has no Lean definition yet.

### Up to constants

The first figure ignores constant factors and startup terms. An arrow $A \to B$ means that a cost bound $O(A)$ implies a cost bound $O(B)$. For most arrows this is an inequality $A \le c\,B + O(n)$ between the benchmarks themselves; the arrows out of $\mathrm{WS}$ and $\mathrm{SO}$ are instead implications between properties of algorithms, with the startup allowance $D\,n(1 + \lfloor\log_2 n\rfloor)$ of [Chapter 12](bounds.html#conventions). "Strict" marks an arrow whose converse fails: the gap is unbounded on some family of sequences. Bounds within constant factors of each other share a box: $\mathrm{LF}^* = \mathrm{WDF}^*$ ([Chapter 14](lazy-finger.html)) and $\mathrm{RF}^* = \mathrm{SO}$ (the entropy bounds of [Section 12.3](bounds.html#static-optimality)).

The bubbles are algorithms. An arrow from an algorithm to a bound means that the algorithm's cost is within that ratio of the bound, and so of every bound below it; the ratio is written when it is not constant. Dashed grey arrows are results that are not formalized yet. They are listed in the library's [roadmap](https://github.com/slef/lean-bst/blob/main/ROADMAP.md), for a later round of proofs.

@viz boundsmap {"map": "bigo", "roadmap": "https://github.com/slef/lean-bst/blob/main/ROADMAP.md"}

| Algorithm | Meets | What is proved | Lean |
|---|---|---|---|
| Tango trees ([Chapter 28](tango.html)) | $\mathrm{OPT}$, ratio $O(\log\log n)$ | An online BST algorithm whose total cost is at most $(56\log_2(\lfloor\log_2 n\rfloor + 1) + 16)$ times that of any offline execution from the same tree, plus $O(n \log\log n)$. | [[Tango.Algorithm.Results.exists_competitive\|exists_competitive]] |
| Splay trees ([Chapter 19](analysis.html)) | $\mathrm{WS}$ | At most $10\,\mathrm{WS} + 6n(1 + \lfloor\log_2 n\rfloor)$ rotations, from every initial tree. | [[Splay.Results.workingSet\|Splay.workingSet]] |
| Splay trees | $\mathrm{OPT}$, ratio $O(\log\log n \cdot \log^2\log\log n)$ | Proved by @chmel2026. | not formalized yet |
| GreedyASS ([Chapter 23](greedy-finger.html)) | $\mathrm{LF}^* = \mathrm{WDF}^*$ | Some online BST algorithm costs at most $722280\,\mathrm{LF}^* + 96303\,n$, and at most $2889120\,\mathrm{WDF}^* + 96303\,n$ from every start key. | [[Geometric.GreedyASS.Performance.Results.bst\|GreedyASS bst]] |
| Combined BST ([Chapter 38](combined-finger.html)) | $\mathrm{OPT}$, ratio $O(\log\log n)$, and $\mathrm{WDF}^* = \mathrm{LF}^*$ | One causal program, chosen before the requests: GreedyASS and Tango with linear startup, combined by ComboBST and deamortized. Its cost is $O(n + \min(\mathrm{WDF}^*, (m + R)(1 + \log_2(1 + \lfloor\log_2 n\rfloor))))$ for every offline execution with $R$ rotations, and each request costs less than $251 + 195\log_2 n$. | [[Geometric.GreedyASS.Combination.Deamortized.Results.combined\|combined]] |
| Optimal lazy-finger tree ([Chapter 29](optimal-lazy-finger.html)) | $\mathrm{LF}^*$ | A dynamic program builds a static tree whose lazy-finger cost is exactly $\mathrm{LF}^*$. It reads the whole sequence first. | [[OptimalLazyFinger.Work.Results.root_start\|root_start]] |
| Entropy tree ([Chapter 18](static-trees.html#entropy-trees)) | $\mathrm{RF}^* = \mathrm{SO}$ | A static tree with the weighted median at every root costs at most $\mathrm{SO}$. It is built from the access frequencies. | [[StaticTree.Results.entropy_upper_bound\|entropy_upper_bound]] |
| Optimal static tree ([Chapter 18](static-trees.html#optimal-static-trees)) | $\mathrm{RF}^*$ | Knuth's dynamic program computes a static tree of cost exactly $\mathrm{RF}^*$, in $O(n^2)$ time. | not formalized yet |
| Balanced trees ([Part III](part-classical.html)) | $m(1 + \log n)$ | The perfect static tree, and AVL, red-black, WAVL, BB[α] and scapegoat trees under updates, have height $O(\log n)$. | not formalized yet |
| Random trees ([Chapter 21](random-trees.html)) | $m(1 + \log n)$, in expectation | Every key of a random BST or a treap has expected depth at most $2 \ln n$. | not formalized yet |
| Multiple trees ([Chapter 30](multiple-trees.html)), not a BST | $m(1+H)$, ratio $O(\log n / \log c)$ | With $c$ successors per key and $10nc$ words, cost at most $6\,m(1+H)\,(1 + \log_2 n)/(1 + \log_2 c)$, in the linked-search model. | [[MultipleTrees.Results.sequence\|MultipleTrees.sequence]] |

### With constants

The second figure separates the shared boxes and writes on each arrow the bound that the library proves. Bounds that share a box in the first figure are on one row here, with an arrow each way. The table below lists every arrow with its theorems.

@viz boundsmap {"map": "detail", "roadmap": "https://github.com/slef/lean-bst/blob/main/ROADMAP.md"}

| Relation | What is proved | Lean |
|---|---|---|
| $\mathrm{IB} \to \mathrm{OPT}$ | Every execution with $r$ rotations has $\mathrm{IB} \le 4r + 2m$, for every reference tree. | [[Wilber.Results.rotation_lower_bound\|rotation_lower_bound]] |
| $\mathrm{OPT} \to \mathrm{LF}^*$, strict | From every initial tree, some pointer execution costs at most $464\,\mathrm{LF}^* + 16n$. Some families have $\mathrm{OPT} = o(\mathrm{LF}^*)$. | [[LazyFinger.Dynamic.Results.optimal\|Dynamic.optimal]], [[LazyFinger.Separation.Results.family\|Separation.family]] |
| $\mathrm{OPT} \to \mathrm{WS}$ | From every initial tree, splaying is a pointer execution of cost at most $31\,\mathrm{WS} + 18n(1 + \lfloor\log_2 n\rfloor)$. | [[Splay.Results.pointer_workingSet\|pointer_workingSet]] |
| $\mathrm{OPT} \not\to m(1+H)$ | No execution bound $C\,m(1+H) + a(n)$ holds, whatever $C$ and $a$. | [[ConditionalEntropy.Results.obstruction\|obstruction]] |
| $\mathrm{LF}^* \leftrightarrow \mathrm{WDF}^*$ | $\mathrm{LF}^* + n \le 4(\mathrm{WDF}^* + n)$ and $\mathrm{WDF}^* + n \le 4(\mathrm{LF}^* + n)$. | [[LazyFinger.Results.characterization\|characterization]] |
| $\mathrm{LF}^* \to \mathrm{RF}^*$, strict | $\mathrm{LF}^* \le 2\,\mathrm{RF}_t$ for every tree $t$. Some families have $\mathrm{LF}^* = o(\mathrm{RF}^*)$. | [[LazyFinger.Results.optimal_root_finger\|optimal_root_finger]], [[LazyFinger.Sequential.Results.family\|Sequential.family]] |
| $\mathrm{LF}^* \to \mathrm{DF}$ | $\mathrm{LF}^* \le n + 4\,\mathrm{DF}$, from any start key. | [[LazyFinger.Consequences.Results.dynamic_finger\|dynamic_finger]] |
| $\mathrm{SO} \leftrightarrow \mathrm{RF}^*$ | $\mathrm{SO} \le 3\,\mathrm{RF}_t$ for every tree $t$, and $\mathrm{RF}_t \le \mathrm{SO}$ for some $t$. | [[StaticTree.Results.entropy_lower_bound\|entropy_lower_bound]], [[StaticTree.Results.entropy_upper_bound\|entropy_upper_bound]] |
| $\mathrm{WS} \to \mathrm{SO}$ | The working-set property implies static optimality. | [[Bounds.workingSet_implies_staticOptimality\|workingSet_implies_staticOptimality]] |
| $\mathrm{SO} \to \mathrm{SF}$ | Static optimality implies the static finger property, for every finger. | [[Bounds.staticOptimality_implies_staticFinger\|staticOptimality_implies_staticFinger]] |
| $\mathrm{DF} \to \mathrm{SF}$ | $\mathrm{DF} \le 2\,\mathrm{SF}_f + \log_2(\lvert p - f\rvert + 1)$ for every finger $f$ and start key $p$: a step from $x$ to $y$ costs at most the steps from $x$ to $f$ and from $f$ to $y$. | not formalized yet |

Some composite relations are also stated directly, as inequalities between benchmarks: $\mathrm{LF}^* \le 2\,\mathrm{SO}$ and $\mathrm{LF}^* \le 6\,\mathrm{SF}$ ([[LazyFinger.Consequences.Results.static_optimality]], [[LazyFinger.Consequences.Results.static_finger]]), and a working-set algorithm competes with every fixed tree ([[StaticTree.Results.workingSet_competes]]).

Two classical facts are left off both maps. The working-set and dynamic finger bounds are incomparable, each beating the other by an unbounded factor on some family of sequences, but the library has no such families. And the unified charge of [Section 12.5](bounds.html#the-unified-charge) has no formalized relations to the other benchmarks, beyond the splay theorem that uses it.
