# Conditional entropy

The cost of the optimal root-finger tree has a classical closed form. Up to constant factors it is the *entropy bound* $m + \sum_x q_x \log_2(m/q_x)$, where $q_x$ counts the requests for $x$ ([Chapter 12](bounds.html)). A lazy finger profits from a different kind of regularity: a request is cheap when it is close, in the tree, to the *previous* request. So the natural candidate for a closed form of the optimal lazy-finger cost is the **conditional entropy** of each request given its predecessor, the information content of the transitions.

Bose, Douïeb, Iacono and Langerman show that this candidate fails (Lemma 7 of their paper). Some sequences have conditional entropy zero, since each key is always followed by the same key, and still cost $\Omega(\log n)$ per request with a lazy finger in any tree. The library proves a stronger form: the sequence costs that much in *every* dynamic BST. The proof is Wilber's interleave bound ([Chapter 13](wilber.html)) applied to a repeated bit-reversal sequence. The paper therefore characterizes the optimal lazy finger differently, by the weighted benchmark of [Chapter 14](lazy-finger.html).

```headline entropy-obstruction
title: No BST, and in particular no lazy-finger tree, is bounded by the conditional entropy
source: Bose, Douïeb, Iacono and Langerman, *The power and limitations of static binary search trees with lazy finger* (2014)
key: yes
theorems: ConditionalEntropy.Results.obstruction LazyFinger.Dynamic.Results.optimal

For a sequence $X = x_1, \dots, x_m$ on $n$ keys and a predecessor $x_0 = p$, let $H$ be the empirical conditional entropy of $x_j$ given $x_{j-1}$, in bits, and let the conditional benchmark be $m(1 + H)$, one unit per request plus the information of the transitions.

**Lemma 7, for dynamic BSTs.** For every constant $C$ and every startup allowance $a : \mathbb N \to \mathbb N$ there are $n \ge 1$, a key $p < n$ and a sequence $X$ of $m \ge n$ valid requests such that $H = 0$, also when only the transitions inside $X$ are counted, so that $m(1 + H) = m$, and such that every legal pointer-machine execution serving $X$, from any initial tree on $n$ keys, costs more than

$$C \cdot m(1 + H) + a(n).$$

**For lazy finger.** Theorem 6 ([Chapter 15](lazy-finger-hierarchy.html)) gives an execution of cost at most $16n + 464\,\mathrm{LF}^*_n(X)$. Applying the lemma with $464\,C$ and $464\,a(n) + 16n$ then gives $\mathrm{LF}^*_n(X) > C \cdot m(1+H) + a(n)$. So no bound of the form $\mathrm{LF}^* \le C\,m(1 + H) + a(n)$ holds. This two-line combination is arithmetic on the two listed theorems; the library does not state it as a separate theorem.
```

The definitions are in `Bounds/ConditionalEntropy/Definitions/Abstract.lean` and `Bounds/Interleave/BitReversal/Definitions/Abstract.lean`, and the theorems in the `Abstract.lean` files next to them. [Section 16.1](#empirical-conditional-information) defines the conditional information and explains the normalization $m(1 + H)$. [Section 16.2](#deterministic-sequences) shows that deterministic and periodic sequences have zero information. [Section 16.3](#the-bit-reversal-sequence) builds the bit-reversal sequence and bounds its cost with Wilber's theorem. [Section 16.4](#the-obstruction) assembles the obstruction. [Section 16.5](#more-space-beats-the-obstruction) explains why the conditional-entropy bound is still achievable outside the BST model, with more space.

## Empirical conditional information

Everything is *empirical*: computed from the counts of the sequence itself, with no probabilistic source. The counts are the directed transition frequencies [[LazyFinger.frequency]] of [Chapter 14](lazy-finger.html): `frequency p xs a b` is the number of $j$ with $(x_{j-1}, x_j) = (a, b)$, where $x_0 = p$. There are exactly $m$ transitions, one into each request.

@decl ConditionalEntropy.rowTotal ConditionalEntropy.information

`rowTotal n f a` is $r_a = \sum_{b < n} f_{ab}$, the number of transitions leaving $a$. The information of a frequency matrix is

$$I(f) \;=\; \sum_{a < n} \sum_{b < n} f_{ab} \log_2 \frac{r_a}{f_{ab}}.$$

A zero entry contributes $0$, since Lean's `0 * _` is $0$, whatever the totalized value of the logarithm. Row by row, $\sum_b f_{ab} \log_2(r_a/f_{ab})$ is $r_a$ times the entropy of the empirical distribution of successors of $a$. So $I(f)/m$ is the conditional entropy $H(\text{next} \mid \text{current})$ of the empirical transition distribution. The row totals are the *outgoing* counts. Among $x_0, \dots, x_{m-1}$ every key appears as a predecessor exactly $r_a$ times, so the last request $x_m$, which has no successor, is not counted. The docstring calls this the endpoint convention.

@decl ConditionalEntropy.sequenceInformation ConditionalEntropy.adjacentInformation

There are two ways to treat the first request.

- `sequenceInformation n p xs` uses an explicit predecessor $p$ for $x_1$. It is not the root of any tree, just a key. This matches the lazy-finger benchmarks with a specified starting finger, and the multiple-tree structure of [Section 16.5](#more-space-beats-the-obstruction).
- `adjacentInformation n xs` uses only the $m - 1$ transitions inside the sequence. Empty and one-element sequences have no transitions, hence zero information.

The obstruction holds with both conventions.

@decl ConditionalEntropy.entropy ConditionalEntropy.cost

`entropy n p xs` is the average $H = I/m$. For $m = 0$, Lean's real division by zero returns $0$, so the empty sequence has entropy $0$. `cost n p xs` is the conditional benchmark $m + I$.

**Theorem (basic properties).** The information of every frequency matrix is nonnegative. The benchmark is at least $m$, and it equals $m(1 + H)$, also when $m = 0$.

@decl ConditionalEntropy.Results.nonnegative ConditionalEntropy.Results.request_charge ConditionalEntropy.Results.normalization

### The normalization $m(1 + H)$

The paper writes the conditional bound as $O(m(1 + H))$, and the library defines it as $m + I$, which is the same thing. The normalization is chosen for three reasons.

- **Empty sequences.** The average $H$ is undefined for $m = 0$. The total $m + I$ needs no division, and `normalization` shows that it agrees with $m(1 + H)$ under Lean's convention $I/0 = 0$, so nothing is lost by stating results with either form.
- **Deterministic transitions.** If every key is always followed by the same key, then $H = 0$, as [Section 16.2](#deterministic-sequences) shows. A bound $C \cdot mH$ would then claim that serving the sequence is free. Every model in this book charges at least one per request, so such a bound is false for trivial reasons, and its failure says nothing. With the unit per request, the benchmark is $m$, and the obstruction says something real: no constant per request suffices.
- **Capacity one.** The positive result of [Section 16.5](#more-space-beats-the-obstruction) trades space for time with a factor $\log n / \log c$, where $c$ is the capacity of each local tree. For $c = 1$ this divides by $\log_2 1 = 0$. The library uses $(1 + \log_2 n)/(1 + \log_2 c)$ instead, together with $m(1 + H)$, so every case is a finite and meaningful bound.

The information is also a sum over the actual transitions of the sequence. Each transition $a \to b$ is charged $\log_2(r_a / f_{ab})$, minus the logarithm of the empirical probability that $a$ is followed by $b$:

@decl ConditionalEntropy.transitionSum

**Theorem (information as a transition sum).** For a valid predecessor $p$ and valid requests, charging every transition $x_{j-1} \to x_j$ the amount $\log_2(r_{x_{j-1}} / f_{x_{j-1} x_j})$ and summing over $j$ gives exactly the information $I$.

@decl ConditionalEntropy.Results.transitions

This is the form a data structure can aim for: if request $x_j$ costs $O(1 + \log_2(r_a / f_{ab}))$ given its predecessor, the total is $O(m(1 + H))$. Nothing about independence or stationarity is assumed.

## Deterministic sequences

A sequence is deterministic if one successor function explains all its transitions:

@decl ConditionalEntropy.Follows

`Follows next p xs` says that $x_1 = \mathit{next}(p)$ and $x_{j+1} = \mathit{next}(x_j)$. The theorem below is stated directly on frequency matrices instead, which is more general: each row has at most one nonzero entry.

**Theorem (deterministic rows carry no information).** If $f_{ab} = 0$ whenever $b \ne \mathit{next}(a)$, then $I(f) = 0$.

@decl ConditionalEntropy.Results.deterministic

The row totals may differ arbitrarily: a key that occurs often and a key that occurs once both contribute $0$, since in each row the only nonzero term is $r_a \log_2(r_a / r_a)$. Unlike the entropy bound of [Chapter 12](bounds.html), conditional information ignores how often keys occur. It only measures how predictable each step is.

The sequences used below repeat a fixed period:

@decl ConditionalEntropy.repeatPeriod

`repeatPeriod period rounds` is `rounds` copies of `period`, concatenated. The transitions at the period boundaries are kept: the last key of one copy is followed by the first key of the next.

**Theorem (repeated periods).** Let the period consist of distinct keys. Then every repetition has zero adjacent-request information. With the last key of the period as the explicit predecessor, which is one choice of $p$ in the period for all repetition counts, the information is zero as well.

@decl ConditionalEntropy.Results.adjacent_cycle ConditionalEntropy.Results.cycle

Distinctness makes the successor of each key unique: in the cyclic order of the period, each key is followed by the same key every time, including across the boundary. The period need not contain every key of the universe; keys that never occur have empty rows.

## The bit-reversal sequence

[Chapter 13](wilber.html) introduced the bit-reversal permutation as Wilber's standard hard example: on a perfect reference tree, nearly every node alternates sides on nearly every request it sees, so the interleave bound is about $\log_2 n$ per request. The obstruction needs a version of this example with an exact recursive structure, so the library builds it on the *leaves* of a perfect tree.

@decl Wilber.BitReversal.reference Wilber.BitReversal.requests

- `reference h` is the perfect tree of height $h$: one node for $h = 0$, and two copies of `reference h` below a root for $h + 1$. It has $2^{h+1} - 1$ keys, $2^h$ of them leaves.
- `requests h` lists the $2^h$ leaves in bit-reversal order, as inorder ranks of the whole tree. For $h + 1$, every request $x$ of `requests h` is replaced by $x$, a leaf of the left copy, followed by $x + |\mathtt{reference}\ h| + 1$, the same leaf in the right copy.

For $h = 2$ the tree has keys $0, \dots, 6$ and the requests are $0, 4, 2, 6$: the leaves in the order of their reversed binary indices $00, 10, 01, 11$. The internal keys separate the leaves and are never requested. Consecutive requests always lie in different halves of the root, and inside each half the requests again alternate between its two halves, and so on down.

@decl Wilber.BitReversal.Results.size Wilber.BitReversal.Results.length Wilber.BitReversal.Results.valid Wilber.BitReversal.Results.distinct

These are the facts the obstruction needs: the size $2^{h+1} - 1$, the length $2^h$, validity, and **distinctness**, which makes the repeated sequence deterministic.

**Theorem (interleave of bit reversal).** On its own reference tree, the bit-reversal sequence has interleave quantity at least $\tfrac12 h \cdot 2^h$, that is, at least half an alternation per request at each of $h$ levels.

@decl Wilber.BitReversal.Results.lower

Here `interleave` is Wilber's quantity [[RotationBST.Wilber.interleave]] of [Chapter 13](wilber.html). The node at the root of each subtree of height $g \ge 1$ sees $2^g$ requests that alternate on every step, so $2^g - 1 \ge 2^{g-1}$ alternations. Summing over the $2^{h-g}$ subtrees of each height gives the bound.

The repeated sequence is then served by a single execution, which never resets its tree between periods. Wilber's bounds of [Chapter 13](wilber.html), $\mathrm{IB} \le 12\,c$ for a pointer-machine execution of cost $c$ ([[Wilber.Results.pointer_lower_bound]]) and $\mathrm{IB} \le 4r + 2m$ for a rotation execution with $r$ rotations ([[Wilber.Results.rotation_lower_bound]]), give lower bounds that are linear in the length.

**Theorem (every BST pays $\log n$ per request).** Let $X$ be `rounds` repetitions of `requests h`, of length $m = \mathit{rounds} \cdot 2^h$. Every pointer-machine execution serving $X$ from any tree with $2^{h+1} - 1$ keys has cost $k$ with $h\,m \le 24\,k$. Every rotation execution with $r$ rotations has $h\,m \le 8r + 4m$.

@decl Wilber.BitReversal.Results.pointer Wilber.BitReversal.Results.rotations

Since $h = \log_2(n + 1) - 1$, this is $\Omega(\log n)$ per request. The initial tree is arbitrary; only its size is fixed. The factor $24 = 2 \cdot 12$ combines the factor 2 of the interleave count with the factor 12 of Wilber's pointer bound.

## The obstruction

The repeated bit-reversal sequence is the witness. It has a distinct period, so its conditional information is zero, and every BST pays $\Omega(\log n)$ per request on it.

**Theorem (bit-reversal obstruction).** For every height $h$ there is a predecessor $p$ in the universe of `reference h` such that, for every number of rounds, the repeated bit-reversal sequence has zero conditional information from $p$, and every pointer-machine execution of it costs $k \ge h\,m/24$.

@decl ConditionalEntropy.Results.bit_reversal

To defeat a given constant $C$ and allowance $a$, take $h = 24C + 24$, so that $k \ge (C + 1)\,m$, and enough rounds that $m > a(n)$. Concretely, the proof takes $24\,a(n) + 2$ rounds, which also gives $m \ge n$.

**Theorem (Lemma 7, normalized).** For every $C$ and every allowance $a$ there are $n \ge 1$, $p < n$ and a sequence $X$ of $m \ge n$ valid requests whose conditional entropy from $p$ is $0$, whose adjacent-request information is $0$, and whose conditional benchmark is exactly $m$, such that every legal pointer-machine execution of $X$ from every initial tree on $n$ keys costs more than $C\,m(1 + H) + a(n)$.

@decl ConditionalEntropy.Results.obstruction

::: check
- **All executions.** The lower bound quantifies over every [[RotationBST.Pointer.Execution]], including offline ones that know the whole sequence, and over every initial tree of the right size. So it bounds the offline optimum, not just one algorithm.
- **Both conventions.** The witness has zero information with the explicit predecessor `p` *and* with adjacent requests only, so the result does not depend on how the first request is treated.
- **No escape through startup.** The allowance `a` may be any function of $n$, chosen before the sequence. The condition $n \le m$ rules out the degenerate escape of sequences shorter than the universe.
- **Lazy finger.** The statement is about dynamic BSTs. The lazy-finger form follows from [[LazyFinger.Dynamic.Results.optimal]], as explained in the headline box, but it is not a separate Lean theorem.
:::

## More space beats the obstruction

The obstruction is a statement about binary search trees. It does not say that $O(m(1 + H))$ is out of reach for every pointer structure. Theorem 9 of the same paper achieves it with a structure of *multiple trees*. For each key $a$ there is a small local search tree on the $c$ most frequent successors of $a$, shaped according to their transition frequencies, together with one shared balanced fallback tree on all keys. A search starts from the local tree of the previous request. [Chapter 30](multiple-trees.html) formalizes this in the linked-search model of [Chapter 11](linked-search.html).

With local trees of capacity $1 \le c \le n$, the structure uses at most $10\,n\,c$ words and serves $X$ from the predecessor $p$ at cost at most

$$6\, m(1 + H) \cdot \frac{1 + \log_2 n}{1 + \log_2 c}$$

([[MultipleTrees.Results.sequence]]). With $c$ about $n^{\varepsilon}$, this is $O(m(1 + H)/\varepsilon)$ with $O(n^{1 + \varepsilon})$ words ([[MultipleTrees.Results.polynomial_space]]). The two results fit together.

- The multiple-tree structure is not a BST. It follows stored links between different trees, so neither Wilber's bound nor the obstruction applies to it.
- It is built from the transition matrix of the sequence it serves, so it is an offline, static structure. Preprocessing time is not part of the bound.
- Its cost uses the same benchmark [[ConditionalEntropy.cost]] as the obstruction, including the unit per request and the explicit predecessor $p$.
