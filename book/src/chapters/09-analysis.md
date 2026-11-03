# The amortized analysis

Sleator and Tarjan analyse splaying with a potential function. Each item $i$ gets a fixed positive weight $w(i)$. The *size* $s(x)$ of a node is the total weight of its subtree, its *rank* is $r(x) = \log_2 s(x)$, and the potential of a tree is the sum of the ranks of its nodes. The Access Lemma bounds the amortized cost of one splay. Their Theorems 1–5 then follow by choosing the weights. This chapter shows the formal versions of the potential, the lemma and the five theorems. The bounds themselves (working set, entropy, finger) are defined in [Chapter 7](bounds.html).

## Weights and potential

@decl RotationBST.Splay.mass RotationBST.Splay.potential

The weights are a function `w : Nat → ℝ` on ranks. Because a subtree does not know its own keys, both functions carry the offset `lo` of the subtree's smallest key and update it exactly as [[RotationBST.Tree.labelFrom|labelFrom]] does ([Chapter 1](shapes.html#implicit-keys)). The root of `node l r` is rank `lo + l.size`, so `mass` adds `w (lo + l.size)` between the masses of the two subtrees. `mass w t 0` is the total weight $W$ of the tree. `mass` is the paper's $s$, and `potential` is $\Phi = \sum_x \log_2 s(x)$, summed over nonempty subtrees only, so `nil` contributes neither weight nor a $\log 0$ term.

::: check
- `potential` is `noncomputable` only because of `Real.logb`. Nothing in it is chosen classically.
- The weights are **ghost data**. `Splay.run` takes no weight argument, and every theorem below quantifies over weights only in its analysis, so the same algorithm satisfies all of them simultaneously.
- The mass of a subtree depends only on the interval of keys it holds, not on its shape. Rotations therefore preserve the total weight $W$ and change only the masses of the rotated nodes. The library proves this as `mass_eq_sum`.
- With unit weights `fun _ => 1`, `mass` is `Tree.size` and $\Phi$ is $\sum \log_2(\text{subtree size})$.
:::

## The access lemma

@decl RotationBST.Splay.Results.access_lemma RotationBST.Splay.Results.access_lemma_subtree

Write $k$ for the number of rotations of `run t x`, $t'$ for the splayed tree, and $W$ for `mass w t 0`. Both statements bound the amortized cost $k + \Phi(t') - \Phi(t)$:

$$
k + \Phi(t') - \Phi(t) \;\le\; 3\bigl(\log_2 W - \log_2 s(x)\bigr) + 1 .
$$

`access_lemma_subtree` takes $s(x)$ to be the initial mass of $x$'s subtree. It writes that as `mass w (locate t x).focus (offset (locate t x).context)`: the focus is the subtree rooted at $x$, and the offset is the rank of its smallest key. This is exactly Lemma 1 of the paper, $3(r(t) - r(x)) + 1$. `access_lemma` weakens $s(x)$ to the weight $w(x)$ of $x$ itself, which is the only form the theorems below need.

::: check
- The hypothesis `positive : ∀ i, 0 < w i` asks for positive weights at *every* natural number, though only ranks below `t.size` affect the statement. This costs nothing, since any positive weights on the keys extend to all of `Nat`. Positivity is needed because `Real.logb 2 0 = 0` in Mathlib: with a zero weight, $-\log_2 w(x)$ would silently become $0$.
- The paper counts the time of a splay as its number of rotations, or $1$ if there are none. Here $k$ is exactly the number of rotations, possibly $0$. The additive $1$ pays for a final zig.
- Both $\Phi$ terms are evaluated with the same weights. Changing weights between accesses, as in the working-set proof, is a separate argument.
:::

The proof is the paper's. Three lemmas bound the amortized cost of the local steps: a zig costs at most $3(r'(x) - r(x)) + 1$, and a zig-zig or zig-zag at most $3(r'(x) - r(x))$ (`zig_left`, `zigzig_left`, `zigzag_left` and their mirror images). A rotation inside the context leaves the mass of every strict ancestor unchanged, so it changes no other term of $\Phi$. The induction follows `splayAt`, and the bounds telescope.

The figure below runs the same transcription of `run` as in [Chapter 8](splay.html) with unit weights. It tracks $\Phi$, and at the end checks both inequalities on the actual run.

@viz splay {"n": 15, "shape": "left-path", "x": 2, "potential": true, "title": "The access lemma on an actual splay (unit weights)"}

## Balance (Theorem 1)

@decl RotationBST.Splay.Results.balance

For $m$ requests on $n$ keys, from **any** initial tree,
$$T = m + R \;\le\; m\,(2 + 3\log_2 n) + n\log_2 n .$$
The paper's Theorem 1 states $O((m+n)\log n + m)$. The left side is `totalCost`, so the request count is included ([Chapter 6](online.html)). The logarithms are real, `Real.logb 2 t.size`, not floors. When $n = 0$ both sides are $0$, since a valid request sequence on the empty tree is empty.

The proof uses unit weights. Then $W = n$ and $w(x) = 1$, so each access has amortized rotation cost at most $1 + 3\log_2 n$. Every subtree has mass at least $1$, so $\Phi \ge 0$, and initially $\Phi \le n \log_2 n$. Summing over the sequence and adding $m$ gives the bound.

## Static optimality (Theorem 2)

Theorem 2 of the paper states that if every item is accessed at least once, the total access time is $O(m + \sum_i q_i \log(m/q_i))$, where $q_i$ is the number of accesses to $i$. The library has three versions.

@decl RotationBST.Splay.Results.staticOptimality_all_accessed

This is the paper's statement with explicit constants: $T \le 4 \cdot$ [[RotationBST.Bounds.staticCost|staticCost]], which is $4\,(m + \sum_i q_i \log_2(m/q_i))$, with **no** startup term. The hypothesis `covers : ∀ x < t.size, x ∈ xs` is exactly "every item is accessed". The proof takes $w(i) = q_i$, so $W = m$. The access lemma gives amortized cost $1 + 3\log_2(m/q_x)$. The potential drop over the whole sequence is at most $\sum_i \log_2(W/w(i)) = \sum_i \log_2(m/q_i)$, which is at most $\sum_i q_i\log_2(m/q_i)$ because every $q_i \ge 1$. Adding $m$ for the requests gives $T \le 2m + 4\sum_i q_i\log_2(m/q_i) \le 4\cdot$`staticCost`.

@decl RotationBST.Splay.Results.staticOptimality

Without `covers`, unused keys still sit in the tree, and some startup allowance is needed. [[RotationBST.HasStaticOptimalityBound|HasStaticOptimalityBound]] ([Chapter 7](bounds.html)) has uniform but unspecified constants and an $n(1+\lfloor\log_2 n\rfloor)$ allowance. This theorem is not proved from the access lemma directly: it is the algorithm-independent implication "working set ⇒ static optimality" of [Chapter 7](bounds.html), applied to [[RotationBST.Splay.Results.hasWorkingSetBound|splay's working-set bound]].

@decl RotationBST.Splay.Results.staticOptimality_fixedTree

This is the comparison-tree reading of static optimality: splay, starting from any tree `t`, costs at most $12$ times what the best *fixed* BST `u` on the same keys would cost to serve `xs` by plain searches. [[RotationBST.StaticTree.cost|StaticTree.cost]] counts one unit per request plus the depth of each requested key ([Chapter 7](bounds.html)). The constant is $12 = 4 \cdot 3$: `staticOptimality_all_accessed` contributes the $4$, and the prefix-code bound [[RotationBST.StaticTree.Results.entropy_lower_bound|entropy_lower_bound]], which says `staticCost ≤ 3 · StaticTree.cost u xs` for every tree `u`, contributes the $3$.

::: caveat
Both `_all_accessed` forms need `covers`. If some key is never requested, they say nothing. The general `staticOptimality` still applies, with an additive startup term and unspecified constants.
:::

## Static finger (Theorem 3)

@decl RotationBST.Splay.Results.staticFinger RotationBST.Splay.Results.staticFinger_all_accessed

Theorem 3 of the paper bounds the total time by $O(n\log n + m + \sum_j \log(|i_j - f| + 1))$ for any fixed item $f$. [[RotationBST.Bounds.fingerCost|fingerCost f xs]] is $\sum_j \bigl(1 + \log_2(|x_j - f| + 1)\bigr)$. The distance is `Nat.dist`, the absolute difference of **ranks**, which matches the paper because its items are numbered in symmetric order. `staticFinger` is again the generic implication from working set (through static optimality). `staticFinger_all_accessed` removes the startup term when every key is accessed. Its constant $12 = 4 \cdot 3$ comes from `staticCost n xs ≤ 3 · fingerCost f xs` ([[RotationBST.Bounds.static_le_finger]]), proved with the weights $1/(|i-f|+1)^2$, whose total is at most $4$.

::: check
In `staticFinger_all_accessed` the finger `f` is an arbitrary natural number. There is no hypothesis `f < t.size`, so the statement is slightly stronger than the paper's. [[RotationBST.HasStaticFingerBound|HasStaticFingerBound]] quantifies only over `f < t.size`.
:::

## Working set (Theorem 4)

@decl RotationBST.Splay.Results.workingSet RotationBST.Splay.Results.hasWorkingSetBound

Theorem 4 of the paper bounds the total time by $O(n\log n + m + \sum_j \log(t(j)+1))$, where $t(j)$ counts the distinct items accessed since the previous access to $i_j$. The formal version bounds **rotations**:
$$R \;\le\; 10\cdot\texttt{workingSetSum} + 6\,n\,(1 + \lfloor\log_2 n\rfloor),$$
where [[RotationBST.workingSetSum|workingSetSum]] charges $1 + \lfloor\log_2 \texttt{workingSetNumber}\rfloor$ per request. The working-set number of a repeated access is the paper's $t(j) + 1$. A first access is charged $n$, which is at least the paper's value; the total extra charge is $O(n \log n)$, within the startup term ([Chapter 7](bounds.html) gives the exact conventions). Because `workingSetSum` charges at least $1$ per request, adding the $m$ requests costs at most one more unit per term. [[RotationBST.workingSet_totalCost_iff]] ([Chapter 7](bounds.html)) makes this precise for the property `HasWorkingSetBound`.

The proof follows the paper and changes the weights after every access. Before request $j$, list the keys by recency: most recently accessed first, never-accessed keys after them in increasing order ([[RotationBST.Recency.recent]]). A key at 1-based position $\rho$ gets weight $1/\rho^2$ ([[RotationBST.Recency.weight]]). The total weight is at most $2$ for every order, so the access lemma bounds the amortized cost of accessing the key at position $\rho$ by $3(1 + 2\log_2\rho) + 1 \le 10(1 + \lfloor\log_2\rho\rfloor)$ ([[RotationBST.Recency.access_bound]]). After the access, $x$ moves to the front of the list. Its weight rises to $1$, every other weight weakly falls, and the total is unchanged. Since $x$ is now the root, this cannot increase $\Phi$ ([[RotationBST.Recency.touch_potential]]). Finally $\rho \le$ `workingSetNumber`: they are equal on a repeated access, and $\rho \le n$ on a first access. For any order, $\Phi$ lies between $-2n\log_2(n+1)$ and $n$, and this width is the $6n(1 + \lfloor\log_2 n\rfloor)$ term.

@decl RotationBST.Splay.Results.pointer_workingSet

The same bound in the conventional pointer model: the [pointer implementation](splay.html#a-pointer-implementation) costs at most $m + 3R$, and $m \le$ `workingSetSum`, so $31 = 3 \cdot 10 + 1$ and $18 = 3 \cdot 6$.

## The unified theorem (Theorem 5)

Theorem 5 of the paper charges each access the *smallest* of its three logarithmic costs: frequency, finger distance and working set.

@decl RotationBST.Bounds.unifiedCharge RotationBST.Bounds.unifiedSum

For a request $x$ with history `past`, `unifiedCharge` is
$$1 + \min\Bigl(\log_2 \texttt{workingSetNumber},\; \log_2\frac{m}{q_x},\; \log_2(|x - f| + 1)\Bigr).$$
Frequencies come from the **whole** sequence `original`, so $m$ is its length and $q_x$ the number of occurrences of $x$ in it. Recency comes from the prefix `past`, which `unifiedSum` extends one request at a time while keeping `original` fixed. This mixes offline information (frequencies) with online information (recency), as the paper's bound does. Only the analysis sees the frequencies; the algorithm is still `Splay.run`.

::: check
- These logarithms are real: `Real.logb 2 (workingSetNumber …)` is not the floor used in `workingSetSum`.
- If $x$ did not occur in `original`, then $q_x = 0$, `m / 0 = 0` in Lean, and `logb 2 0 = 0`, so the minimum could collapse to $0$. That never happens here: the theorem uses `unifiedSum t.size f xs [] xs`, so `original` is the very sequence being summed over, and every $x$ occurs in it.
:::

@decl RotationBST.Splay.Results.unified

So $T \le 11\cdot$`unifiedSum` $+\, 8n(1 + \lfloor\log_2 n\rfloor)$ for every initial tree and every finger `f`, again with no `f < t.size` hypothesis. The minimum is taken **per access**, so this is not merely the minimum of the three earlier theorems. The proof uses the sum of three weights: the recency weight $1/\rho^2$, which changes after each access as in the working-set proof, plus two fixed weights, $q_i/m$ and $1/(|i - f| + 1)^2$. The total weight is at most $7 < 2^3$, so $\log_2 W \le 3$. Each of the three weights is at most the combined weight, so the amortized cost of an access is at most $10\cdot$`unifiedCharge`. Every charge is at least $1$, which absorbs the $m$ requests into the constant $11$.

::: caveat Not the dynamic unified bound
This is the 1985 *fixed-finger* unified theorem. It is not Iacono's later unified bound, in which the finger distance is measured to recently accessed keys. Whether splay trees satisfy that bound is open, and the library makes no claim about it.
:::

## Measured cost against the bounds

The figure runs the transcription of splay on a request sequence and plots its cumulative cost against the bound of a chosen theorem. Each point $j$ applies the theorem to the first $j$ requests from the same initial tree. For the static-optimality bound, the panel checks the `covers` hypothesis and says when it fails.

@viz experiment {"theorem": "workingset", "sequence": "workingset", "n": 63, "shape": "left-path", "m": 400}

::: exercise Constants versus behaviour
Switch to **Balance** with **sequential scans**. The measured cost stays far below $m(2 + 3\log_2 n)$, because sequential access is linear ([Chapter 10](beyond.html)). Then try **one key repeated** under **Working set**: after the first access the key stays at the root, each request costs $0$ rotations, and the bound grows by $10$ per request. The theorems give worst-case guarantees with generous constants, not estimates of typical cost.
:::
