# The amortized analysis

A single splay can be slow: an access at depth $n-1$ costs $n-1$ rotations. Sleator and Tarjan's insight is that such an access also roughly halves the depth of every node on its path, so expensive accesses pay for later cheap ones. They make this precise with a potential function and one lemma, the Access Lemma. A whole family of bounds then follows by choosing weights:

- $O(\log n)$ amortized cost per access (balance);
- within a constant factor of the best *static* tree for the sequence (static optimality);
- cheap accesses near any fixed key (static finger);
- cheap accesses to recently used keys (working set).

These are the headline results of the 1985 paper, and all four hold for the same algorithm, which never sees the weights. This chapter proves them with explicit constants. In all four, $t$ is an arbitrary initial tree on $n$ keys, $X = x_1, \dots, x_m$ is a sequence of keys of $t$, and $R$ is the number of rotations splaying performs while serving $X$. The *total cost* $m + R$ counts one unit per request plus one per rotation ([Chapter 5](online.html)).

```headline splay-balance
title: Splaying costs $O(\log n)$ amortized per access
source: Sleator and Tarjan, *Self-adjusting binary search trees* (1985)
key: yes
theorems: Splay.Results.correct Splay.Results.balance

Every splay is a legal root access by rotations, fewer than $n$ of them. Serving any sequence of $m$ requests by splaying, from any initial tree on $n$ keys, has total cost

$$m + R \;\le\; m\,(2 + 3\log_2 n) + n\log_2 n .$$

In Lean, `correct` certifies one splay as an [[RotationBST.Access]], and `balance` bounds `totalCost` of [[RotationBST.Splay.algorithm]], the online algorithm that splays each request in turn.
```

```headline splay-static-optimality
title: Splaying is statically optimal
source: Sleator and Tarjan, *Self-adjusting binary search trees* (1985)
key: yes
theorems: Splay.Results.staticOptimality StaticTree.Results.entropy_lower_bound

Let key $i$ be requested $q_i$ times. There are constants $C$ and $D$ such that for every initial tree on $n$ keys and every sequence of $m$ requests,

$$m + R \;\le\; C\Bigl(m + \sum_i q_i \log_2 \frac{m}{q_i}\Bigr) + D\,n\,\bigl(1 + \lfloor\log_2 n\rfloor\bigr).$$

The sum $\sum_i q_i \log_2(m/q_i)$ is $m$ times the entropy of the access frequencies. The bracket is a lower bound for static trees: for every BST $u$ on the same $n$ keys, serving the sequence by plain searches in $u$ costs $\sum_j \bigl(1 + \mathrm{depth}_u(x_j)\bigr)$, which is at least a third of the bracket. So splaying, which never learns the frequencies, costs at most $3C$ times as much as the best static tree for the sequence, plus a startup term.

In Lean, `staticOptimality` is the property [[RotationBST.HasStaticOptimalityBound]] of [[RotationBST.Splay.algorithm]], and `entropy_lower_bound` is the comparison with every static tree, whose search cost is [[RotationBST.StaticTree.cost]].
```

```headline splay-static-finger
title: Splaying has the static finger property
source: Sleator and Tarjan, *Self-adjusting binary search trees* (1985)
key: yes
theorems: Splay.Results.staticFinger

There are constants $C$ and $D$ such that for every initial tree on $n$ keys, every fixed key $f < n$ (the *finger*) and every sequence of $m$ requests,

$$m + R \;\le\; C\sum_{j=1}^{m} \Bigl(1 + \log_2\bigl(|x_j - f| + 1\bigr)\Bigr) + D\,n\,\bigl(1 + \lfloor\log_2 n\rfloor\bigr).$$

Keys are ranks, so $|x_j - f|$ is the number of keys between the request and the finger. The finger is used only in the analysis: the algorithm is plain splaying.

In Lean, `staticFinger` is the property [[RotationBST.HasStaticFingerBound]] of [[RotationBST.Splay.algorithm]]; the sum is [[RotationBST.Bounds.fingerCost]].
```

```headline splay-working-set
title: Splaying has the working-set property
source: Sleator and Tarjan, *Self-adjusting binary search trees* (1985)
key: yes
theorems: Splay.Results.workingSet

For each request $x_j$, let $w_j$ be one plus the number of distinct keys requested since the previous request to $x_j$, or $n$ if $x_j$ was not requested before. For every initial tree on $n$ keys and every sequence of requests, the number of rotations is at most

$$R \;\le\; 10\sum_{j} \bigl(1 + \lfloor\log_2 w_j\rfloor\bigr) + 6\,n\,\bigl(1 + \lfloor\log_2 n\rfloor\bigr).$$

A key that was used recently is cheap to access again, however large the tree. The sum charges at least $1$ per request, so adding the $m$ requests changes only the constant.

In Lean, $w_j$ is [[RotationBST.workingSetNumber]] and the sum is [[RotationBST.workingSetSum]]; `Splay.algorithm.cost` counts rotations only.
```

## Weights and potential

Sleator and Tarjan analyse splaying with a potential function. Each item $i$ gets a fixed positive weight $w(i)$. The *size* $s(x)$ of a node is the total weight of its subtree, its *rank* is $r(x) = \log_2 s(x)$, and the potential of a tree is the sum of the ranks of its nodes. The Access Lemma bounds the amortized cost of one splay. Their Theorems 1–5 then follow by choosing the weights. The rest of this chapter shows the formal versions of the potential, the lemma and the five theorems. The bounds themselves (working set, entropy, finger) are defined in [Chapter 10](bounds.html).

@decl RotationBST.Splay.mass RotationBST.Splay.potential

The weights are a function `w : Nat → ℝ` on ranks. Because a subtree does not know its own keys, both functions carry the offset `lo` of the subtree's smallest key and update it exactly as [[RotationBST.Tree.labelFrom|labelFrom]] does ([Chapter 1](shapes.html#implicit-keys)). The root of `node l r` is rank `lo + l.size`, so `mass` adds `w (lo + l.size)` between the masses of the two subtrees. `mass w t 0` is the total weight $W$ of the tree. `mass` is the paper's $s$, and `potential` is $\Phi = \sum_x \log_2 s(x)$, summed over nonempty subtrees only, so `nil` contributes neither weight nor a $\log 0$ term.

::: check
- `potential` is `noncomputable` only because of `Real.logb`. Nothing in it is chosen classically.
- The weights are **ghost data**. `Splay.run` takes no weight argument, and every theorem below quantifies over weights only in its analysis, so the same algorithm satisfies all of them simultaneously.
- The mass of a subtree depends only on the interval of keys it holds, not on its shape. Rotations therefore preserve the total weight $W$ and change only the masses of the rotated nodes. The library proves this as `mass_eq_sum`.
- With unit weights `fun _ => 1`, `mass` is `Tree.size` and $\Phi$ is $\sum \log_2(\text{subtree size})$.
:::

## The access lemma

**Theorem (access lemma).** Fix positive weights $w$. Let $t$ be a tree of total weight $W$, and let splaying the rank $x < |t|$ take $k$ rotations and produce $t'$. Then the amortized cost is bounded:

$$
k + \Phi(t') - \Phi(t) \;\le\; 3\bigl(\log_2 W - \log_2 s(x)\bigr) + 1 ,
$$

where $s(x)$ is the initial weight of $x$'s subtree. Since $s(x) \ge w(x)$, the same holds with $s(x)$ replaced by $w(x)$.

@decl RotationBST.Splay.Results.access_lemma RotationBST.Splay.Results.access_lemma_subtree

In Lean, $W$ is `mass w t 0`. `access_lemma_subtree` takes $s(x)$ to be the initial mass of $x$'s subtree. It writes that as `mass w (locate t x).focus (offset (locate t x).context)`: the focus is the subtree rooted at $x$, and the offset is the rank of its smallest key. This is exactly Lemma 1 of the paper, $3(r(t) - r(x)) + 1$. `access_lemma` weakens $s(x)$ to the weight $w(x)$ of $x$ itself, which is the only form the theorems below need.

::: check
- The hypothesis `positive : ∀ i, 0 < w i` asks for positive weights at *every* natural number, though only ranks below `t.size` affect the statement. This costs nothing, since any positive weights on the keys extend to all of `Nat`. Positivity is needed because `Real.logb 2 0 = 0` in Mathlib: with a zero weight, $-\log_2 w(x)$ would silently become $0$.
- The paper counts the time of a splay as its number of rotations, or $1$ if there are none. Here $k$ is exactly the number of rotations, possibly $0$. The additive $1$ pays for a final zig.
- Both $\Phi$ terms are evaluated with the same weights. Changing weights between accesses, as in the working-set proof, is a separate argument.
:::

The proof is the paper's. Three lemmas bound the amortized cost of the local steps: a zig costs at most $3(r'(x) - r(x)) + 1$, and a zig-zig or zig-zag at most $3(r'(x) - r(x))$ (`zig_left`, `zigzig_left`, `zigzag_left` and their mirror images). A rotation inside the context leaves the mass of every strict ancestor unchanged, so it changes no other term of $\Phi$. The induction follows `splayAt`, and the bounds telescope.

The figure below runs the same transcription of `run` as in [Chapter 8](splay.html) with unit weights. It tracks $\Phi$, and at the end checks both inequalities on the actual run.

@viz splay {"n": 15, "shape": "left-path", "x": 2, "potential": true, "title": "The access lemma on an actual splay (unit weights)"}

## Balance (Theorem 1)

**Theorem (balance).** For every initial tree on $n$ keys and every sequence of $m$ valid requests, splaying has total cost $m + R \le m\,(2 + 3\log_2 n) + n\log_2 n$.

@decl RotationBST.Splay.Results.balance

The paper's Theorem 1 states $O((m+n)\log n + m)$. The left side is `totalCost`, so the request count is included ([Chapter 6](online.html)). The logarithms are real, `Real.logb 2 t.size`, not floors. When $n = 0$ both sides are $0$, since a valid request sequence on the empty tree is empty.

The proof uses unit weights. Then $W = n$ and $w(x) = 1$, so each access has amortized rotation cost at most $1 + 3\log_2 n$. Every subtree has mass at least $1$, so $\Phi \ge 0$, and initially $\Phi \le n \log_2 n$. Summing over the sequence and adding $m$ gives the bound.

## Static optimality (Theorem 2)

Theorem 2 of the paper states that if every item is accessed at least once, the total access time is $O(m + \sum_i q_i \log(m/q_i))$, where $q_i$ is the number of accesses to $i$. The library has three versions.

**Theorem (static optimality, every key requested).** If every key of the initial tree is requested at least once, then $m + R \le 4\bigl(m + \sum_i q_i \log_2(m/q_i)\bigr)$.

@decl RotationBST.Splay.Results.staticOptimality_all_accessed

This is the paper's statement with explicit constants: $T \le 4 \cdot$ [[RotationBST.Bounds.staticCost|staticCost]], which is $4\,(m + \sum_i q_i \log_2(m/q_i))$, with **no** startup term. The hypothesis `covers : ∀ x < t.size, x ∈ xs` is exactly "every item is accessed". The proof takes $w(i) = q_i$, so $W = m$. The access lemma gives amortized cost $1 + 3\log_2(m/q_x)$. The potential drop over the whole sequence is at most $\sum_i \log_2(W/w(i)) = \sum_i \log_2(m/q_i)$, which is at most $\sum_i q_i\log_2(m/q_i)$ because every $q_i \ge 1$. Adding $m$ for the requests gives $T \le 2m + 4\sum_i q_i\log_2(m/q_i) \le 4\cdot$`staticCost`.

**Theorem (static optimality).** There are constants $C$ and $D$ such that for every initial tree on $n$ keys and every valid sequence, $m + R \le C\bigl(m + \sum_i q_i \log_2(m/q_i)\bigr) + D\,n\,(1 + \lfloor\log_2 n\rfloor)$.

@decl RotationBST.Splay.Results.staticOptimality

Without `covers`, unused keys still sit in the tree, and some startup allowance is needed. [[RotationBST.HasStaticOptimalityBound|HasStaticOptimalityBound]] ([Chapter 7](bounds.html)) has uniform but unspecified constants and an $n(1+\lfloor\log_2 n\rfloor)$ allowance. This theorem is not proved from the access lemma directly: it is the algorithm-independent implication "working set ⇒ static optimality" of [Chapter 7](bounds.html), applied to [[RotationBST.Splay.Results.hasWorkingSetBound|splay's working-set bound]].

**Theorem (static optimality against a fixed tree).** If every key is requested, then for every tree $u$ on the same $n$ keys, splaying from any initial tree has total cost $m + R \le 12 \sum_j \bigl(1 + \mathrm{depth}_u(x_j)\bigr)$.

@decl RotationBST.Splay.Results.staticOptimality_fixedTree

This is the comparison-tree reading of static optimality: splay, starting from any tree `t`, costs at most $12$ times what the best *fixed* BST `u` on the same keys would cost to serve `xs` by plain searches. [[RotationBST.StaticTree.cost|StaticTree.cost]] counts one unit per request plus the depth of each requested key ([Chapter 7](bounds.html)). The constant is $12 = 4 \cdot 3$: `staticOptimality_all_accessed` contributes the $4$, and the prefix-code bound [[RotationBST.StaticTree.Results.entropy_lower_bound|entropy_lower_bound]], which says `staticCost ≤ 3 · StaticTree.cost u xs` for every tree `u`, contributes the $3$.

::: caveat
Both `_all_accessed` forms need `covers`. If some key is never requested, they say nothing. The general `staticOptimality` still applies, with an additive startup term and unspecified constants.
:::

## Static finger (Theorem 3)

**Theorem (static finger).** There are constants $C$ and $D$ such that for every initial tree on $n$ keys, every finger $f < n$ and every valid sequence, $m + R \le C \sum_j \bigl(1 + \log_2(|x_j - f| + 1)\bigr) + D\,n\,(1 + \lfloor\log_2 n\rfloor)$. If every key is requested, then $m + R \le 12 \sum_j \bigl(1 + \log_2(|x_j - f| + 1)\bigr)$ for every natural number $f$, with no startup term.

@decl RotationBST.Splay.Results.staticFinger RotationBST.Splay.Results.staticFinger_all_accessed

Theorem 3 of the paper bounds the total time by $O(n\log n + m + \sum_j \log(|i_j - f| + 1))$ for any fixed item $f$. [[RotationBST.Bounds.fingerCost|fingerCost f xs]] is $\sum_j \bigl(1 + \log_2(|x_j - f| + 1)\bigr)$. The distance is `Nat.dist`, the absolute difference of **ranks**, which matches the paper because its items are numbered in symmetric order. `staticFinger` is again the generic implication from working set (through static optimality). `staticFinger_all_accessed` removes the startup term when every key is accessed. Its constant $12 = 4 \cdot 3$ comes from `staticCost n xs ≤ 3 · fingerCost f xs` (`Bounds.static_le_finger`), proved with the weights $1/(|i-f|+1)^2$, whose total is at most $4$.

::: check
In `staticFinger_all_accessed` the finger `f` is an arbitrary natural number. There is no hypothesis `f < t.size`, so the statement is slightly stronger than the paper's. [[RotationBST.HasStaticFingerBound|HasStaticFingerBound]] quantifies only over `f < t.size`.
:::

## Working set (Theorem 4)

**Theorem (working set).** For every initial tree on $n$ keys and every valid sequence, $R \le 10 \sum_j \bigl(1 + \lfloor\log_2 w_j\rfloor\bigr) + 6\,n\,(1 + \lfloor\log_2 n\rfloor)$, where $w_j$ is the working-set number of request $j$. In particular, splaying has the working-set property `HasWorkingSetBound`.

@decl RotationBST.Splay.Results.workingSet RotationBST.Splay.Results.hasWorkingSetBound

Theorem 4 of the paper bounds the total time by $O(n\log n + m + \sum_j \log(t(j)+1))$, where $t(j)$ counts the distinct items accessed since the previous access to $i_j$. The formal version bounds **rotations**:
$$R \;\le\; 10\cdot\texttt{workingSetSum} + 6\,n\,(1 + \lfloor\log_2 n\rfloor),$$
where [[RotationBST.workingSetSum|workingSetSum]] charges $1 + \lfloor\log_2 \texttt{workingSetNumber}\rfloor$ per request. The working-set number of a repeated access is the paper's $t(j) + 1$. A first access is charged $n$, which is at least the paper's value; the total extra charge is $O(n \log n)$, within the startup term ([Chapter 7](bounds.html) gives the exact conventions). Because `workingSetSum` charges at least $1$ per request, adding the $m$ requests costs at most one more unit per term. [[RotationBST.workingSet_totalCost_iff]] ([Chapter 7](bounds.html)) makes this precise for the property `HasWorkingSetBound`.

The proof follows the paper and changes the weights after every access. Before request $j$, list the keys by recency: most recently accessed first, never-accessed keys after them in increasing order (`Recency.recent`). A key at 1-based position $\rho$ gets weight $1/\rho^2$ (`Recency.weight`). The total weight is at most $2$ for every order, so the access lemma bounds the amortized cost of accessing the key at position $\rho$ by $3(1 + 2\log_2\rho) + 1 \le 10(1 + \lfloor\log_2\rho\rfloor)$ (`Recency.access_bound`). After the access, $x$ moves to the front of the list. Its weight rises to $1$, every other weight weakly falls, and the total is unchanged. Since $x$ is now the root, this cannot increase $\Phi$ (`Recency.touch_potential`). Finally $\rho \le$ `workingSetNumber`: they are equal on a repeated access, and $\rho \le n$ on a first access. For any order, $\Phi$ lies between $-2n\log_2(n+1)$ and $n$, and this width is the $6n(1 + \lfloor\log_2 n\rfloor)$ term.

**Theorem (working set on the pointer machine).** For every initial tree and every valid sequence, there is a pointer-machine execution that ends in exactly the splayed tree and costs at most $31 \sum_j \bigl(1 + \lfloor\log_2 w_j\rfloor\bigr) + 18\,n\,(1 + \lfloor\log_2 n\rfloor)$.

@decl RotationBST.Splay.Results.pointer_workingSet

The same bound in the conventional pointer model: the [pointer implementation](splay.html#a-pointer-implementation) costs at most $m + 3R$, and $m \le$ `workingSetSum`, so $31 = 3 \cdot 10 + 1$ and $18 = 3 \cdot 6$.

## The unified theorem (Theorem 5)

Theorem 5 of the paper charges each access the *smallest* of its three logarithmic costs: frequency, finger distance and working set. The charge [[RotationBST.Bounds.unifiedCharge|unifiedCharge]] and its sum [[RotationBST.Bounds.unifiedSum|unifiedSum]] are sequence functions, defined with the other benchmarks in [Section 10.4](bounds.html#the-unified-charge). The frequencies there come from the whole sequence, but only the analysis sees them; the algorithm is still `Splay.run`.

**Theorem (unified bound, fixed finger).** For every initial tree on $n$ keys, every natural number $f$ and every valid sequence, $m + R \le 11 \sum_j c_j + 8\,n\,(1 + \lfloor\log_2 n\rfloor)$, where $c_j$ is the smallest of the frequency, finger and working-set charges of request $j$.

@decl RotationBST.Splay.Results.unified

As for the static finger theorem, there is no `f < t.size` hypothesis. The minimum is taken **per access**, so this is not merely the minimum of the three earlier theorems. The proof uses the sum of three weights: the recency weight $1/\rho^2$, which changes after each access as in the working-set proof, plus two fixed weights, $q_i/m$ and $1/(|i - f| + 1)^2$. The total weight is at most $7 < 2^3$, so $\log_2 W \le 3$. Each of the three weights is at most the combined weight, so the amortized cost of an access is at most $10\cdot$`unifiedCharge`. Every charge is at least $1$, which absorbs the $m$ requests into the constant $11$.

::: caveat Not the dynamic unified bound
This is the 1985 *fixed-finger* unified theorem. It is not Iacono's later unified bound, in which the finger distance is measured to recently accessed keys. Whether splay trees satisfy that bound is open, and the library makes no claim about it.
:::

## Measured cost against the bounds

The figure runs the transcription of splay on a request sequence and plots its cumulative cost against the bound of a chosen theorem. Each point $j$ applies the theorem to the first $j$ requests from the same initial tree. For the static-optimality bound, the panel checks the `covers` hypothesis and says when it fails.

@viz experiment {"theorem": "workingset", "sequence": "workingset", "n": 63, "shape": "left-path", "m": 400}

::: exercise Constants versus behaviour
Switch to **Balance** with **sequential scans**. The measured cost stays far below $m(2 + 3\log_2 n)$, because sequential access is linear ([Chapter 10](beyond.html)). Then try **one key repeated** under **Working set**: after the first access the key stays at the root, each request costs $0$ rotations, and the bound grows by $10$ per request. The theorems give worst-case guarantees with generous constants, not estimates of typical cost.
:::

::: note Worst-case time per access
All the bounds of this chapter are amortized: a single access can cost $\Theta(n)$ rotations. [Chapter 37](deamortization.html) builds one deamortized splay program that keeps the scanning, balance, working-set, static-optimality and static-finger bounds up to constant factors, and serves every access in $O(\log n)$ time in the worst case.
:::
