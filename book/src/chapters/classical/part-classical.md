# Classical search trees

[Part I](part-models.html) and [Part II](part-bounds.html) fixed the models and the benchmarks. Part III collects the classical binary search trees, which do not adapt to the requests. Their shape depends on the set of keys, on the history of insertions and deletions, and for random trees on random choices. It never depends on which keys are searched. They are the baseline that the adaptive algorithms of [Part IV](part-algorithms.html) are measured against.

The baseline is simple to state. A search visits at most as many nodes as the height of the tree, counted in nodes, and a balanced tree has height $\lfloor\log_2 n\rfloor + 1$. So $m$ searches cost at most $m(1 + \log_2 n)$. Every benchmark of [Part II](part-bounds.html) is at most this much, up to constant factors: it is the bottom box of the [map of the bounds](part-bounds.html#a-map-of-the-bounds). In general it cannot be beaten. On the bit-reversal sequence every BST pays $\Omega(\log n)$ per request ([Chapter 17](conditional-entropy.html#the-bit-reversal-sequence)). What a classical tree cannot do is exploit an easy sequence. On a sequential scan, a balanced tree still pays $\log_2 n$ per request, while splay trees pay a constant amortized ([Section 23.3](beyond.html#sequential-access)).

The part has four chapters, one per idea for keeping a tree shallow. Each chapter presents one theory, and the classical structures as its instances, rather than one analysis per structure:

- [Chapter 18](static-trees.html): **static trees** never change. They are built once, from the number of keys or from access frequencies. The theory is the cost of a fixed tree, its entropy bounds, and the optimal tree by dynamic programming.
- [Chapter 19](rank-balanced.html): **rank-balanced trees** store an integer rank in each node and keep the rank differences within fixed rules. AVL, red-black and WAVL trees are three choices of rules.
- [Chapter 20](weight-balanced.html): **weight-balanced trees** keep every child's subtree a bounded fraction of its parent's. They restore the invariant either with rotations (BB[α] trees) or by rebuilding a subtree (scapegoat trees).
- [Chapter 21](random-trees.html): **random trees** leave the shape to chance. Random insertion orders, treaps and randomized BSTs all draw from the same distribution.

Dynamic trees change their key set, so they need a model with insertions and deletions. It is described in [Chapter 6](dictionary.html).

## The structures at a glance

The table lists the guarantees that the chapters state. Here $n$ is the number of keys, heights count nodes, and a rotation count is per insertion or deletion. Every operation also pays for its search path, at most the height.

| Structure | Height | Rotations per update | Status | Chapter |
|---|---|---|---|---|
| Balanced static tree | $\lfloor \log_2 n \rfloor + 1$, the minimum | none (static) | formalized | {{num:static-trees}} |
| Entropy tree for given frequencies | key $x$ at depth $\le \log_2(W/w_x)$ | none (static) | formalized | {{num:static-trees}} |
| Optimal static tree (Knuth) | depends on the frequencies | none (static); its cost computed in $O(n^2)$ steps | formalized | {{num:static-trees}} |
| AVL tree | $\le \log_\varphi(n + 1) \approx 1.44 \log_2(n + 1)$ | insertion: one single or double rotation; deletion: $O(\log n)$ | height and insertion formalized; deletion not yet | {{num:rank-balanced}} |
| Red-black tree | $\le 2 \log_2(n + 1)$ | insertion $\le 2$, deletion $\le 3$ | height formalized; updates not yet | {{num:rank-balanced}} |
| WAVL tree | $\le 2 \log_2(n + 1)$, and $\le \log_\varphi(m + 1)$ after $m$ insertions | $\le 2$; $O(1)$ amortized rank changes from empty | height and insertion formalized; deletion not yet | {{num:rank-balanced}} |
| BB[α] tree, $\frac{2}{11} < \alpha \le 1 - \frac{\sqrt 2}{2}$ | $\le \log_{1/(1-\alpha)} (n + 1)$, for any $\alpha$ | $O(1)$ amortized | height formalized; rebalancing not yet | {{num:weight-balanced}} |
| Scapegoat tree, $\alpha > \frac12$ | depth $\le \log_{1/\alpha} n + 1$ | $O(\log n)$ amortized cost, by rebuilding | formalized | {{num:weight-balanced}} |
| Random BST, treap | expected depth $\le 2 \ln n$ | treap: fewer than 2 expected | expected depth formalized; treap updates not yet | {{num:random-trees}} |

## What is formalized

The library proves most of this part:

- **Static trees** ([Chapter 18](static-trees.html)): the balanced tree is as shallow as possible; the logarithmic baseline is met by the balanced tree, and paid by every static tree on some sequence; the entropy bounds; the optimal static tree by the recurrence, Yao's quadrangle inequality, and Knuth's $O(n^2)$ algorithm.
- **Rank-balanced trees** ([Chapter 19](rank-balanced.html)): the height bounds of AVL, red-black and WAVL trees, and WAVL insertion, which is also AVL insertion, with at most two rotations, and $O(1)$ amortized rank changes for insertions from the empty tree.
- **Weight-balanced trees** ([Chapter 20](weight-balanced.html)): the height bound for any balance parameter, rebuilding with two rotations per key, and scapegoat trees with logarithmic depth and $O(\log n)$ amortized cost per update.
- **Random trees** ([Chapter 21](random-trees.html)): the exact expected depth in a random BST, and the fact that insertion in a given order builds the treap of that order.
- **The update model** ([Chapter 6](dictionary.html)), shared by all of them, which charges each operation its search path and its rotations.

What is missing is in dashed boxes marked "Not yet formalized": deletion and red-black insertion, BB[α] rebalancing, treap updates by rotations, and the other samplers of the random BST. The library's [roadmap](https://github.com/slef/lean-bst/blob/main/ROADMAP.md) gives a target Lean statement for each of them, for a later round of proofs. The results that are hard to formalize are listed there as stretch goals.
