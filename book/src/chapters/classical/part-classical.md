# Classical search trees

Parts I and II fixed the models and the benchmarks. Part III collects the classical binary search trees, which do not adapt to the requests. Their shape depends on the set of keys, on the history of insertions and deletions, and for random trees on random choices. It never depends on which keys are searched. They are the baseline that the adaptive algorithms of [Part IV](part-algorithms.html) are measured against.

The baseline is simple to state. A tree of height $h$ serves a search with at most $h + 1$ nodes, and a balanced tree has height about $\log_2 n$. So $m$ searches cost at most about $m(1 + \log_2 n)$. Every benchmark of Part II is at most this much, up to constant factors: it is the bottom box of the [map of the bounds](part-bounds.html#a-map-of-the-bounds). In general it cannot be beaten. On the bit-reversal sequence every BST pays $\Omega(\log n)$ per request ([Chapter 17](conditional-entropy.html#the-bit-reversal-sequence)). What a classical tree cannot do is exploit an easy sequence. On a sequential scan, a balanced tree still pays $\log_2 n$ per request, while splay trees pay a constant amortized ([Section 23.3](beyond.html#sequential-access)).

The part has four chapters, one per idea for keeping a tree shallow. Each chapter presents one theory, and the classical structures as its instances, rather than one analysis per structure:

- [Chapter 18](static-trees.html): **static trees** never change. They are built once, from the number of keys or from access frequencies. The theory is the cost of a fixed tree, its entropy bounds, and the optimal tree by dynamic programming.
- [Chapter 19](rank-balanced.html): **rank-balanced trees** store an integer rank in each node and keep the rank differences within fixed rules. AVL, red-black and WAVL trees are three choices of rules.
- [Chapter 20](weight-balanced.html): **weight-balanced trees** keep every child's subtree a bounded fraction of its parent's. They restore the invariant either with rotations (BB[α] trees) or by rebuilding a subtree (scapegoat trees).
- [Chapter 21](random-trees.html): **random trees** leave the shape to chance. Random insertion orders, treaps and randomized BSTs all draw from the same distribution.

Dynamic trees change their key set, so they need a model with insertions and deletions. It is described in [Chapter 6](dictionary.html).

## The structures at a glance

The table lists the guarantees that the chapters state. Here $n$ is the number of keys, and a rotation count is per insertion or deletion. Every operation also pays for its search path, at most the height plus one.

| Structure | Height | Rotations per update | Status | Chapter |
|---|---|---|---|---|
| Perfect static tree | $\lfloor \log_2 n \rfloor$ | none (static) | not yet formalized | {{num:static-trees}} |
| Entropy tree for given frequencies | key $x$ at depth $\le \log_2(W/w_x)$ | none (static) | formalized | {{num:static-trees}} |
| Optimal static tree (Knuth) | depends on the frequencies | none (static) | not yet formalized | {{num:static-trees}} |
| AVL tree | $< 1.4405 \log_2(n + 2)$ | insertion: one single or double rotation; deletion: $O(\log n)$ | not yet formalized | {{num:rank-balanced}} |
| Red-black tree | $\le 2 \log_2(n + 1)$ | insertion $\le 2$, deletion $\le 3$ | not yet formalized | {{num:rank-balanced}} |
| WAVL tree | as AVL without deletions, never worse than red-black | $\le 2$ | not yet formalized | {{num:rank-balanced}} |
| BB[α] tree | $\le \log_{1/(1-\alpha)} (n + 1)$ | $O(1)$ amortized | not yet formalized | {{num:weight-balanced}} |
| Scapegoat tree | $\le \log_{1/\alpha} n + 1$ | $O(\log n)$ amortized, by rebuilding | not yet formalized | {{num:weight-balanced}} |
| Random BST, treap | expected depth $\le 2 \ln n$ | treap: fewer than 2 expected | partly formalized | {{num:random-trees}} |

## What is formalized

Most of this part is not formalized yet. The library already has:

- the cost of a fixed tree and its two entropy bounds ([Chapter 13](bounds.html#comparison-with-a-fixed-tree));
- weighted-median trees, with depth $\log_2(W/w_x)$ for every key ([Chapter 31](prefix-sums.html#weighted-search-trees));
- the perfect and balanced trees, as definitions ([Section 26.1](preferred-paths.html));
- random treaps, with the probability that one key is an ancestor of another ([Chapter 29](treaps.html#random-treaps)).

The chapters of this part point to these results and state the rest. Each missing result is in a dashed box marked "Not yet formalized". The library's [roadmap](https://github.com/slef/lean-bst/blob/main/ROADMAP.md) gives a target Lean statement for each of them, for a later round of proofs. The results that are hard to formalize are listed there as stretch goals.
