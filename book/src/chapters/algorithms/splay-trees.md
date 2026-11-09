# Splay trees

Splay trees, introduced by Sleator and Tarjan in 1985, are the best-known self-adjusting binary search tree. They store no balance information. After every access they move the accessed node to the root by a fixed pattern of rotations, and this alone gives $O(\log n)$ amortized cost per access, and much better bounds on structured sequences. Whether splay trees are dynamically optimal is open.

The chapter has three sections.

- [Section 18.1](splay.html) defines splaying, proves that it is a legal BST algorithm in the rotation model, and runs it on the pointer machine.
- [Section 18.2](analysis.html) proves Theorems 1–5 of the 1985 paper from the access lemma: $O(\log n)$ amortized cost, static optimality, the static finger bound, the working-set bound, and a bound that charges each access the smallest of the three.
- [Section 18.3](beyond.html) treats insertion, deletion, split and join, splaying only along long paths, the snapshot theorem, and Tarjan's theorem that sequential access takes linear time.

Splay trees return in [Chapter 24](deamortization.html), which builds a deamortized splay tree: it keeps the access bounds of [Section 18.2](analysis.html) and the sequential access bound, and every access costs $O(\log n)$ in the worst case. Two further results about splay trees are not formalized. The dynamic finger theorem of Cole and coauthors [@cole2000sorting; @cole2000proof] is discussed in [Chapter 12](bounds.html#what-is-not-formalized). The theorem of @chmel2026, that splay trees are $O(\log\log n \cdot \log^2\log\log n)$-competitive, is shown as a dashed arrow in the [map of the bounds](part-bounds.html#a-map-of-the-bounds) and is listed in the library's [roadmap](https://github.com/slef/lean-bst/blob/main/ROADMAP.md).
