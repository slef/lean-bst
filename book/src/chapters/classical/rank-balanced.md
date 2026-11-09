# Rank-balanced trees

AVL trees [@adelson1962] and red-black trees [@bayer1972symmetric; @guibas1978] are usually presented as two different structures, with different invariants and different case analyses. @haeupler2015 showed that both are instances of one framework. Each node stores an integer *rank*, and an invariant on the rank differences between parents and children replaces both the AVL height condition and the red-black colours. The same framework gives a third structure, the weak AVL or *WAVL* tree, which combines the best properties of both. This chapter follows that framework.

Nothing in this chapter is formalized yet. The updates need the dictionary model of [Chapter 6](dictionary.html), which is not formalized either.

## Ranks and rank rules

Every node $x$ has a rank $r(x) \ge 0$, and a missing child has rank $-1$. The *rank difference* of a child $y$ of $x$ is $r(x) - r(y)$. A node whose two children have rank differences $i$ and $j$ is an *$i,j$ node*. The three structures differ only in which rank differences they allow:

| Structure | Rank rule | Rank is |
|---|---|---|
| AVL | every node is 1,1 or 1,2 | the height |
| Red-black | every rank difference is 0 or 1, and no parent of a 0-child is itself a 0-child | the black height; a 0-child is a red node |
| WAVL | every rank difference is 1 or 2, and every leaf is 1,1 | at least the height, at most twice it |

Under each rule, the rank and the height are within a factor of two of each other, and a counting argument bounds the rank. The smallest AVL tree of rank $k$ has one less than a Fibonacci number of keys, $F_{k+3} - 1$, and a red-black tree of rank $k$ has at least $2^{k+1} - 1$ keys. Inverting these counts gives the height bounds.

::: todo
- AVL trees have height less than $1.4405 \log_2(n + 2)$.
- Red-black trees have height at most $2 \log_2(n + 1)$.
- WAVL trees built by $m$ insertions and any deletions have height at most $\log_\varphi m \approx 1.44 \log_2 m$, where $\varphi$ is the golden ratio, and rank at most $2 \log_2 n$. Without deletions a WAVL tree is an AVL tree.

Roadmap [entry 7](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#7-rank-balanced-trees).
:::

## Rebalancing

An insertion adds a leaf of rank $0$, and a deletion removes a node. Either can break the rank rule at one node. Bottom-up rebalancing then repairs it with four primitive steps:

- **promote**, which increases a rank by one;
- **demote**, which decreases a rank by one;
- a **single rotation**;
- a **double rotation**, which is two rotations.

Each step either fixes the violation or moves it one level up. The rank rules differ in when the walk stops, and so in how many rotations an update needs.

::: todo
- **AVL insertion** uses at most one single or double rotation. **AVL deletion** may need $\Theta(\log n)$ rotations.
- **Red-black trees** use at most 2 rotations per insertion and 3 per deletion, and $O(1)$ amortized rank changes (recolourings) per update.
- **WAVL trees** use at most 2 rotations per insertion or deletion, and $O(1)$ amortized rank changes. Rebalancing at rank $k$ is exponentially rare in $k$.
- In the dictionary model, every operation therefore costs $O(\log n)$.

Roadmap [entry 7](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#7-rank-balanced-trees).
:::

In the library, the plan is one representation (a tree with a rank in each node), one set of rebalancing steps, and three rank rules. Each theorem is then proved once for the framework and specialized to each rule.

## Further results

Red-black trees are binary encodings of 2-3-4 trees, the B-trees of order 4 [@bayer1972]. Several variants simplify their case analysis, among them AA trees [@andersson1993] and left-leaning red-black trees [@sedgewick2008]. The [bibliographic notes](notes-classical.html) of this part give the history, including the worst-case and amortized bounds on rebalancing [@tarjan1983; @huddleston1982].
