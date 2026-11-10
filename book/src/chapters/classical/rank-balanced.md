# Rank-balanced trees

AVL trees [@adelson1962] and red-black trees [@bayer1972symmetric; @guibas1978] are usually presented as two different structures, with different invariants and different case analyses. @haeupler2015 showed that both are instances of one framework. Each node stores an integer *rank*, and an invariant on the rank differences between parents and children replaces both the AVL height condition and the red-black colours. The same framework gives a third structure, the weak AVL or *WAVL* tree, which combines the best properties of both. This chapter follows that framework: one representation, three rules, and one insertion procedure.

```headline rank-balanced-height
title: AVL, red-black and WAVL trees have logarithmic height
source: @adelson1962; @guibas1978; @haeupler2015
theorems: Classical.RankBalanced.Results.avl_height Classical.RankBalanced.Results.redBlack_height Classical.RankBalanced.Results.wavl_height

Let $t$ be a tree on $n$ keys whose nodes carry integer ranks, and count its height in nodes. If the ranks satisfy the AVL rule, the height is at most $\log_\varphi(n + 1) \approx 1.44 \log_2(n + 1)$, where $\varphi$ is the golden ratio. If they satisfy the red-black rule, or the WAVL rule, the height is at most $2\log_2(n + 1)$.

In Lean, ranked trees are [[RotationBST.Classical.RankBalanced.RankedTree]], the rules are [[RotationBST.Classical.RankBalanced.Rule]], and `Valid rule t` says that every node of `t` satisfies the rule. Heights are [[RotationBST.Tree.height]] of the underlying shape `t.erase`.
```

```headline wavl-insertion
title: WAVL and AVL insertion uses at most two rotations, and $O(1)$ amortized rank changes from the empty tree
source: @haeupler2015
theorems: Classical.RankBalanced.Results.insert_step Classical.RankBalanced.Results.insert_wavl Classical.RankBalanced.Results.insert_avl Classical.RankBalanced.Results.insert_rotations Classical.RankBalanced.Results.insertEdits_empty Classical.RankBalanced.Results.insertAll_height

Bottom-up insertion into a WAVL tree keeps the WAVL rule, keeps the AVL rule when the tree is an AVL tree, and makes at most two rotations. It is a step of the dictionary model whose cost is one plus the depth of the new leaf plus the rotations. Any $m$ insertions into the empty tree change at most $7m$ ranks in total, and leave a tree of height at most $\log_\varphi(m + 1)$.

In Lean, insertion is [[RotationBST.Classical.RankBalanced.insert]], which returns the tree, its number of rotations and its number of rank changes. The dictionary step is [[RotationBST.Dictionary.Step]] of [Chapter 6](dictionary.html), with rank changes as its data edits.
```

## Ranks and rank rules

@decl RotationBST.Classical.RankBalanced.RankedTree RotationBST.Classical.RankBalanced.rank

A ranked tree is a labelled tree of [Chapter 1](shapes.html#labelled-trees) whose labels are integers. Keys remain the inorder ranks of the shape, so a ranked tree has two kinds of rank: the key rank of a node, its position in the inorder, and its balance rank, the integer it stores. In this chapter "rank" means the balance rank. The empty tree has rank $-1$.

The *rank difference* of a child is its parent's rank minus its own. A node whose two children have rank differences $i$ and $j$ is an *$i,j$ node*. The three structures differ only in which rank differences they allow:

@decl RotationBST.Classical.RankBalanced.Rule RotationBST.Classical.RankBalanced.NoZeroChild RotationBST.Classical.RankBalanced.Rule.Local RotationBST.Classical.RankBalanced.Valid

| Structure | Rank rule | Rank is |
|---|---|---|
| AVL | every node is 1,1 or 1,2 | the height in edges |
| Red-black | every rank difference is 0 or 1, and a 0-child has no 0-child | the black height; a 0-child is a red node |
| WAVL | every rank difference is 1 or 2, and every leaf has rank 0 | at least the height in edges, at most twice it |

`Rule.Local rule l k r` is the rule at one node of rank `k` with subtrees `l` and `r`. `Valid rule t` asks it at every node, and asks every rank to be nonnegative. The red-black condition "a 0-child has no 0-child" is `NoZeroChild`, applied to every child of rank difference $0$.

## Heights

Under each rule a counting argument bounds the rank. The smallest AVL tree of rank $k$ has $F_{k+3} - 1$ keys, one less than a Fibonacci number. For the red-black and WAVL rules, similar counts show that a tree of height $h$, in nodes, has at least $2^{h/2} - 1$ keys. Inverting these counts gives the height bounds.

**Theorem (heights).** In an AVL tree the rank of the root is its height in edges. AVL trees have height at most $\log_\varphi(n + 1)$, in nodes. Red-black trees have height at most $2\log_2(n + 1)$. WAVL trees have rank plus one, and height, at most $2\log_2(n + 1)$. Every AVL tree is a WAVL tree.

@decl RotationBST.Classical.RankBalanced.Results.avl_height_rank RotationBST.Classical.RankBalanced.Results.avl_height RotationBST.Classical.RankBalanced.Results.redBlack_height RotationBST.Classical.RankBalanced.Results.wavl_rank RotationBST.Classical.RankBalanced.Results.wavl_height RotationBST.Classical.RankBalanced.Results.avl_wavl

Knuth's sharper form of the AVL bound is $h < 1.4405 \log_2(n + 2) - 0.3277$, for the height $h$ in nodes. The library proves $\log_\varphi(n + 1)$, with the same leading constant $1/\log_2\varphi \approx 1.4404$ but a weaker additive term; the sharper form is not proved.

## Insertion

An insertion adds a leaf of rank $0$ at the gap, with [[LabelledTree.insertAt]] of [Chapter 6](dictionary.html). Its parent may now have a 0-child, which both the AVL and the WAVL rule forbid. Going up, the procedure repairs the parent with one of three moves:

- if the other child is a 1-child, **promote** the parent, increasing its rank by one, and continue at the grandparent;
- otherwise, if the outer child of the 0-child is a 1-child, make one **single rotation**, with one demotion, and stop;
- otherwise make a **double rotation**, two rotations with three rank changes, and stop.

@decl RotationBST.Classical.RankBalanced.fixLeft RotationBST.Classical.RankBalanced.fixRight RotationBST.Classical.RankBalanced.insert RotationBST.Classical.RankBalanced.insertAll RotationBST.Classical.RankBalanced.insertEdits

`fixLeft l' k r a e` repairs a node of rank `k` whose left subtree became `l'`, adding to the counts `a` of rotations and `e` of rank changes; `fixRight` is its mirror image. `insert t g` inserts at gap `g` recursively and repairs on the way back up. `insertAll` and `insertEdits` run a list of insertions, and add up their rank changes. The same procedure is AVL insertion: on an AVL tree it produces an AVL tree.

**Theorem (insertion).** Insertion is a dictionary step whose main cost is one plus the depth of the new leaf, in the tree before rebalancing, plus the rotations, and whose data edits are the rank changes. It adds one key. It keeps the WAVL rule and the AVL rule, and makes at most two rotations.

@decl RotationBST.Classical.RankBalanced.Results.insert_step RotationBST.Classical.RankBalanced.Results.insert_size RotationBST.Classical.RankBalanced.Results.insert_wavl RotationBST.Classical.RankBalanced.Results.insert_avl RotationBST.Classical.RankBalanced.Results.insert_rotations

A single insertion may promote all the way up, $\Theta(\log n)$ rank changes. On average it does not. The potential is the number of 1,1 nodes: a promotion turns a 1,1 node into a 1,2 node, and the steps that end the walk create only a constant number of 1,1 nodes.

**Theorem (insertions from empty).** Any $m$ insertions into the empty tree change at most $7m$ ranks in total, and leave a tree of height at most $\log_\varphi(m + 1)$.

@decl RotationBST.Classical.RankBalanced.Results.insertEdits_empty RotationBST.Classical.RankBalanced.Results.insertAll_height

The height bound follows from the AVL bound, because insertions alone keep the tree an AVL tree.

## What is not formalized

::: todo
- **Deletion.** WAVL deletion with at most two rotations, red-black deletion with at most three, and AVL deletion, which may need $\Theta(\log n)$ rotations.
- **Red-black insertion**, with at most two rotations.
- **Amortized rank changes with deletions**: $O(1)$ per update for red-black and WAVL trees, and rebalancing at rank $k$ exponentially rare in $k$.
- **WAVL height with deletions**: at most $\log_\varphi m$ after $m$ insertions and any deletions. Without deletions, the theorem above gives $\log_\varphi(m + 1)$.

Roadmap [entry 7](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#7-rank-balanced-trees).
:::

## Further results

Red-black trees are binary encodings of 2-3-4 trees, the B-trees of order 4 [@bayer1972]. Several variants simplify their case analysis, among them AA trees [@andersson1993] and left-leaning red-black trees [@sedgewick2008]. The [bibliographic notes](notes-classical.html) of this part give the history, including the worst-case and amortized bounds on rebalancing [@tarjan1983; @huddleston1982].
