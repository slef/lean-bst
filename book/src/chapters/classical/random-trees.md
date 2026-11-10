# Random search trees

The third way to keep a tree shallow is to leave its shape to chance. Several classical structures do this, and all of them draw from the same distribution: the *random BST*. This chapter presents that distribution once, through treaps, and the structures as different ways to sample it and keep it under updates.

```headline random-bst-depth
title: In a random binary search tree, key $x$ has expected depth $H_{x+1} + H_{n-x} - 2 \le 2\ln n$
source: @hibbard1962; @seidel1996
theorems: Classical.Random.Results.random_bst_depth Classical.Random.Results.random_bst_depth_le Classical.Random.Results.insertKeys_treap

Insert the keys $0, \dots, n - 1$ into an empty binary search tree, without rebalancing, in a uniformly random order. Then key $x$ has expected depth exactly $H_{x+1} + H_{n-x} - 2$, where $H_k = 1 + \frac12 + \dots + \frac1k$ is the harmonic number, and this is at most $2 \ln n$. The tree built from an insertion order is the treap whose priorities are the positions in the order.

In Lean, insertion is [[RotationBST.Classical.Random.insertKeys]], the expectation over random orders is [[RotationBST.Treap.Random.average]] of [Chapter 31](treaps.html#random-treaps) with uniform weights, and `harmonic` is Mathlib's.
```

## One distribution

Give the $n$ keys a uniformly random order, and read it as priorities: the first key in the order has the smallest priority. The treap for these priorities is the BST in which every node has a smaller priority than its descendants, [[Geometric.Heap]] of [Chapter 31](treaps.html#treaps-for-arbitrary-priorities). It is unique. It is also the tree obtained by inserting the keys into an empty BST, without rebalancing, in that order: the first key becomes the root, and each later key is a descendant of every earlier key on its search path. This is the random BST of @hibbard1962.

@decl RotationBST.Classical.Random.insertKey RotationBST.Classical.Random.insertKeys

Here keys are labels, compared on insertion, and the shape of the result is its `erase`. `insertKey` goes left at a larger label and right otherwise.

**Theorem (insertion builds the treap).** If `order` lists the keys $0, \dots, n - 1$ once each, then inserting them in that order gives a tree on $n$ keys with the heap property for the positions in the order.

@decl RotationBST.Classical.Random.Results.insertKeys_treap

Everything about the expected shape follows from one fact. A key $a$ is an ancestor of $x$ exactly when $a$ has the smallest priority among the keys between $a$ and $x$, inclusive. With a uniform order this happens with probability $1/(|a - x| + 1)$. The library proves the weighted version of this fact, for the random treaps of [Chapter 31](treaps.html#random-treaps), in which the order is drawn with probabilities proportional to given weights; with equal weights, it is the uniform case. Summing over $a$ gives the expected depth of $x$, its number of proper ancestors. Counting keys from $0$,

$$\mathbb{E}[\mathrm{depth}(x)] \;=\; \sum_{a \ne x} \frac{1}{|a - x| + 1} \;=\; H_{x+1} + H_{n-x} - 2 \;\le\; 2 \ln n .$$

**Theorem (expected depth in a random treap).** For every family of trees `T xs` on $n$ keys, one for every list `xs`, with the heap property for the positions in `xs`, the expected depth of $x$ over a uniformly random order is $H_{x+1} + H_{n-x} - 2$, and at most $2 \ln n$.

@decl RotationBST.Classical.Random.Results.expected_depth RotationBST.Classical.Random.Results.expected_depth_le

Combining the two theorems gives the headline result for random insertion orders:

@decl RotationBST.Classical.Random.Results.random_bst_depth RotationBST.Classical.Random.Results.random_bst_depth_le

Summing over the searches, a random BST serves $m$ searches at expected cost at most $m(1 + 2\ln n) \approx m(1 + 1.39 \log_2 n)$; the library states the bound per key, not this sum. The Isabelle formalization of @eberl2020 covers similar ground.

## Treaps

Treaps [@seidel1996] keep the distribution under updates. Each key draws a random priority when it is inserted. An insertion adds the key as a leaf, then rotates it up while its priority is smaller than its parent's. A deletion rotates the key down until it is a leaf, then removes it. The trees are the Cartesian trees of @vuillemin1980, maintained dynamically.

Because the treap for given keys and priorities is unique, the shape after any sequence of updates depends only on the current keys and their priorities, not on the order of the updates. With random priorities it is always a random BST.

::: todo
- Treap insertion and deletion produce the treap of the new key set.
- An insertion or a deletion makes fewer than 2 rotations in expectation.

Roadmap [entry 9](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#9-random-search-trees).
:::

## Other ways to sample

Randomized BSTs [@martinez1998] replace stored priorities by subtree sizes and fresh random choices at each insertion. A new key becomes the root of a subtree of size $s$ with probability $1/(s + 1)$. The tree is again a random BST after every operation. Zip trees [@tarjan2021] store small random ranks, drawn from a geometric distribution, and break ties by key. Their insertions and deletions *unzip* and *zip* a search path instead of rotating. Their shape is a treap for these ranks, with expected depths that are also logarithmic. They belong in this chapter as further samplers of a treap. Each needs one theorem relating it to the treap, not a separate analysis.

::: todo
Randomized BSTs produce the random BST after every operation. Zip trees produce the treap of their ranks.

Roadmap [entry 9](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#9-random-search-trees).
:::

## Height

The expected depth of a single key is about $2 \ln n$. The height of a random BST, the largest depth, is larger: about $4.311 \ln n$ in expectation [@devroye1986], and concentrated around that value [@reed2003; @drmota2003]. This is a hard proof. It is a stretch goal in the roadmap ([S2](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#s2-height-of-random-search-trees)).
