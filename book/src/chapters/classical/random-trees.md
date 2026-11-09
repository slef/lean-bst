# Random search trees

The third way to keep a tree shallow is to leave its shape to chance. Several classical structures do this, and all of them draw from the same distribution: the *random BST*. This chapter presents that distribution once, through treaps, and the structures as different ways to sample it and keep it under updates.

## One distribution

Give the $n$ keys a uniformly random order, and read it as priorities: the first key in the order has the smallest priority. The treap for these priorities is the BST in which every node has a smaller priority than its descendants ([Chapter 31](treaps.html#treaps-for-arbitrary-priorities)). It is unique, and it is the same tree as the one obtained by inserting the keys into an empty BST, without rebalancing, in that order. This is the random BST of @hibbard1962.

Everything about its expected shape follows from one fact. A key $a$ is an ancestor of $x$ exactly when $a$ has the smallest priority among the keys between $a$ and $x$, inclusive. With a uniform order this happens with probability $1/(|a - x| + 1)$. The library proves the weighted version of this fact, for the random treaps of [Chapter 31](treaps.html#random-treaps), in which the order is drawn with probabilities proportional to given weights. With equal weights, it is the uniform case.

Summing over $a$ gives the expected depth of $x$, the number of its proper ancestors. Counting keys from $0$,

$$\mathbb{E}[\mathrm{depth}(x)] \;=\; \sum_{a \ne x} \frac{1}{|a - x| + 1} \;=\; H_{x+1} + H_{n-x} - 2 \;\le\; 2 \ln n ,$$

where $H_k = 1 + \frac12 + \dots + \frac1k$ is the harmonic number. So a random BST serves $m$ searches at expected cost at most $m(1 + 2\ln n) \approx m(1 + 1.39 \log_2 n)$.

::: todo
- With uniform weights, the expected depth of $x$ in a random treap is $H_{x+1} + H_{n-x} - 2$. This is a short corollary of the formalized ancestor probability.
- Inserting the keys in a given order into an empty BST, without rebalancing, builds the treap whose priorities are the positions in that order.

Roadmap [entry 9](https://github.com/slef/lean-bst/blob/main/ROADMAP.md#9-random-search-trees). The Isabelle formalization of @eberl2020 covers similar ground.
:::

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
