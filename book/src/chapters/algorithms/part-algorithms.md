# Adaptive algorithms

Part IV describes the algorithms that adapt to the requests. The classical trees of [Part III](part-classical.html), which do not, are the baseline they improve on. Each chapter defines an algorithm and then states the bounds it satisfies. The definitions of [Part I](part-models.html), what an [online algorithm](online.html#online-algorithms) is and what it pays, and the benchmarks of [Part II](part-bounds.html) are fixed beforehand, so every theorem here is a statement about a specific algorithm in a model already explained. The map in the [introduction to Part II](part-bounds.html#a-map-of-the-bounds) shows which benchmark each algorithm meets.

An algorithm with several analyses is one chapter, with one section per analysis. The first section defines the algorithm and the later ones prove its bounds. The headline results are stated at the top of the section that proves them, and [Checking a result](checking.html) lists them all.

## The algorithms

| Chapter | Algorithm | Model | What the library proves |
|---|---|---|---|
| {{num:move-to-root}} | [Move-to-root](move-to-root.html) | rotations | Each request is a legal access with fewer than $n$ rotations. No amortized bound. |
| {{num:splay-trees}} | [Splay trees](splay-trees.html) | rotations, pointer machine | Theorems 1–5 of Sleator and Tarjan: $O(\log n)$ amortized cost, static optimality, static finger, working set, and a bound that charges each access the smallest of the three. Updates in $O(\log n)$ amortized time, and linear-time sequential access. |
| {{num:greedy-ass}} | [GreedyASS](greedy-ass.html) | geometric, then rotations | Each row is the unique smallest legal one. Every online geometric algorithm is an online BST algorithm at a constant factor, so GreedyASS is one. It costs $O(\mathrm{LF}^* + n)$: it is competitive with the best lazy-finger tree, and has the weighted dynamic finger and dynamic finger bounds. |
| {{num:tango-trees}} | [Tango trees](tango-trees.html) | rotations | $O(\log\log n)$-competitive with the offline optimum, with an $O(n\log\log n)$ startup term; a bottom-up variant has a linear startup term. |
| {{num:optimal-lazy-finger}} | [Optimal lazy-finger tree](optimal-lazy-finger.html) | static tree, offline | A dynamic program returns a tree whose lazy-finger cost is exactly $\mathrm{LF}^*$, with work $4m + 64(n+1)^3$. |
| {{num:multiple-trees}} | [Multiple trees](multiple-trees.html) | linked searches, not a BST | Within $O(\log n/\log c)$ of the conditional-entropy benchmark $m(1+H)$, in $O(nc)$ words. |
| {{num:combination}} | [Combining search trees](combination.html) | pointer machine | Two online algorithms with well-behaved charges combine into one online BST, within a constant factor of the cheaper charge on every window, plus an additive overhead; also for finite families. |
| {{num:deamortization}} | [Deamortization](deamortization.html) | pointer machine | Every online rotation algorithm becomes one with $O(\log n)$ worst-case cost per access and the same total cost up to a constant factor. A deamortized splay tree keeps splaying's bounds. |
| {{num:combined-finger}} | [All the finger bounds at once](combined-finger.html) | pointer machine | GreedyASS and Tango, combined and deamortized: one online BST with the weighted dynamic finger bound, $O(\log\log n)$-competitive, with $O(\log n)$ worst-case cost per access. |

The last three chapters are transformations rather than algorithms. They take online BST algorithms as input and return one, and [Chapter 25](combined-finger.html) applies both to GreedyASS and Tango.

## What each chapter uses

The splay-tree chapter needs only Part I and the benchmarks of [Chapter 12](bounds.html). The others draw on more of the book.

- **GreedyASS** is defined in the geometric view of [Chapter 8](geometry.html). Turning it into a BST uses treaps ([Chapter 26](treaps.html)) and split trees ([Chapter 27](split-trees.html)), and its finger bounds are stated with the lazy-finger costs of [Chapter 13](lazy-finger.html).
- **Tango trees** charge their work to Wilber's interleave bound ([Chapter 15](wilber.html)).
- **The optimal lazy-finger tree** and **multiple trees** answer the questions of [Chapter 13](lazy-finger.html) and [Chapter 16](conditional-entropy.html). They use the prefix sums and weighted search trees of [Chapter 28](prefix-sums.html), and multiple trees run in the linked-search model of [Chapter 10](linked-search.html).
- **Combining** and **deamortization** produce pointer-machine executions ([Chapter 6](pointer.html)) and multi-finger programs ([Chapter 9](fingers.html)). Their proofs use most of [Part V](part-structures.html): the finger simulation of [Chapter 29](finger-simulation.html), the replay tools of [Chapter 30](replay.html), and, for deamortization, the pop-tarts and heavy paths of [Chapter 31](poptarts.html) and [Chapter 32](heavy-path-simulation.html), and for combining, the saved trees of [Chapter 33](tree-state.html).
