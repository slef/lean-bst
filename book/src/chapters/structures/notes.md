# Bibliographic notes

Most structures of this part were introduced inside proofs about dynamic BSTs, and the book follows those proofs. These notes give the origin of each, and some related structures that the book does not use.

## Treaps and point sets

The treap [@seidel1996] and the Cartesian tree [@vuillemin1980] are the same object, studied for different purposes. The use of treaps in [Chapter 26](treaps.html) is that of @demaine2009: a treap whose priorities are the times of the next touches executes an arborally satisfied point set with one touched node per point. The converse direction, from executions to point sets, is also theirs. The random treaps with weighted priorities, which give the static half of the lazy finger characterization, are Theorem 1 of @bose2016, who attribute the construction to Seidel and Aragon.

## Split trees

The split trees of [Chapter 27](split-trees.html) come from the online simulation of @demaine2009. They rest on an older idea: a search tree in which splitting off $k$ keys costs $O(\log \min(k, n - k))$, so that any sequence of splits that separates $n$ keys costs $O(n)$ in total. Level-linked 2-3 trees [@brown1980] support this kind of finger operation, and @hoffmann1986 used it to sort Jordan sequences in linear time. The library builds its split trees on 2–3–4 trees, the B-trees of order 4 [@bayer1972], and stores them in binary form [@bayer1972symmetric; @guibas1978].

## Prefix sums and weighted trees

Two-dimensional prefix sums are folklore. The weighted search trees of [Chapter 28](prefix-sums.html), with every key $x$ at depth at most $\log_2(W/w_x)$, follow the weighted-median rule of @mehlhorn1975. The biased search trees of @bent1985 reach the same depths in a dynamic setting.

## Simulating fingers

BST deques, tendons and finger hands ([Chapter 29](finger-simulation.html)) are the multi-finger simulation of @demaine2013. Their construction shows that a constant number of persistent fingers can be simulated by one root cursor at a constant factor. The library's version is a reconstruction with explicit constants. @chalermsook2018multi simulate $k$ fingers by one with an $O(\log k)$ overhead, using techniques from the $k$-server problem.

## Replays, pop-tarts and heavy paths

The detours of [Chapter 30](replay.html) appear in the deamortization of @bose2012, in the proof of their Theorem 6. Pop-tarts ([Chapter 31](poptarts.html)) and the heavy-path representation ([Chapter 32](heavy-path-simulation.html)) are from the same paper: pop-tarts from its Section 2, heavy paths from its Section 3. Heavy paths themselves are older. The heavy-path decomposition appears in the dynamic trees of @sleator1983 and in the nearest common ancestor algorithm of @harel1984. Its key property, that a root-to-leaf path crosses $O(\log n)$ light edges, is what keeps the stored depths logarithmic. Weighted versions such as those of the deamortization replace $\log n$ by $\log(W/w_x)$.

## Saving trees in their nodes

Tree buffers and snapshots ([Chapter 33](tree-state.html)) are the tree-state buffer of @demaine2013, Section 3. ComboBST uses them to restore its initial tree at the end of every round without memory outside the tree.
