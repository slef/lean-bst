# Bibliographic notes

These notes say where the results of this part come from. Knuth's volume on sorting and searching [@knuth1998] and Mehlhorn's textbook [@mehlhorn1984] cover most of the classical material in more depth.

## Static trees

[Chapter 18](static-trees.html) studies trees that never change.

The optimal static tree for given access frequencies goes back to @gilbert1959, who computed it by dynamic programming in $O(n^3)$ time, for the case where only the gaps between keys carry weight. @knuth1971 treated the general problem and observed that optimal roots are monotone, which brings the time down to $O(n^2)$. @yao1980 isolated the reason: the quadrangle inequality on the weights implies monotone optimal choices for a whole family of dynamic programs.

When only the gaps carry weight, the problem is that of optimal alphabetic codes. @hu1971 solved it in $O(n \log n)$ time. The algorithm of @garsia1977 computes a tree of the same cost by a simpler procedure, with the same running time.

Near-optimal trees are easier to build. @mehlhorn1975 put the weighted median at the root and recursed, and showed that the resulting tree is within an additive constant of the entropy bound, which no tree can beat by more than a constant factor. @mehlhorn1977 gave the best possible bound on the weighted path length of optimal trees in terms of the entropy. @larmore1987 computed approximately optimal trees in subquadratic time. These entropy bounds are the ones the book proves in [Chapter 13](bounds.html#comparison-with-a-fixed-tree).

Weights can also change. @mehlhorn1979 maintained nearly optimal trees under changing frequencies, and the biased search trees of @bent1985 keep every key $x$ at depth $O(\log(W/w_x))$ under insertions, deletions, joins and splits.

## Rank-balanced trees

[Chapter 19](rank-balanced.html) presents AVL, red-black and WAVL trees as one theory of ranks.

AVL trees are the first balanced search trees [@adelson1962]. @bayer1972symmetric introduced symmetric binary B-trees, the binary form of 2-3-4 trees, which are B-trees of order 4 [@bayer1972]. @guibas1978 recast them with red and black colours and gave a common framework for several balance conditions. The half-balanced trees of @olivie1982 are another formulation of the same idea.

@tarjan1983 showed that red-black trees can be updated with $O(1)$ rotations per insertion or deletion, against $\Theta(\log n)$ in the worst case for AVL deletion. @huddleston1982 proved that the amortized number of rebalancing steps in suitable $(a,b)$-trees is constant, which also gives red-black trees $O(1)$ amortized recolourings. @andersson1993 simplified the case analysis of red-black trees with what are now called AA trees.

@haeupler2015 introduced rank-balanced trees and the WAVL rule. A WAVL tree with no deletions is an AVL tree, it is always a red-black tree, and it uses at most two rotations per update. @sen2016 showed that a tree can skip rebalancing on deletion entirely and still keep its height logarithmic in the number of insertions.

## Weight-balanced trees

[Chapter 20](weight-balanced.html) keeps subtree sizes in proportion.

Trees of bounded balance, BB[α], are due to @nievergelt1973. @blum1980 corrected the range of parameters for which rotations restore the balance, and proved that the average number of rebalancing operations per update is constant.

Partial rebuilding replaces rotations by rebuilding a whole subtree. @andersson1989 used it with simple balance criteria, and the scapegoat trees of @galperin1993 store no balance information in the nodes at all. Both achieve $O(\log n)$ amortized update time.

Rebuilding a subtree into a perfectly balanced one takes linear time and constant extra space. The method of @day1976 was improved by @stout1986; it is now known as the Day–Stout–Warren algorithm. It first turns the tree into a path, a *vine*, and then compresses the vine by rotations.

## Random trees

[Chapter 21](random-trees.html) shows that random insertion orders, treaps and randomized BSTs all draw from one distribution.

@hibbard1962 analysed the BST built by inserting keys in random order, and showed that the expected cost of a search is about $2 \ln n$. The height is larger. @pittel1984 showed that it grows like $c \ln n$ almost surely, and @devroye1986 identified the constant, $c \approx 4.311$. @reed2003 and @drmota2003 determined the next term of the expected height and showed that its variance is bounded.

Treaps are due to Aragon and Seidel; the journal version is @seidel1996. The same trees appear earlier as the Cartesian trees of @vuillemin1980. A treap with random priorities is a random BST, and an update makes fewer than two rotations in expectation. The randomized BSTs of @martinez1998 store subtree sizes instead of priorities and keep the distribution of a random BST after every insertion and deletion. Zip trees [@tarjan2021] are treaps whose ranks are geometric random variables, updated by unzipping and zipping paths instead of rotating; they are isomorphic to the skip lists of @pugh1990. @gila2026 refine them to make the depth smaller and to support biased and persistent variants.

## Insertions and deletions

[Chapter 6](dictionary.html) adds insertions and deletions to the model of Part I. The amortized bounds for splay trees with updates are in @sleator1985. Level-linked trees support finger searches and updates near a finger in time logarithmic in the distance [@brown1980; @huddleston1982], and @hoffmann1986 used them for linear-time Jordan sorting.

## Rotation distance

Every tree on $n$ keys can be turned into every other one with a bounded number of rotations. @culik1982 showed that $2n - 2$ rotations suffice. @sleator1988 improved the bound to $2n - 6$ for $n \ge 11$, and proved, with hyperbolic geometry, that it is tight for all large $n$. @pournin2014 gave a combinatorial proof that it is tight for every $n \ge 11$. The graph of rotations between trees on $n$ keys has a Hamiltonian cycle [@lucas1987]. Computing the rotation distance between two given trees is fixed-parameter tractable in the distance [@cleary2009]; no polynomial-time algorithm is known, and the problem is not known to be NP-hard.
