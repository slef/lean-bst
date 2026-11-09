# Bibliographic notes

These notes say where each algorithm of this part comes from, which of its known properties the book formalizes, and which it does not.

## Move-to-root

Move-to-root ([Chapter 17](move-to-root.html)) is the rule of @allen1978. They showed that under independent random requests its expected cost is within a constant factor of the optimal static tree for the request probabilities. @chalermsook2016landscape showed that it is optimal in the key-independent setting of @iacono2005.

## Splay trees

Splay trees ([Chapter 18](splay-trees.html)) are due to @sleator1985, after a preliminary version at STOC 1983. The access lemma and its consequences in [Section 18.2](analysis.html), and the bounds for insertions, deletions, splits and joins in [Section 18.3](beyond.html), are theirs. The sequential access theorem is due to @tarjan1985. @elmasry2004 gave a simpler proof with a better constant, and @kakimura2026 show that the amortized cost per access is at most $5.5$ and that some initial trees need almost $4$; the book's proof uses their potential function. The dynamic finger theorem is due to @cole2000sorting and @cole2000proof.

Several conjectures about splaying remain open. The *traversal conjecture* of @sleator1985 says that splaying the keys of any tree $T$ in the preorder of $T$, starting from any initial tree on the same keys, costs $O(n)$. It is proved when the initial tree is the one whose preorder is accessed [@chaudhuri1993], and for preorders and postorders inserted by splaying into an empty tree [@levy2019preorders]. The *deque conjecture*, stated by @tarjan1985, says that $n$ deque operations cost $O(n)$. Tarjan proved it for output-restricted deques; @sundar1992 proved the bound $O(n\alpha(n))$, and @pettie2008 the bound $O(n\alpha^*(n))$. @lucas1991 related splaying to the union-find problem and proved a special case of the *split conjecture*, on the cost of splitting a splay tree into single nodes. @pettie2010 applies forbidden 0-1 matrices to these questions.

Several works isolate why splaying works. @subramanian1996 and @chalermsook2015tick give general conditions under which a restructuring rule satisfies the access lemma. @georgakopoulos2004 shows that splay trees are competitive with dynamic balanced trees. @levy2019path and @levy2019foundation show that splaying is dynamically optimal if and only if it is approximately monotone, that is, if removing requests from a sequence never increases its cost by more than a constant factor. @albers2002 study randomized splaying.

@chmel2026 proved that splay trees are $O(\log\log n \cdot \log^2\log\log n)$-competitive. This is the first $o(\log n)$ competitive ratio for splaying; it is a 2026 preprint and is not formalized.

The splay analysis has been formalized before, in Isabelle, by @nipkow2019, and the amortized analysis of splay trees and related structures has been automated [@leutgeb2021].

## GreedyASS

The offline greedy algorithm, Greedy Future, was proposed by @lucas1988 and again by @munro2000, who both conjectured that it is dynamically optimal. @demaine2009 found its online form in the geometric view and the simulation that turns it into an online BST ([Chapter 19](greedy-ass.html)). @fox2011 proved an access lemma for it, which gives the working-set bound and static optimality; @goyal2011 showed that it is $O(\log n)$-competitive. The finger bounds of [Section 19.3](greedy-finger.html) to [Section 19.6](greedy-amortized.html) are those of @iacono2016.

Many further properties are known and not formalized. GreedyASS serves deque sequences in nearly linear time [@chalermsook2015deque], pattern-avoiding sequences in nearly linear time [@chalermsook2015pattern; @chalermsook2023matrix; @chalermsook2024sorting], and decomposable sequences within the bound of @goyal2019. @chalermsook2023matrix also settle the postorder traversal conjecture for GreedyASS, and @pareek2024 studies GreedyASS from other initial trees. On the side of lower bounds, Greedy Future is not better than 2-competitive, and its additive gap to the optimum can be $\Omega(m\log\log n)$ [@sadeh2023].

@guo2026 proved that GreedyASS is $2^{O(\sqrt{\log\log n})}$-competitive, the first $o(\log n)$ competitive ratio for it. Like the splay result above, it is a 2026 preprint.

The geometric view also connects BSTs to heaps: @kozma2020 map heap algorithms to BST algorithms on a dual sequence, and obtain the smooth heap as the counterpart of Greedy.

## Tango trees and other $O(\log\log n)$-competitive trees

Tango trees ([Chapter 20](tango-trees.html)) are due to @demaine2007, first presented at FOCS 2004. The variant with linear startup in [Section 20.3](tango-linear.html) is the one the combination needs.

Several later trees reach the same ratio with other properties. Multi-splay trees [@wang2006] also keep $O(\log n)$ amortized cost per access. Chain-splay trees [@georgakopoulos2008] use splaying on the paths of a Tango-like decomposition. Zipper trees [@bose2010] and Poketrees [@kujala2006] add $O(\log n)$ worst-case cost per access. @aladhami2024 implement Tango trees and compare them experimentally with splay and multi-splay trees. @jiang2024 show that, among the algorithms whose cost is charged to Wilber's interleave bound, Tango trees are optimal.

The same ideas apply to other search structures: skip lists and B-trees [@bose2008; @demaine2021], and search trees on trees, where the BST is replaced by a decomposition of a tree [@bose2023; @berendsohn2022].

## Static structures

The dynamic program for the optimal lazy-finger tree ([Chapter 21](optimal-lazy-finger.html)) is Theorem 8 of @bose2016, and the multiple-tree structure ([Chapter 22](multiple-trees.html)) is their Theorem 9. The classical dynamic program for the optimal root-finger tree is that of @knuth1971.

## Combining and deamortizing

The combination of [Chapter 23](combination.html) is from @demaine2013. Their application combines splay trees, multi-splay trees [@wang2006] and layered working-set trees [@bose2012layered], so that one BST has the bounds of all three; that application is not formalized. The deamortization of [Chapter 24](deamortization.html) is from @bose2012. Earlier trees with both good amortized and good worst-case bounds were built one at a time: zipper trees and Poketrees for the $O(\log\log n)$ ratio, and layered working-set trees for the working-set bound in the worst case. The deamortization gives such a version of every online BST algorithm.

[Chapter 25](combined-finger.html) formalizes Theorem 4.3 of @iacono2016, which applies both transformations to GreedyASS and Tango trees.

## Other algorithms

PopTrees [@iacono2026] are weight-balanced trees that, on long enough sequences, are within a constant factor of the best offline execution that keeps the same balance invariant: dynamic optimality within a restricted class of trees. It is a 2026 preprint. @blum2003 showed that, if computation between requests is free and only searches are charged, an online BST can be dynamically search-optimal.
