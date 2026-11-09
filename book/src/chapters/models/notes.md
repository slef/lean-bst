# Bibliographic notes

The models of this part come from several papers, each of which fixed the model it needed. The book follows the conventions of the papers it formalizes and proves the correspondences between them in [Chapter 11](equivalence.html).

## Trees, rotations and accesses

Binary search trees and rotations are classical; see @knuth1998 for their history. The rotation distance between two trees on $n$ keys is at most $2n - 2$ [@culik1982], at most $2n - 6$ for $n \ge 11$, and this bound is tight for all large $n$ [@sleator1988]. @pournin2014 gave a combinatorial proof that it is tight for every $n \ge 11$. The library proves the simpler bound $2n$ in [Chapter 3](accesses.html). The rotation graph is Hamiltonian [@lucas1987], and computing the rotation distance is fixed-parameter tractable [@cleary2009]; whether it can be computed in polynomial time is open. For search trees on a tree, which generalize BSTs, the largest rotation distance is $\Theta(n \log n)$ in the worst case [@cardinal2018].

The root-access model, in which each request rotates the requested key to the root, is the model of @wilber1989 and of the splay tree paper [@sleator1985]. Allen and Munro's move-to-root rule [@allen1978] is its simplest algorithm.

## Online algorithms and dynamic optimality

The dynamic optimality conjecture is stated in the splay tree paper [@sleator1985]: splaying is within a constant factor of the best offline execution on every sequence. The surveys of @iacono2013 and of @chalermsook2016landscape describe what is known. @blum2003 showed that a BST that is allowed unlimited computation between accesses can be *dynamically search-optimal*: its search cost, though not its rotation cost, is within a constant factor of the offline optimum.

No polynomial-time algorithm is known that computes the offline optimum of a given sequence, and the problem is not known to be NP-hard.

## The pointer machine and touched regions

The single-cursor pointer machine of [Chapter 6](pointer.html) is the standard BST model of the literature, stated precisely by @demaine2009. Derryberry's thesis [@derryberry2009] compares the variants of this model used in the literature and shows that they agree up to constant factors. The touched-region accounting of [Chapter 7](regions.html) is the one used by @demaine2009 and in most later work on dynamic optimality.

## The geometric view

The geometric view of [Chapter 8](geometry.html) is due to @demaine2009, who showed that BST executions correspond to arborally satisfied point sets, up to constant factors. @derryberry2005 found a closely related formulation independently, in their framework for lower bounds. The PhD theses of @harmon2006 and @kozma2016 develop the geometric view further; the second also covers pattern-avoiding sequences. @kozma2016rectangulations relate BST executions to flips between rectangulations, and @blelloch2023 show that many sorting algorithms correspond to offline BST executions in the geometric view.

## Many fingers and linked searches

Executions with several persistent fingers ([Chapter 9](fingers.html)) are simulated by a single cursor in @demaine2013. @chalermsook2018multi show that the offline optimum with $k$ fingers can be matched by a single root finger with an $O(\log k)$ factor overhead, which is tight, and give randomized online BSTs within a further $(\log k)^{O(1)}$ factor, using techniques from the $k$-server problem. The linked-search model of [Chapter 10](linked-search.html) is the model of the multiple-tree structure of @bose2016, Theorem 9; it is a pointer machine whose memory holds many trees, not a BST.

## How the models agree

The equivalence of the rotation model, the pointer machine and the geometric view, up to constant factors, combines @demaine2009 and @derryberry2009. The constants proved in [Chapter 11](equivalence.html) are the library's own.
