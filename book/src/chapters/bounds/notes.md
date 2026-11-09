# Bibliographic notes

The benchmarks of this part come from the analysis of splay trees and from the search for lower bounds on the offline optimum. These notes give their origins and the main results about them that the book does not formalize. The surveys of @iacono2013 and @bose2013 cover the adaptive bounds in more detail, and @chalermsook2016landscape map many of their relations.

## Adaptive bounds

The working-set, static optimality and static finger bounds of [Chapter 12](bounds.html), and the fixed-finger version of the unified bound, are the theorems of the splay tree paper [@sleator1985]. The entropy lower bound for a fixed tree, which gives static optimality its meaning, goes back to the analysis of nearly optimal trees [@mehlhorn1975]. @iacono2001 showed that the working-set bound implies static optimality and the static finger bound. @iacono2005 introduced key-independent optimality, the expected optimal cost when the keys are relabelled at random, and showed that it is equivalent to the working-set bound.

The dynamic finger bound for splay trees is the theorem of @cole2000sorting and @cole2000proof. The working-set and dynamic finger bounds are incomparable. Iacono's unified bound combines them: a request is cheap if it is close in rank to a recently requested key [@iacono2001; @badoiu2007]. It holds for some data structures that are not BSTs, and it is open whether any BST achieves it. Skip-splay trees [@derryberry2009skip] and layered working-set trees [@bose2012layered] come within additive terms, and the group access bounds of @chalermsook2024group give another route to the same additive guarantee. Variants of the property include the fresh-finger property of @howat2013 and the multi-finger bounds of @chalermsook2018multi. The *queueish* property of priority queues [@iacono2005queaps] is the opposite of the working-set bound: there, an item is cheap to extract if few of the items still present were inserted before it.

## The lazy finger and the weighted dynamic finger

The lazy finger of [Chapter 13](lazy-finger.html) is due to @bose2016. They showed that, unlike the root finger, its optimum is not described by an entropy, derived an asymptotically tight expression for it, and computed the optimal tree by dynamic programming. Expressed with weights on the keys, this cost is the weighted dynamic finger bound, the name used by @iacono2016, who showed that GreedyASS meets it. [Chapter 23](greedy-finger.html) formalizes their proof. The comparison of [Chapter 14](lazy-finger-hierarchy.html) between lazy-finger trees, root-finger trees and dynamic BSTs is Theorem 6 of @bose2016. @chalermsook2016landscape extend the lazy finger to several fingers and obtain a hierarchy of bounds, including a tight $O(n \log d)$ bound for GreedyASS on $d$-decomposable sequences, which @goyal2019 proved independently with a new lower-bound certificate.

## Lower bounds

@wilber1989 gave two lower bounds on the offline optimum, first at FOCS 1986. The first, the interleave or alternation bound, is the subject of [Chapter 15](wilber.html) and the basis of Tango trees. The second, the funnel bound, is not formalized. @fredman2011 extended the first bound to trees that are not ordered.

The geometric view gave further lower bounds. @demaine2009 introduced the independent rectangle bound and showed that it equals, up to constant factors, the cost of a greedy algorithm run on one side of the diagonal at a time (SIGNED Greedy). @derryberry2005 found a closely related framework independently. The independent rectangle bound subsumes both bounds of Wilber.

Recent work compares these bounds. @lecomte2020 showed that the funnel bound is always at least the interleave bound up to constant factors, and that the gap can be $\Theta(\log\log n)$. @chalermsook2023wilber showed that even the best interleave bound over all reference trees can be smaller than the offline optimum by a factor $\Omega(\log\log n / \log\log\log n)$. @jiang2024 proved direct-sum theorems for both bounds of Wilber, and concluded that Tango trees are optimal among the algorithms whose cost is charged to the interleave bound. An analysis that charges an algorithm's cost to the interleave bound therefore cannot prove a competitive ratio much below $\log\log n$.

No polynomial-time algorithm is known that computes the offline optimum within a constant factor. @chalermsook2023wilber give a constant-factor approximation in subexponential time.

## Conditional entropy

The conditional-entropy benchmark of [Chapter 16](conditional-entropy.html), the proof that no BST meets it (Lemma 7), and the multiple-tree structure that meets it within a factor $\log n / \log c$ with $O(nc)$ words of space (Theorem 9) are from @bose2016. The bit-reversal sequence used in the proof is Wilber's standard hard example [@wilber1989].

## Related bounds not covered

Several families of sequences are known to be easy for the offline optimum, and serve as tests for candidate algorithms. @chalermsook2015pattern conjectured that the optimum is linear on sequences that avoid a fixed permutation pattern, and @berendsohn2024 proved it: the amortized optimum is $O(1)$ per request on such sequences. No online algorithm is known to achieve this. Pattern-avoiding sequences can also be sorted in linear time [@opler2024]. The traversal, deque and split conjectures of the algorithms' notes are special cases of the same question.

Other models change the benchmark. Lazy search trees [@sandlund2020] charge only for the order information that the queries need. Learning-augmented search trees use predictions of the access frequencies [@lin2022]. Skip lists and B-trees have their own versions of dynamic optimality [@bose2008; @demaine2021].
