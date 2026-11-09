# Pop-tarts

A *pop-tart*, in the terms of Bose, Collette, Fagerberg and Langerman [-@bose2012], is a binary search tree that implements a stack. Nodes are pushed in decreasing key order as the new root, and popped from the root. Between operations the tree may rebalance itself with finger moves and rotations, and the finger must end at the root again. The leaves of the stack carry weights. A pop-tart is *good* if push and pop take $O(1)$ amortized and $O(\log n)$ worst-case time, and *crazy good* if moreover every leaf of weight $w$ is at depth $O(\log(W/w))$, where $W$ is the total weight.

- [Section 31.1](pop-tarts.html) sets up the common vocabulary: weighted trees, slots and crumbs. It proves the paper's Lemmas 1–3 for the *Vanilla* pop-tart, which never rebalances, and the *Cherry* pop-tart, a 2–4 tree laid out along the right spine. It also defines located slots and mirrored pop-tarts, which the heavy paths use.
- [Section 31.2](chocolate.html) proves the paper's Lemma 4 for the *Chocolate* pop-tart, which is crazy good for arbitrary weights, with explicit constants. It adds two refinements: operations that can be interrupted after any instruction with bounded depths, and replacement of the top slot.

The Chocolate pop-tart is what the deamortization uses. Its heavy paths ([Chapter 32](heavy-path-simulation.html)) are stored as pairs of Chocolate pop-tarts. Cherry pop-tarts are used nowhere else, as in the paper, where they are a warm-up.
