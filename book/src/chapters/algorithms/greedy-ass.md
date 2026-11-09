# GreedyASS

GreedyASS is the greedy algorithm of the geometric view. Lucas [-@lucas1988] and Munro [-@munro2000] proposed it as an offline BST algorithm, *Greedy Future*: to serve a request, touch its search path, then rearrange the path so that the keys requested soonest are nearest the top. Demaine, Harmon, Iacono, Kane and Pătraşcu [-@demaine2009] found that in the geometric view of [Chapter 8](geometry.html) the same rule needs no knowledge of the future, and that every online geometric algorithm can be run as an online BST algorithm at a constant factor. GreedyASS and splay trees are the two main candidates for a dynamically optimal BST.

The chapter has six sections. The first two define GreedyASS and make it an online BST algorithm. The third states its finger bounds, from Iacono and Langerman [-@iacono2016]: it is competitive with the best static tree searched with a lazy finger, and so has the weighted dynamic finger and dynamic finger bounds. The last three prove the theorem behind those bounds.

- [Section 19.1](greedy.html) defines the sweep, proves that it is a legal online geometric algorithm, and that each row it adds is the unique smallest legal row.
- [Section 19.2](simulation.html) turns every online geometric algorithm into an online BST algorithm, with treaps and split trees from [Part V](part-structures.html), and so GreedyASS into a BST.
- [Section 19.3](greedy-finger.html) states Theorems 4.1 and 4.2 and Corollary 1 of Iacono and Langerman, for the geometric algorithm, for the BST, and on the pointer machine.
- [Section 19.4](reference-forest.html) builds the reference tree that a lazy finger walks in, and the forest that a search leaves behind.
- [Section 19.5](greedy-potential.html) defines the colored potential of the proof and proves its local properties.
- [Section 19.6](greedy-amortized.html) pays for each row that GreedyASS adds, and concludes Theorem 3.1, from which the finger bounds follow.

A reader who wants to check the finger bounds needs [Section 19.3](greedy-finger.html) and the definitions it points to. The last three sections are the proof, and each says at its start which of its definitions, if any, the statements need. GreedyASS is one of the two ingredients of [Chapter 25](combined-finger.html).
