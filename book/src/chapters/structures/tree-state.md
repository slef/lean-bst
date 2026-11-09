# Saving trees in their nodes

The combination of [Chapter 23](combination.html) runs two online BST algorithms in alternating rounds, and every round starts from the same initial tree $T$. At the end of a round, the structure must turn whatever tree the interrupted algorithm left behind back into $T$. A BST cannot keep a second copy of $T$ on the side. Demaine, Iacono, Langerman and Özkan [-@demaine2013] therefore store $T$ inside the tree itself, in the $O(\log n)$ bits of data that every node may carry: their *tree state buffer* [@demaine2013, Section 3].

- [Section 33.1](tree-buffers.html) formalizes the buffer: one data cell per node, indexed by inorder rank, and a finger that walks from cell to cell while another finger rotates the tree. Its headline is the paper's Lemma 9: an inorder scan interleaved with $r$ rotations costs at most $4n + 3r$.
- [Section 33.2](snapshots.html) saves a tree into the cells of its own nodes, at twelve bits per node, and restores it from any tree of the same size. Both take linear time: at most $72n$ to save and $56n$ to load, the paper's Lemma 10.

Most of this chapter is proof machinery. The exception is the node and shared-node layers at the end of [Section 33.1](tree-buffers.html): the combined policy of [Chapter 23](combination.html) carries a shared tree, so their definitions are on the reading paths of the combination theorems. The note at the start of that section says what a reader needs from them.
