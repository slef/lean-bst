# Combining search trees

Different BST algorithms are good on different sequences, and no single analysis gives all of their bounds at once. Demaine, Iacono, Langerman and Özkan [-@demaine2013] showed that two online BSTs can be combined into one that, on every sequence and on every contiguous window of it, costs at most a constant times the cheaper of the two, plus an additive overhead. Their construction, *ComboBST*, runs the two algorithms in alternating rounds of fixed length on one tree. Each round starts again from a copy of the initial tree saved inside the nodes, and the extra fingers that this needs are simulated by the single cursor of the pointer machine.

The chapter has four sections, which follow the layers of the paper.

- [Section 23.1](combining.html) states the abstract counterpart of the paper's Theorem 3 and its extension to finite families, explains the hypotheses, and does the accounting: well-behaved charges, the counting of rounds, and the window bounds.
- [Section 23.2](combo-workers.html) says what an input algorithm must provide: an *interruptible worker* that can be run one charged unit at a time and stopped anywhere. It turns every online BST algorithm into a worker by replay.
- [Section 23.3](combo-rounds.html) defines the controller, which runs bounded attempts of the two workers in alternating rounds, and proves its accounting.
- [Section 23.4](combo-online.html) turns the controller into one online pointer-machine algorithm, fixed before the first request, and proves its bounds on every prefix and every window.

The theorem has hypotheses. The two input algorithms come as workers with a pointer interpretation, a correctness contract and *well-behaved* charges, and [Section 23.1](combining.html#what-is-assumed-and-what-is-proved) lists them. The library proves them for GreedyASS and for Tango with linear startup, which [Chapter 25](combined-finger.html) combines. The construction draws on [Part V](part-structures.html): the finger simulation of [Chapter 29](finger-simulation.html), the replay tools of [Chapter 30](replay.html), and the saved trees of [Chapter 33](tree-state.html).
