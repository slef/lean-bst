# Literature survey: binary search trees

This survey lists the research literature on binary search trees, grouped by topic, and compares it with the book "Binary Search Trees in Lean" (`book/`) as of November 2026. It was written with the bibliography (`book/src/bibliography.json`) and the bibliographic notes that end each part of the book.

For each result the tables give:

- **Key**: the entry in `book/src/bibliography.json`. Results listed without a key are not in the bibliography; their identifier is given instead, checked against Crossref, DataCite or arxiv.org.
- **In the book**: where it appears. Chapter numbers are those of the current build (Part I: 1–11, Part II: 12–16, Part III: 17–25, Part IV: 26–33), with the page slug. "Notes" means it is only cited in a part's bibliographic notes. "Classical branch" means it belongs to the "Classical search trees" part being written on the branch `book-classical`.
- **Recommendation**: **core** (should get a chapter or a section), **notes** (cite in the notes, no formal treatment needed), or **out of scope**.

Every DOI and arXiv identifier in the bibliography was resolved and its title compared with the entry. The method and the few entries without a verifiable link are listed at the end.

## Summary: what the book is missing

The book covers the theory behind its formalized papers well: splay trees, Wilber's first bound, Tango, the geometric view and GreedyASS, the lazy finger, combining and deamortization. The main gaps, in order of importance:

1. **The 2026 competitive ratios.** Splay trees are $O(\log\log n \cdot \log^2\log\log n)$-competitive [`chmel2026`], GreedyASS is $2^{O(\sqrt{\log\log n})}$-competitive [`guo2026`], and PopTrees are dynamically optimal among weight-balanced trees [`iacono2026`]. These are the first $o(\log n)$ ratios for the two classical candidates for dynamic optimality. All three are recent preprints. The splay result is already roadmap entry 2 and a dashed arrow on the map of the bounds. Recommendation: core, once the proofs have been refereed. A section in each of the splay and GreedyASS chapters, and a short chapter for PopTrees.
2. **Lower bounds beyond Wilber's first bound.** The book proves only the interleave bound. Missing: Wilber's second (funnel) bound [`wilber1989`], the independent rectangle bound and SIGNED Greedy [`demaine2009`], the result that the funnel bound dominates the interleave bound [`lecomte2020`], and the results showing that the interleave bound cannot certify a ratio much below $\log\log n$ [`chalermsook2023wilber`, `jiang2024`]. Recommendation: core, as a Part II chapter "Other lower bounds". The independent rectangle bound fits the geometric view of Chapter 8 directly.
3. **The access lemma beyond splaying.** GreedyASS satisfies an access lemma, and so has the working-set bound and static optimality [`fox2011`]. General conditions for the access lemma are in [`subramanian1996`, `chalermsook2015tick`]. The book proves the finger bounds of GreedyASS but not its working-set bound, so the map of the bounds has no arrow from GreedyASS to WS. Recommendation: core, as a section of the GreedyASS chapter.
4. **Easy sequences and open conjectures.** The traversal, deque and split conjectures, the theorem that the offline optimum is $O(1)$ amortized on pattern-avoiding sequences [`berendsohn2024`], and the partial results for splay and Greedy. None is in the book. Recommendation: core, as a Part II section "Easy sequences" stating the conjectures and the known bounds, possibly with the formalized special cases that are short, such as output-restricted deques.
5. **The dynamic finger theorem for splay trees** [`cole2000sorting`, `cole2000proof`]. It is mentioned, but its proof is long. The book proves the dynamic finger bound for GreedyASS instead. Recommendation: notes, unless a shorter proof is found.
6. **Key-independent optimality** [`iacono2005`]: equivalent to the working-set bound. The short proof would complete the bounds chapter, and the deamortization chapter lists it as not formalized. Recommendation: core, as a section of Chapter 12.
7. **Multi-splay trees** [`wang2006`]: an $O(\log\log n)$-competitive tree with $O(\log n)$ amortized cost, used by the combination's application. Recommendation: core, as a section next to Tango.
8. **Prior formalizations** [`nipkow2019`, `leutgeb2021`]: the splay analysis is verified in Isabelle, and its amortized analysis has been automated. Recommendation: notes, and a sentence in the preface or Appendix A.

The classical, non-adaptive material (optimal static trees, balanced trees, random trees, rotation distance) is the subject of the branch `book-classical`; its bibliography entries are included here, and its notes page is `book/src/chapters/classical/notes.md`.

## 1. Surveys and theses

| Result | Key | In the book | Recommendation |
|---|---|---|---|
| Survey of the dynamic optimality conjecture | `iacono2013` | Notes I, II | notes |
| History of distribution-sensitive data structures | `bose2013` | Notes II | notes |
| The landscape of bounds for BSTs: new properties, multiple lazy fingers, move-to-root key-independently optimal | `chalermsook2016landscape` | Notes I, II, III | notes |
| Kozma's thesis: rectangles, patterns, the landscape | `kozma2016` | Notes I | notes |
| Harmon's thesis: the geometric view | `harmon2006` | Notes I | notes |
| Derryberry's thesis: models compared, multi-splay, skip-splay | `derryberry2009` | Preface, Notes I | notes |
| Knuth, TAOCP vol. 3; Mehlhorn, Data Structures and Algorithms 1 | `knuth1998`, `mehlhorn1984` | Notes I, classical notes | notes |

## 2. Models

| Result | Key | In the book | Recommendation |
|---|---|---|---|
| Root-access rotation model; dynamic optimality conjecture | `sleator1985`, `wilber1989` | Ch. 3 `accesses`, Ch. 5 `online` | covered |
| Pointer machine and touched regions | `wilber1989`, `demaine2009` | Ch. 6 `pointer`, Ch. 7 `regions` | covered |
| Comparison of BST models | `derryberry2009` | Ch. 11 `equivalence` | covered |
| Geometric view: arborally satisfied sets | `demaine2009` | Ch. 8 `geometry`, Ch. 11 | covered |
| Geometric lower-bound framework found independently | `derryberry2005` | Notes I, II | notes |
| BST executions and rectangulation flips | `kozma2016rectangulations` | Notes I | notes |
| Tree-based sorting algorithms as BST executions | `blelloch2023` | Notes I | notes |
| Multi-finger BSTs: $k$ fingers cost $O(\log k)$ overhead, tight | `chalermsook2018multi` | Notes I, II, IV | core: section in Ch. 9 `fingers` (the book simulates fingers at constant overhead for constant $k$, Ch. 29) |
| Dynamic search-optimality when restructuring is free | `blum2003` | Notes I, III | notes |
| Insertions and deletions in the geometric view | `chalermsook2015deque` | Notes III | notes (classical branch adds the update model, Part I `dictionary`) |
| Computing the offline optimum: no polynomial algorithm known; subexponential constant-factor approximation | `chalermsook2023wilber` | Notes I, II | notes |

Rotation distance, which the classical branch and Part I touch:

| Result | Key | In the book | Recommendation |
|---|---|---|---|
| Rotation distance at most $2n - 2$ | `culik1982` | Notes I, classical notes | notes |
| $2n - 6$, tight for large $n$ | `sleator1988` | Ch. 3 `accesses`, notes | covered (the library proves $2n$); notes for tightness |
| Tight for all $n \ge 11$ | `pournin2014` | Notes I, classical notes | notes |
| Rotation graph is Hamiltonian | `lucas1987` | Notes I, classical notes | notes |
| Rotation distance is fixed-parameter tractable | `cleary2009` | Notes I, classical notes | notes |
| Diameter of tree associahedra is $\Theta(n\log n)$ | `cardinal2018` | Notes I | notes |
| Diameter of caterpillar associahedra | arXiv:2110.12928 (SWAT 2022, doi:10.4230/LIPIcs.SWAT.2022.14) | — | out of scope |
| Rotation distance via flows | arXiv:2409.17905 | — | out of scope |

## 3. Adaptive bounds

| Result | Key | In the book | Recommendation |
|---|---|---|---|
| Balance, static optimality, static finger, working set, fixed-finger unified theorem | `sleator1985` | Ch. 12 `bounds`, Ch. 18 | covered |
| Entropy bounds for static trees | `mehlhorn1975`, `mehlhorn1977` | Ch. 12 | covered (lower bound); classical branch |
| Working set implies static optimality and static finger | `iacono2001` | Ch. 12 | covered |
| Key-independent optimality, equivalent to working set | `iacono2005` | Ch. 24 (listed as not formalized), Notes II | **core**: section in Ch. 12 |
| Dynamic finger theorem for splay trees | `cole2000sorting`, `cole2000proof` | Ch. 12, Ch. 18 (not formalized) | notes (long proof; the bound is proved for GreedyASS) |
| Unified bound, defined and achieved outside the BST model | `iacono2001`, `badoiu2007` | Ch. 12, Notes II | notes; core if a BST achieving it is found |
| Unified bound up to additive terms in a BST: skip-splay, layered working-set trees | `derryberry2009skip`, `bose2012layered` | Notes II, III | notes |
| Group access bounds: beyond the access lemma, with a simulation theorem | `chalermsook2024group` | Notes II | notes; core candidate if the simulation theorem is reused |
| Fresh-finger property | `howat2013` | Notes II | notes |
| Queueish property, the opposite of working set | `iacono2005queaps` | Notes II | notes |
| Lazy finger: characterization, optimal tree by dynamic programming, hierarchy | `bose2016` | Ch. 13, 14, 16, 21, 22 | covered |
| Weighted dynamic finger | `iacono2016` | Ch. 13, 19, 25 | covered |
| Multiple lazy fingers; decomposable sequences | `chalermsook2016landscape`, `goyal2019` | Notes II, III | notes |
| Conditional entropy benchmark and its obstruction | `bose2016` | Ch. 16, 22 | covered |

## 4. Lower bounds

| Result | Key | In the book | Recommendation |
|---|---|---|---|
| Wilber's first (interleave, alternation) bound | `wilber1989` | Ch. 15 `wilber` | covered |
| Wilber's second (funnel) bound | `wilber1989` | Ch. 15 (not formalized) | **core**: Part II chapter "Other lower bounds" |
| Independent rectangle bound; SIGNED Greedy; it subsumes both Wilber bounds | `demaine2009` | Ch. 15 (not formalized), Notes II | **core**: same chapter |
| The funnel bound dominates the interleave bound; $\Theta(\log\log n)$ gap | `lecomte2020` | Ch. 15, Notes II | **core**: same chapter (statement), proof optional |
| The best interleave bound can be $\Omega(\log\log n/\log\log\log n)$ below OPT | `chalermsook2023wilber` | Notes II | notes; core if the chapter above is written |
| Direct-sum theorems; Tango optimal among interleave-charging algorithms | `jiang2024` | Notes II, III | notes |
| Wilber's theorem for unordered trees | `fredman2011` | Notes II | notes |
| Lower bounds for Greedy Future: ratio at least 2, additive gap $\Omega(m\log\log n)$ | `sadeh2023` | Notes III | notes |
| Information-theoretic lower bound for sets of permutations | `chalermsook2015deque` | — | notes |

## 5. Splay trees

| Result | Key | In the book | Recommendation |
|---|---|---|---|
| Splay trees; access lemma; Theorems 1–5; updates | `sleator1985` | Ch. 18 | covered |
| Sequential access (scanning) theorem | `tarjan1985` | Section 18.3 | covered |
| Better constants for sequential access | `elmasry2004`, `kakimura2026` | Section 18.3, Notes III | covered (the library proves $14n$; $5.5n$ is not claimed) |
| Dynamic finger | `cole2000sorting`, `cole2000proof` | not formalized | notes |
| $\tilde O(\log\log n)$-competitive | `chmel2026` | Part II map (dashed), roadmap 2 | **core**, when refereed |
| Traversal conjecture: special cases | `chaudhuri1993`, `levy2019preorders` | Notes III | **core** as statements in an "Easy sequences" section; proofs optional |
| Deque conjecture: $O(n\alpha(n))$, $O(n\alpha^*(n))$; output-restricted deques linear | `sundar1992`, `pettie2008`, `tarjan1985`, `elmasry2004` | Notes III | **core** as statements; the output-restricted case is a candidate for formalization |
| Split conjecture, union-find connection | `lucas1991` | Notes III | notes |
| Forbidden 0-1 matrices applied to splay trees | `pettie2010` | Notes III | notes |
| Why splaying works: general access-lemma conditions | `subramanian1996`, `chalermsook2015tick` | Notes III | **core**: a section generalizing the access lemma of Section 18.2 would serve splay, GreedyASS and multi-splay |
| Splay is dynamically optimal iff approximately monotone | `levy2019path`, `levy2019foundation` | Notes III | notes |
| Splay competitive with dynamic balanced trees | `georgakopoulos2004` | Notes III | notes |
| Randomized splaying | `albers2002` | Notes III | notes |
| Splay-to-root traversal constant | arXiv:2108.05666 | — | out of scope |
| A study on splay trees (regular access bound) | doi:10.1016/j.tcs.2018.12.020, arXiv:1511.03148 | — | out of scope |
| Isabelle formalization of the splay analysis; automated amortized analysis | `nipkow2019`, `leutgeb2021` | Notes III | notes; mention in the preface or Appendix A |
| Splay top trees | doi:10.1137/1.9781611977585.ch28, arXiv:2210.11918 | — | out of scope |

## 6. GreedyASS and the geometric view

| Result | Key | In the book | Recommendation |
|---|---|---|---|
| Greedy Future, offline | `lucas1988`, `munro2000` | Ch. 19 | covered |
| Online Greedy in the geometric view; online simulation | `demaine2009` | Ch. 19, Ch. 26, 27 | covered |
| Access lemma for Greedy: working set, static optimality | `fox2011` | Section 19.2 (not formalized) | **core**: section of Ch. 19 |
| GreedyArb is $O(\log n)$-competitive | `goyal2011` | Notes III | notes |
| Weighted dynamic finger for Greedy | `iacono2016` | Sections 19.3–19.6 | covered |
| Greedy on deques: $O(n\alpha^*(n))$ | `chalermsook2015deque` | Notes III | notes |
| Pattern-avoiding access; traversal conjecture up to small factors | `chalermsook2015pattern` | Notes II, III | **core** (statements, "Easy sequences") |
| Improved pattern-avoidance bounds; postorder traversal settled for Greedy | `chalermsook2023matrix`, `chalermsook2024sorting` | Notes III | notes |
| Offline optimum is $O(1)$ amortized on pattern-avoiding sequences | `berendsohn2024` | Notes II | **core** (statement and its meaning as a barrier) |
| Sorting pattern-avoiding sequences in linear time | `opler2024` | Notes II | notes |
| Extremal functions of acyclic forbidden matrices | doi:10.1137/1.9781611977912.45, arXiv:2306.16365 | — | out of scope |
| Greedy on decomposable sequences: $O(n\log k)$ | `goyal2019` | Notes II, III | notes |
| Greedy from permutation initial trees | `pareek2024` | Notes III | notes |
| Greedy is $2^{O(\sqrt{\log\log n})}$-competitive | `guo2026` | Notes II, III | **core**, when refereed |
| BST–heap duality, smooth heaps | `kozma2020` | Notes III | notes |
| Extended geometric inversions: a potential for Greedy and splay (ESA 2020) | doi:10.4230/LIPIcs.ESA.2020.28 | — | notes candidate; its claims were not checked against the paper |
| Adaptive sorting in the BST model | arXiv:2610.15828 | — | out of scope |

## 7. Tango trees and other $O(\log\log n)$-competitive trees

| Result | Key | In the book | Recommendation |
|---|---|---|---|
| Tango trees | `demaine2007` | Ch. 20 | covered |
| Multi-splay trees | `wang2006` | Ch. 23, 24 (applications not formalized) | **core**: section next to Tango |
| Chain-splay trees | `georgakopoulos2008` | Notes III | notes |
| Zipper trees: $O(\log\log n)$ ratio, $O(\log n)$ worst case | `bose2010` | Notes III | notes (subsumed by Ch. 24 deamortization) |
| Poketrees | `kujala2006` | Notes III | notes |
| Implementation and experiments: Tango, multi-splay, splay | `aladhami2024` | Notes III | notes |
| Tango optimal among interleave-charging algorithms | `jiang2024` | Notes II, III | notes |

## 8. Transformations

| Result | Key | In the book | Recommendation |
|---|---|---|---|
| Combining BSTs (ComboBST); multi-finger simulation; tree-state buffers | `demaine2013` | Ch. 23, 29, 33 | covered |
| Deamortizing BSTs; pop-tarts; heavy-path simulation | `bose2012` | Ch. 24, 30–32 | covered |
| Layered working-set trees: working set in the worst case | `bose2012layered` | Notes III | notes |
| GreedyASS and Tango combined and deamortized (Theorem 4.3) | `iacono2016` | Ch. 25 | covered |
| Heavy-path decomposition | `sleator1983`, `harel1984` | Notes IV | notes |
| Static optimality transformation for other structures | doi:10.1142/S0218195912600084, arXiv:1104.5597 | — | out of scope |

## 9. Other models and generalizations

| Result | Key | In the book | Recommendation |
|---|---|---|---|
| PopTree: dynamically optimal among weight-balanced trees | `iacono2026` | Notes III | **core** candidate, when refereed; fits next to the classical weight-balanced chapter |
| Dynamic optimality for skip lists and B-trees | `bose2008` | Notes II, III | notes |
| Belga B-trees | `demaine2021` | Notes II, III | notes |
| Dynamic optimality in external memory | doi:10.4230/LIPIcs.ITCS.2022.18, arXiv:2201.01742 | — | out of scope |
| Search trees on trees: $O(\log\log n)$-competitive | `bose2023` | Notes III | notes |
| Splay trees on trees; approximately optimal static trees on trees | `berendsohn2022` | Notes III | notes |
| Centroid trees on trees; LP relaxation; succinct representation | doi:10.4230/LIPIcs.ICALP.2023.19; arXiv:2501.17563; arXiv:2609.21236 | — | out of scope |
| Lazy search trees | `sandlund2020` | Notes II | notes |
| Selectable heaps and optimal lazy search trees; lazy B-trees | doi:10.1137/1.9781611977073.78; doi:10.4230/LIPIcs.MFCS.2025.87 | — | out of scope |
| Learning-augmented BSTs | `lin2022` | Notes II | notes |
| Further learning-augmented search structures | arXiv:2211.09251, arXiv:2402.09687, arXiv:2402.10457, arXiv:2411.16030, arXiv:2605.27490, arXiv:2609.32260 | — | out of scope |
| Biased skip lists; skip-list/BST duality | doi:10.1007/s00453-004-1138-6; doi:10.1145/1233341.1233413 | — | out of scope |
| Pure binary finger search trees | doi:10.1137/1.9781611978315.14 | — | notes candidate for the classical branch (finger search) |

## 10. Heaps and working sets beyond BSTs

These follow from the BST theory but are about other data structures. All are out of scope for the book, except the duality itself, which the GreedyASS notes mention [`kozma2020`].

| Result | Identifier |
|---|---|
| Smooth and slim heaps analysed | doi:10.4230/LIPIcs.ICALP.2021.79; doi:10.1145/3708989 (arXiv:2307.02772) |
| Multipass pairing heaps and path-balanced BSTs | doi:10.4230/LIPIcs.ESA.2018.24 |
| Tournament heaps are not dynamically optimal | arXiv:1908.00563 |
| Universally optimal Dijkstra via working-set heaps | doi:10.1109/FOCS61266.2024.00125; doi:10.4230/LIPIcs.ESA.2025.71; doi:10.4230/LIPIcs.ESA.2026.45 |
| Sorting under partial information | doi:10.1007/s00453-026-01387-3; arXiv:2604.12653 |
| Pairing heaps: towards a final analysis; linear potential | doi:10.1109/SFCS.2005.75; doi:10.1007/978-3-319-48749-6_36 |

Concurrent and network variants of self-adjusting trees (CB tree, splay-list, SplayNet, push-down trees, SeedTree, $k$-ary search tree networks) are out of scope.

## 11. Classical search trees

These entries are for the part "Classical search trees" on the branch `book-classical`, whose notes page is `book/src/chapters/classical/notes.md` (not yet listed in `book.json`). The build checks its keys and counts its citations.

| Topic | Keys | Chapter on that branch |
|---|---|---|
| Optimal static trees | `gilbert1959`, `knuth1971`, `yao1980`, `hu1971`, `garsia1977`, `mehlhorn1975`, `mehlhorn1977`, `larmore1987` | `static-trees` |
| Weighted and dynamic weighted trees | `mehlhorn1979`, `bent1985` | `static-trees` |
| AVL, red-black and relatives | `adelson1962`, `bayer1972symmetric`, `bayer1972`, `guibas1978`, `olivie1982`, `andersson1993` | `rank-balanced` |
| $O(1)$ rotations and amortized rebalancing | `tarjan1983`, `huddleston1982` | `rank-balanced` |
| Rank-balanced and WAVL trees; deletion without rebalancing | `haeupler2015`, `sen2016` | `rank-balanced` |
| BB[α] trees | `nievergelt1973`, `blum1980` | `weight-balanced` |
| Partial rebuilding, scapegoat trees | `andersson1989`, `galperin1993` | `weight-balanced` |
| Day–Stout–Warren rebuilding | `day1976`, `stout1986` | `weight-balanced` |
| Random BSTs and their height | `hibbard1962`, `pittel1984`, `devroye1986`, `reed2003`, `drmota2003` | `random-trees` |
| Treaps, Cartesian trees, randomized BSTs | `seidel1996`, `vuillemin1980`, `martinez1998` | `random-trees` |
| Skip lists, zip trees, zip-zip trees | `pugh1990`, `tarjan2021`, `gila2026` | `random-trees` |
| Level-linked trees and finger search | `brown1980`, `huddleston1982`, `hoffmann1986` | `dictionary` (Part I) |
| Rotation distance | `culik1982`, `sleator1988`, `pournin2014`, `lucas1987`, `cleary2009` | Part I notes |
| Move-to-root | `allen1978` | Ch. 17 (already) |
| Textbooks | `knuth1998`, `mehlhorn1984` | all |

## Method

Entries were collected from the formalized papers, the classical literature, and searches of arXiv, Crossref and DataCite for the topics above (DBLP was not reachable from the build machine). For every DOI, the Crossref or DataCite record was fetched and its title and first author compared with the entry. For every arXiv identifier, the arxiv.org abstract page was fetched and its title compared. The newest preprints (`chmel2026`, `guo2026`, `iacono2026`, `kakimura2026`) were also checked against their abstracts.

Entries without a verifiable DOI or arXiv link (the reference is given without a link):

- `lucas1988` (Rutgers technical report), `derryberry2005` (CMU technical report; report number not verified), `harmon2006` (MIT thesis; no handle verified).
- `iacono2001` and `bose2008` (SODA 2001 and 2008, which have no registered DOIs), and `pettie2008` (SODA 2008; linked to its arXiv version only).
- `adelson1962` (Soviet Mathematics Doklady), `day1976` (The Computer Journal; the DOI of the issue section, 10.1093/comjnl/19.4.360, is titled "Algorithms supplement" and was not used), `knuth1998` (book).
- `galperin1993` and `derryberry2009` link to the authors' PDF instead of a DOI.
- `lin2022` (ICML 2022) links to arXiv only; PMLR has no DOIs.
