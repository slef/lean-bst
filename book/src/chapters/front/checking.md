# Checking a result

You may not want to read the whole book. Perhaps you only want to know whether the library really proves that Tango trees are $O(\log\log n)$-competitive, or that arborally satisfied sets capture the cost of offline BST algorithms. This page is for that.

## What there is to check

Lean checks every proof, so you never need to read one. What Lean cannot check is that a theorem *says what you think it says*. A statement can be technically true and still miss the point: the cost might be counted in the wrong place, or a definition might quietly assume what it should prove. To trust a result, you have to read its statement, every definition the statement mentions, every definition *those* mention, and so on down to standard Lean and Mathlib notions such as lists, natural numbers and $\log_2$.

That set of definitions is usually small. The book computes it from the compiled library: it starts from the statement and follows definition types and bodies, but never proofs. For Tango trees, it is ten definitions: what a tree is, what a rotation, an access and an execution are, and what an online algorithm and its cost are. You do not need to know how Tango trees work.

Two refinements keep the list honest and short:

- **Skips.** Sometimes a definition can be safely ignored. A decidability instance is an example: it only lets Lean compute a test, and any two instances for the same proposition agree, so it cannot change what a definition means. Each skip is listed on the reading list with its reason, so you can disagree.
- **Internal modules.** If a statement used a definition from outside the reading interface, the book could not quote it, and the reading list would link it to the library source instead. No main result does at present.

The axioms behind each proof are listed in [Appendix A](audit.html). All of them are Lean's three standard axioms.

## How to use it

Every chapter or section that proves something opens with a box stating its main result, in English and in Lean. Results marked ★ are *key results*: the ones that the formalized papers announce in their abstracts or introductions. Select one or several results below, or tick the box in a chapter's main-result box. To narrow the selection down to a single result, use its **only this one** button, or open the list of selected results in the bar at the bottom of the page. The selection then follows you through the book:

- the sidebar shows, for each chapter or section, how many definitions you need from it;
- on each page, those definitions are outlined and tagged **needed**;
- a bar at the bottom of the page steps through them in reading order, and can dim everything else.

The reading list at the bottom of this page collects everything in one place.

## The main results

@claims
