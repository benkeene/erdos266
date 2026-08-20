# Erdős problem #266 — a Lean formalization of the Kovač–Tao disproof of Stolarsky's conjecture

**Status: complete.**  Both theorems are fully proved; the only `sorry`s in
the repository are the two deliberate holes in `Challenge.lean` (the
Comparator convention), and both compared theorems depend on exactly
`propext`, `Classical.choice` and `Quot.sound`.

## What this is

Stolarsky conjectured (recorded as [Erdős problem #266](https://www.erdosproblems.com/266))
that for every sequence of positive integers $(a_n)$ with $\sum 1/a_n$
convergent, there is an integer $t \ge 1$ such that $\sum 1/(a_n+t)$ is
irrational.  Kovač and Tao disproved this in
[*On several irrationality problems for Ahmes series*](https://arxiv.org/abs/2406.17593),
constructing a strictly increasing sequence of positive integers whose shifted
series all have rational sums.

This repository formalizes that resolution in Lean 4 against
[Mathlib](https://github.com/leanprover-community/mathlib4), in the layout
expected by the [Palomar registry](https://palomar-registry.org/):

- [`Challenge.lean`](Challenge.lean) — the statements of record (with
  deliberate `sorry` holes), adapted from the
  [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
  statement of the problem (Apache 2.0).
- [`Solution.lean`](Solution.lean) — the same statements, to be proved by thin
  bridges into the development library.
- [`Erdos266/`](Erdos266/) — the development library where the construction
  is formalized.
- [`comparator.json`](comparator.json) — the
  [Comparator](https://github.com/leanprover/comparator) configuration naming
  the compared theorems.
- [`formalization.yaml`](formalization.yaml) — metadata, sources, automation
  disclosures, and known limitations.

## Structure of the proof

See `docs/plan.md` for the full module map.  In brief: `Enumeration` (a
growth-bounded enumeration of ℚ), `Defs` (partial fractions via Lagrange
interpolation), `Reduction` (the triangular induction turning rational
`f`-sums into rational shifted sums, with pole bookkeeping), `SlopeLemma`
(Lemma 7.1, by telescoping products — no calculus), `LatticeLemma`
(Lemma 7.2, adjugate-based integer preimages of a Vandermonde system),
`Growth` (the scale sequence $N_k = 2^{k^2}$), `Algorithm`/`Recursion`
(the block construction and its invariant (8.5)), `Convergence`
(extraction of the sequence and the `HasSum`s), `Glue` (the Erdős-problem
statement from the construction).

Remaining steps toward registration: local Comparator run, final review,
Palomar submission, and a PR of the formalization link to
[teorth/erdosproblems](https://github.com/teorth/erdosproblems).

## Building

```
lake exe cache get
lake build
```

## Authorship and the role of AI

The formalization is produced with heavy AI assistance — Claude (Anthropic),
working in Claude Code, is expected to write most of the Lean source — under
the direction and review of the author, who selects the targets, makes the
mathematical decisions, and audits the statements against the sources.  See
`formalization.yaml` for the full disclosure.  The mathematics formalized
here is due to Kovač and Tao; no mathematical novelty is claimed.

## License

Apache 2.0.
