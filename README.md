# Erdős problem #266 — a Lean formalization of the Kovač–Tao disproof of Stolarsky's conjecture

**Status: complete; registered with Palomar.**  Both main results are
proved, with no unresolved `sorry` in `Solution.lean` or the `Erdos266/`
library; `Challenge.lean` contains two deliberate Comparator placeholders.
Palomar registration
[PALOMAR-2026-08-20-000008](https://palomar-registry.org/) (2026-08-20)
records verification at commit `aa0cd43fb45d4f8a3019bf8925424c06b1e67874`:
Comparator checked both statements, replayed through Lean's kernel and the
independent nanoda kernel, using only `propext`, `Classical.choice` and
`Quot.sound`.

## What this is

Stolarsky conjectured (recorded as [Erdős problem #266](https://www.erdosproblems.com/266))
that for every sequence of positive integers $(a_n)$ with $\sum 1/a_n$
convergent, there is an integer $t \ge 1$ such that $\sum 1/(a_n+t)$ is
irrational.  Kovač and Tao disproved this in
[*On several irrationality problems for Ahmes series*](https://arxiv.org/abs/2406.17593),
constructing a strictly increasing sequence of positive integers whose shifted
series have rational sums for every admissible rational shift.

This repository formalizes that resolution in Lean 4 against
[Mathlib](https://github.com/leanprover-community/mathlib4), in the layout
expected by the [Palomar registry](https://palomar-registry.org/):

- [`Challenge.lean`](Challenge.lean) — the statements of record (with
  deliberate `sorry` holes), adapted from the
  [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
  statement of the problem (Apache 2.0).
- [`Solution.lean`](Solution.lean) — the same statements, proved by thin
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

Palomar registration is complete at the commit identified above.  Remaining
dissemination work: propose proof citations for the corresponding
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
declarations (`erdos_266` and `erdos_266.variants.all_rationals`), and submit
the formalization link to
[teorth/erdosproblems](https://github.com/teorth/erdosproblems).  Independent
human review of the statement correspondence remains welcome.

## Building

```
lake exe cache get
lake build
```

## Authorship and the role of AI

The formalization was produced with heavy AI assistance — Claude (Anthropic),
working in Claude Code, wrote essentially all of the Lean source — under the
direction and review of the author, who selected the target, made the
mathematical decisions, and audited the statements against the sources.  See
`formalization.yaml` for the full disclosure.  The mathematics formalized
here is due to Kovač and Tao; no mathematical novelty is claimed.

## License

Apache 2.0.
