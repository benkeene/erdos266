# Erdős problem #266 — a Lean formalization of the Kovač–Tao disproof of Stolarsky's conjecture

**Status: complete; registered with Palomar; cited by Formal Conjectures.**
Both main results are proved, with no unresolved `sorry` in `Solution.lean`
or the `Erdos266/` library; `Challenge.lean` contains two deliberate
Comparator placeholders.  Palomar registration
[PALOMAR-2026-08-20-000008 v2](https://palomar-registry.org/entry?id=PALOMAR-2026-08-20-000008&version=2)
(2026-10-12) records verification at commit
`ef01b23804a60669f24b25733f1a2b688084609d` (Lean and Mathlib
`v4.35.0-rc3`): Comparator checked both statements
(`Erdos266.erdos_266`, `Erdos266.erdos_266_rational_shifts`), replayed
through the nanoda and con-ron kernels, using only `propext`,
`Classical.choice` and `Quot.sound`; registry review outcome `neutral`
(not an endorsement), no warnings.  Version 1 (2026-08-20) recorded the
same result at commit `aa0cd43fb45d4f8a3019bf8925424c06b1e67874`.
The [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
project cites this formalization as the proof of
`erdos_266.variants.all_rationals`
([PR #7171](https://github.com/google-deepmind/formal-conjectures/pull/7171),
merged 2026-10-22).

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

Palomar registration is complete at the commit identified above.
Dissemination: the Formal Conjectures proof citation for
`erdos_266.variants.all_rationals` was merged on 2026-10-22
([PR #7171](https://github.com/google-deepmind/formal-conjectures/pull/7171));
the existing citation on `erdos_266` (plby/lean-proofs) was left in place,
the two formalizations being independent.  Still to do: submit the
formalization link to
[teorth/erdosproblems](https://github.com/teorth/erdosproblems).  Independent
human review of the statement correspondence remains welcome.

## Palomar entry and citation

This formalization is hosted on Palomar as
[PALOMAR-2026-08-20-000008 v2](https://palomar-registry.org/entry?id=PALOMAR-2026-08-20-000008&version=2);
the pinned commit is preserved in
https://github.com/PalomarArchive/benkeene--erdos266--5089d7151e9d.
To cite it:
```bibtex
@misc{palomar-2026-08-20-000008-v2,
  author = {{Ben Keene}},
  title = {{Erdős problem #266: the Kovač–Tao disproof of Stolarsky's conjecture}},
  year = {2026},
  howpublished = {Palomar, PALOMAR-2026-08-20-000008 v2},
  url = {https://palomar-registry.org/entry?id=PALOMAR-2026-08-20-000008&version=2},
}
```
Commits on main after `ef01b23` are not part of version 2.

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
