# Erdős problem #266 — a Lean formalization of the Kovač–Tao disproof of Stolarsky's conjecture

**Status: work in progress** (scaffold; nothing is proved yet — the Solution
module contains 2 deliberate `sorry`s and the development library is empty).

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

## Roadmap

1. **Statement-fidelity check** (in progress): the arXiv abstract states the
   final construction for integer shifts $t \in \mathbb{Z}$; the problem page
   and the Formal Conjectures statement record it for all rational
   $t \in \mathbb{Q}$.  Verify against the paper body which form is proved,
   and weaken the second Challenge statement if necessary.  (The first
   compared statement — the negative answer to #266 itself — is implied by
   either form.)
2. Glue: derive `Erdos266.erdos_266` from `Erdos266.erdos_266_rational_shifts`.
3. Formalize the construction, its convergence estimates, and the
   rationality of the shifted sums.
4. Audit: sorry-free, axioms exactly `propext`, `Classical.choice`,
   `Quot.sound`; run Comparator locally.
5. Submit to Palomar and PR the formalization link to
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
