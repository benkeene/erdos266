/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene

The two theorem statements below are adapted from the Formal Conjectures
project (https://github.com/google-deepmind/formal-conjectures, file
FormalConjectures/ErdosProblems/266.lean), Copyright 2025 The Formal
Conjectures Authors, Apache 2.0 license.
-/
import Mathlib

/-!
# Erdős problem #266: the Kovač–Tao disproof of Stolarsky's conjecture

This is the statement of record for the Palomar submission.  It states two
theorems and introduces no definitions of its own; every notion used is
Mathlib's.

## The statements

Stolarsky conjectured (recorded as Erdős problem #266, see
[erdosproblems.com/266](https://www.erdosproblems.com/266)) that for every
sequence `a : ℕ → ℕ` of positive integers with `∑ 1/aₙ` convergent, there is
some integer shift `t ≥ 1` for which `∑ 1/(aₙ + t)` is irrational.

Kovač and Tao (*On several irrationality problems for Ahmes series*,
[arXiv:2406.17593](https://arxiv.org/abs/2406.17593)) disproved this:

* `Erdos266.erdos_266` is the negative answer itself — it is **not** the case
  that every such sequence admits an irrationalizing shift.

* `Erdos266.erdos_266_rational_shifts` is the stronger construction behind it:
  there is a strictly monotone sequence of positive integers such that
  `∑ 1/(aₙ + t)` converges to a rational number for **every** admissible
  rational shift `t`.

## How the statements are phrased

* Sequences are `a : ℕ → ℕ`; positivity is `a n ≥ 1` (first theorem) or
  `StrictMono a ∧ a 0 ≥ 1` (second theorem).
* Summability of `∑ 1/aₙ` is Mathlib's `Summable`, for the real-valued
  function `n ↦ (1 : ℝ) / a n` (natural-number coercion into `ℝ`).
* "The sum is rational" is phrased as `∃ q : ℚ, HasSum (…) q`: the series
  converges and its limit is (the real embedding of) a rational number.
  `HasSum` for `ℕ`-indexed real series is unconditional convergence, which
  for these positive-term series agrees with the ordinary sum.
* In the second theorem the shift ranges over `t : ℚ`, excluded only from the
  values `-aₙ` where a term would be undefined.  In Lean, division by zero
  yields zero rather than being undefined, so the exclusion is what makes the
  statement faithful rather than what makes it typecheck.
* `Irrational` is Mathlib's: membership of a real number in the complement of
  the range of `ℚ → ℝ`.

## Provenance and status

The formal statements are those of the Formal Conjectures project (file
`ErdosProblems/266.lean`, adapted here under Apache 2.0: the `@[category]`
attributes are removed and the declarations renamed into the `Erdos266`
namespace; the mathematical content is unchanged).

Nothing here is claimed to be new mathematics: the theorems are due to Kovač
and Tao, and this repository contributes their formalization.  See
`formalization.yaml` and README.md for sources, the role of AI in producing
the development, and known limitations — including one statement-fidelity
point under active verification: the arXiv abstract of [KoTa24] states the
final construction for integer shifts `t ∈ ℤ`, while the paper's full result
as recorded by erdosproblems.com and the Formal Conjectures project covers
all rational shifts `t ∈ ℚ`.  The stronger `ℚ` form is stated here and will
be checked against the paper body before any submission.

The proofs are developed in the `Erdos266` library of this repository and are
compared against these statements by Comparator.  They are to use `propext`,
`Classical.choice` and `Quot.sound` only.
-/

namespace Erdos266

/-- **Erdős problem #266 / Stolarsky's conjecture, disproved** (Kovač–Tao).
It is not the case that for every sequence `a : ℕ → ℕ` of positive integers
with `∑ 1/aₙ` summable there exists an integer `t ≥ 1` making
`∑ 1/(aₙ + t)` irrational. -/
theorem erdos_266 :
    ¬ ∀ (a : ℕ → ℕ), ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·) →
      ∃ t ≥ (1 : ℕ), Irrational <| ∑' n, (1 : ℝ) / ((a n) + t)) := by
  sorry

/-- **The Kovač–Tao construction.**  There is a strictly increasing sequence
of positive integers `a` such that `∑ 1/(aₙ + t)` converges to a rational
number for every rational `t` that avoids the values `-aₙ`. -/
theorem erdos_266_rational_shifts :
    ∃ a : ℕ → ℕ, StrictMono a ∧ a 0 ≥ 1 ∧
      (∀ t : ℚ, (¬ ∃ n : ℕ, t = -(a n)) →
        (∃ q : ℚ, HasSum (fun n : ℕ => ((1 : ℝ) / ((a n) + t))) q)) := by
  sorry

end Erdos266
