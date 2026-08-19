/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import Mathlib

/-!
# Glue: the negative answer to Erdős #266 from the rational-shifts construction

Kovač–Tao's Theorem 2.11 produces a strictly increasing sequence of positive
integers whose shifted Ahmes series `∑ 1/(aₙ + t)` has a rational sum for
every admissible rational shift `t`.  This file derives from any such
sequence the negative answer to Stolarsky's conjecture as recorded by
Erdős–Graham: it is not the case that every positive sequence with summable
reciprocals admits an integer shift `t ≥ 1` making the shifted sum
irrational.

The two steps are bookkeeping:

* positivity of the sequence rules out the excluded shifts `-aₙ` for every
  nonnegative rational `t`;
* the shift `t = 0` gives summability of the unshifted series, and any
  integer shift `t ≥ 1` gives a rational value for the shifted series,
  contradicting its claimed irrationality.
-/

namespace Erdos266

/-- The property produced by the Kovač–Tao construction (Theorem 2.11 of
[KoTa24]): every admissible rational shift of the Ahmes series of `a` has a
rational sum. -/
def RationalShifts (a : ℕ → ℕ) : Prop :=
  ∀ t : ℚ, (¬ ∃ n : ℕ, t = -(a n)) →
    ∃ q : ℚ, HasSum (fun n : ℕ => ((1 : ℝ) / ((a n) + t))) q

/-- A sequence of positive integers admits no rational shift equal to `-aₙ`
for nonnegative rational `t`. -/
theorem not_neg_shift {a : ℕ → ℕ} (hpos : ∀ n, 1 ≤ a n) {t : ℚ} (ht : 0 ≤ t) :
    ¬ ∃ n : ℕ, t = -(a n) := by
  rintro ⟨n, rfl⟩
  have h1 : (1 : ℚ) ≤ (a n : ℚ) := by exact_mod_cast hpos n
  linarith

/-- From any strictly increasing positive sequence with the rational-shifts
property, the negative answer to Erdős problem #266 follows. -/
theorem erdos_266_of_rationalShifts
    (h : ∃ a : ℕ → ℕ, StrictMono a ∧ a 0 ≥ 1 ∧ RationalShifts a) :
    ¬ ∀ (a : ℕ → ℕ), ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·) →
      ∃ t ≥ (1 : ℕ), Irrational <| ∑' n, (1 : ℝ) / ((a n) + t)) := by
  rintro hall
  obtain ⟨a, hmono, h0, hrat⟩ := h
  have hpos : ∀ n, 1 ≤ a n := fun n => h0.trans (hmono.monotone (Nat.zero_le n))
  -- summability of the unshifted series, from the shift `t = 0`
  obtain ⟨q0, hq0⟩ := hrat 0 (not_neg_shift hpos le_rfl)
  have hsum : Summable ((1 : ℝ) / a ·) := by
    have := hq0.summable
    simpa using this
  -- the claimed irrationalizing integer shift
  obtain ⟨t, ht1, hirr⟩ := hall a ⟨hpos, hsum⟩
  -- but that shift has a rational sum
  obtain ⟨q, hq⟩ := hrat t (not_neg_shift hpos (by positivity))
  have hfun : (fun n : ℕ => (1 : ℝ) / ((a n) + ((t : ℚ) : ℝ)))
      = fun n : ℕ => (1 : ℝ) / ((a n) + (t : ℝ)) := by
    push_cast
    rfl
  have htsum : ∑' n, (1 : ℝ) / ((a n) + (t : ℝ)) = (q : ℝ) := by
    rw [← hfun]
    exact hq.tsum_eq
  exact Rat.not_irrational q (htsum ▸ hirr)

end Erdos266
