/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import Erdos266

/-!
# Solutions to the Challenge

The two declarations of `Challenge.lean`, proved.  Each is a thin bridge to
the corresponding theorem of the `Erdos266` development library.

Both are complete: the construction is `Erdos266.construction_exists`
(the block algorithm of Sections 7–8 of [KoTa24], run through the
reduction `Erdos266.rational_shifts_of_construction`), and the negative
answer to the Erdős problem follows by `Erdos266.erdos_266_of_rationalShifts`.
-/

namespace Erdos266

/-- **The Kovač–Tao construction** (Theorem 2.11 of [KoTa24]). -/
theorem erdos_266_rational_shifts :
    ∃ a : ℕ → ℕ, StrictMono a ∧ a 0 ≥ 1 ∧
      (∀ t : ℚ, (¬ ∃ n : ℕ, t = -(a n)) →
        (∃ q : ℚ, HasSum (fun n : ℕ => ((1 : ℝ) / ((a n) + t))) q)) :=
  rational_shifts_of_construction construction_exists

/-- **Erdős problem #266 / Stolarsky's conjecture, disproved** (Kovač–Tao),
derived from the construction. -/
theorem erdos_266 :
    ¬ ∀ (a : ℕ → ℕ), ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·) →
      ∃ t ≥ (1 : ℕ), Irrational <| ∑' n, (1 : ℝ) / ((a n) + t)) :=
  erdos_266_of_rationalShifts erdos_266_rational_shifts

end Erdos266
