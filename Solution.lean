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

**Status: work in progress.**  The bridges currently contain `sorry` and the
development library is being built; nothing may be submitted to Palomar until
this module is sorry-free and depends only on `propext`, `Classical.choice`
and `Quot.sound`.
-/

namespace Erdos266

/-- **Erdős problem #266 / Stolarsky's conjecture, disproved** (Kovač–Tao). -/
theorem erdos_266 :
    ¬ ∀ (a : ℕ → ℕ), ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·) →
      ∃ t ≥ (1 : ℕ), Irrational <| ∑' n, (1 : ℝ) / ((a n) + t)) := by
  sorry

/-- **The Kovač–Tao construction.** -/
theorem erdos_266_rational_shifts :
    ∃ a : ℕ → ℕ, StrictMono a ∧ a 0 ≥ 1 ∧
      (∀ t : ℚ, (¬ ∃ n : ℕ, t = -(a n)) →
        (∃ q : ℚ, HasSum (fun n : ℕ => ((1 : ℝ) / ((a n) + t))) q)) := by
  sorry

end Erdos266
