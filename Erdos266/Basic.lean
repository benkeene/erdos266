/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import Mathlib

/-!
# The Kovač–Tao construction: development library

This library will carry the formalization of the construction of
Kovač–Tao, *On several irrationality problems for Ahmes series*
(arXiv:2406.17593), Section on Stolarsky's conjecture: a strictly increasing
sequence of positive integers whose shifted Ahmes series `∑ 1/(aₙ + t)` has a
rational sum for every admissible shift `t`.

See `docs/plan.md` for the module plan and current status.  Done so far:
`Glue` (the Erdős-problem statement from the construction), `Enumeration`
(condition (7.1)), `Defs` (partial fractions), `Reduction` (the triangular
induction: rational `f`-sums imply `RationalShifts`).  Remaining: the
construction itself (`SlopeLemma`, `LatticeLemma`, `Growth`, `Algorithm`,
`Convergence`, `Main`).
-/

namespace Erdos266

end Erdos266
