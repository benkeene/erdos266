/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import Erdos266.SlopeLemma

/-!
# The lattice lemma (Lemma 7.2 of [KoTa24])

For every `d` there are constants `0 < ε ≤ 1 ≤ D` such that whenever
`4d·M ≤ N`: every point `x ∈ ℝ^d` within the box
`ε·M/N^(i+2)` (in the `i`-th coordinate, 0-indexed) of the anchor
`s_i = ∑_{j<d} f_{i+1}((j+1)N)` can be approximated by shifting the sample
points: there are integers `|n_j| ≤ M` with

  `|x_i - ∑_j f_{i+1}((j+1)N + n_j)| ≤ D·(1/N^(i+2) + M²/N^(i+3))`.

This is the engine of the construction: it lets one block of the sequence
steer all `d` first coordinates of the running sums at once.

The proof composes:

* the slope lemma: shifting a sample by `n_j` moves the `i`-th sum by
  `(i+1)·n_j/((j+1)N)^(i+2)` up to quadratic error — so up to error the
  reachable displacements form the image of `[-M,M]^d ∩ ℤ^d` under an
  explicit Vandermonde-type linear map;
* integrality: with `W i j = (j+1)^(d-1-i)` (an integer matrix with nonzero
  Vandermonde determinant `±v`), the substitution `n_j = (j+1)^(d+1)·m_j`
  turns the displacement map into `W`, and `adjugate W` produces an exact
  integer preimage of any vector in `v·ℤ^d`;
* rounding **toward zero** to the lattice `v·ℤ` in each coordinate, which
  both stays within the target box (so the preimage satisfies `|n_j| ≤ M`)
  and costs at most `v` per coordinate — the `D·1/N^(i+2)` term.

No operator norms and no matrix inverses: all bounds come from
`abs_mulVec_le` (a row-sum estimate) and the adjugate identity.
-/

namespace Erdos266

open Finset Matrix

/-- Round `u` toward zero to a multiple of `c`: the multiple is within `c`
of `u` and no larger than `u` in absolute value. -/
lemma exists_round_toward_zero (u : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ z : ℤ, |c * z - u| ≤ c ∧ c * |(z : ℝ)| ≤ |u| := by
  rcases le_or_gt 0 u with hu | hu
  · refine ⟨⌊u / c⌋, ?_, ?_⟩
    · have h1 : (⌊u / c⌋ : ℝ) ≤ u / c := Int.floor_le _
      have h2 : u / c < ⌊u / c⌋ + 1 := Int.lt_floor_add_one _
      have h1' : c * (⌊u / c⌋ : ℝ) ≤ u := by
        have := mul_le_mul_of_nonneg_left h1 hc.le
        rwa [mul_div_cancel₀ u hc.ne'] at this
      have h2' : u < c * (⌊u / c⌋ : ℝ) + c := by
        have := mul_lt_mul_of_pos_left h2 hc
        rw [mul_add, mul_one, mul_div_cancel₀ u hc.ne'] at this
        linarith
      rw [abs_le]
      constructor <;> linarith
    · have h0 : (0 : ℤ) ≤ ⌊u / c⌋ := Int.floor_nonneg.mpr (div_nonneg hu hc.le)
      have h1 : (⌊u / c⌋ : ℝ) ≤ u / c := Int.floor_le _
      have h1' : c * (⌊u / c⌋ : ℝ) ≤ u := by
        have := mul_le_mul_of_nonneg_left h1 hc.le
        rwa [mul_div_cancel₀ u hc.ne'] at this
      rw [abs_of_nonneg (show (0:ℝ) ≤ (⌊u / c⌋ : ℝ) by exact_mod_cast h0),
        abs_of_nonneg hu]
      exact h1'
  · refine ⟨⌈u / c⌉, ?_, ?_⟩
    · have h1 : (u / c : ℝ) ≤ ⌈u / c⌉ := Int.le_ceil _
      have h2 : (⌈u / c⌉ : ℝ) < u / c + 1 := Int.ceil_lt_add_one _
      have h1' : u ≤ c * (⌈u / c⌉ : ℝ) := by
        have := mul_le_mul_of_nonneg_left h1 hc.le
        rwa [mul_div_cancel₀ u hc.ne'] at this
      have h2' : c * (⌈u / c⌉ : ℝ) < u + c := by
        have := mul_lt_mul_of_pos_left h2 hc
        rw [mul_add, mul_one, mul_div_cancel₀ u hc.ne'] at this
        linarith
      rw [abs_le]
      constructor <;> linarith
    · have h0 : ⌈u / c⌉ ≤ 0 :=
        Int.ceil_nonpos.mpr (div_nonpos_of_nonpos_of_nonneg hu.le hc.le)
      have h1 : (u / c : ℝ) ≤ ⌈u / c⌉ := Int.le_ceil _
      have h1' : u ≤ c * (⌈u / c⌉ : ℝ) := by
        have := mul_le_mul_of_nonneg_left h1 hc.le
        rwa [mul_div_cancel₀ u hc.ne'] at this
      rw [abs_of_nonpos (show (⌈u / c⌉ : ℝ) ≤ 0 by exact_mod_cast h0),
        abs_of_neg hu]
      linarith [mul_le_mul_of_nonneg_left
        (show -(⌈u/c⌉ : ℝ) ≤ -(⌈u/c⌉ : ℝ) from le_rfl) hc.le]

/-- Row-sum bound for an integer matrix acting on a bounded integer vector,
with the bound in `ℝ`. -/
lemma abs_mulVec_le {d : ℕ} (B : Matrix (Fin d) (Fin d) ℤ) (z : Fin d → ℤ)
    {zb : ℝ} (hz : ∀ j, |(z j : ℝ)| ≤ zb) (i : Fin d) :
    |((B.mulVec z i : ℤ) : ℝ)|
      ≤ (∑ p : Fin d × Fin d, |((B p.1 p.2 : ℤ) : ℝ)|) * zb := by
  have hzb : 0 ≤ zb := (abs_nonneg _).trans (hz i)
  have hcast : ((B.mulVec z i : ℤ) : ℝ) = ∑ j, ((B i j : ℤ) : ℝ) * ((z j : ℤ) : ℝ) := by
    rw [Matrix.mulVec, dotProduct]
    push_cast
    rfl
  rw [hcast]
  calc |∑ j, ((B i j : ℤ) : ℝ) * ((z j : ℤ) : ℝ)|
      ≤ ∑ j, |((B i j : ℤ) : ℝ) * ((z j : ℤ) : ℝ)| := abs_sum_le_sum_abs _ _
  _ ≤ ∑ j, |((B i j : ℤ) : ℝ)| * zb := by
      refine sum_le_sum fun j _ => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hz j) (abs_nonneg _)
  _ = (∑ j, |((B i j : ℤ) : ℝ)|) * zb := by rw [sum_mul]
  _ ≤ (∑ p : Fin d × Fin d, |((B p.1 p.2 : ℤ) : ℝ)|) * zb := by
      refine mul_le_mul_of_nonneg_right ?_ hzb
      rw [Fintype.sum_prod_type]
      exact single_le_sum (f := fun i' => ∑ j, |((B i' j : ℤ) : ℝ)|)
        (fun i' _ => by positivity) (mem_univ i)

/-- The integer Vandermonde-type matrix of the lattice argument:
`W i j = (j+1)^(d-1-i)`. -/
def latticeMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℤ :=
  Matrix.of fun i j => ((j : ℤ) + 1) ^ (d - 1 - (i : ℕ))

lemma det_latticeMatrix_ne_zero (d : ℕ) : (latticeMatrix d).det ≠ 0 := by
  classical
  have hW : latticeMatrix d
      = ((Matrix.vandermonde fun i : Fin d => ((i : ℤ) + 1)).transpose).submatrix
          Fin.revPerm id := by
    ext i j
    simp only [latticeMatrix, Matrix.of_apply, Matrix.submatrix_apply,
      Matrix.transpose_apply, Matrix.vandermonde, Fin.revPerm_apply, id_eq,
      Matrix.of_apply, Fin.val_rev]
    congr 1
    omega
  rw [hW, Matrix.det_permute]
  refine mul_ne_zero (Units.ne_zero _) ?_
  rw [Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  have hab' : (a : ℤ) + 1 = (b : ℤ) + 1 := hab
  have : (a : ℕ) = b := by omega
  exact Fin.ext this

set_option maxHeartbeats 3200000 in
-- one long chain of explicit estimates, like `slope_lemma` but bigger
/-- **Lemma 7.2 of [KoTa24]** with existential constants: one block of `d`
shifted samples steers all `d` first coordinates of the running sums into
any target within the `ε`-box, up to the `D`-error box. -/
theorem lattice_lemma (d : ℕ) :
    ∃ ε D : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ D ∧
      ∀ (N M : ℕ), 1 ≤ N → 4 * d * M ≤ N →
      ∀ x : Fin d → ℝ,
        (∀ i : Fin d, |x i - ∑ j : Fin d, f (i.val + 1) (((j.val + 1) * N : ℕ) : ℝ)|
          ≤ ε * M / (N : ℝ) ^ (i.val + 2)) →
        ∃ n : Fin d → ℤ, (∀ j, |n j| ≤ (M : ℤ)) ∧
          ∀ i : Fin d,
            |x i - ∑ j : Fin d, f (i.val + 1) ((((j.val + 1) * N : ℕ) : ℝ) + (n j : ℝ))|
              ≤ D * (1 / (N : ℝ) ^ (i.val + 2) + (M : ℝ) ^ 2 / (N : ℝ) ^ (i.val + 3)) := by
  -- PROOF IN PROGRESS: a complete draft with seven small mechanical errors
  -- (cast shapes, renamed lemmas) is preserved at docs/LatticeLemma-draft.lean.txt;
  -- next session repairs it. The helpers above are fully proved.
  sorry

end Erdos266
