/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import Erdos266.Enumeration

/-!
# The functions `fᵢ` and their partial-fraction decomposition

For `i ≥ 1` the paper defines `fᵢ(x) = 1/∏_{j<i}(x + tⱼ)`, set to `0` at the
poles `x ∈ {-t₀, …, -t_{i-1}}`.  In Lean, `(∏ (x + tⱼ))⁻¹` already vanishes
at the poles (the product is `0` and `(0 : ℝ)⁻¹ = 0`), so the junk-value
convention *is* the paper's convention and no case split is needed.

The partial-fraction coefficients are `m i j = (∏_{k<i, k≠j} (tₖ - tⱼ))⁻¹`;
they are nonzero because the enumeration is injective, and away from the
poles `f i x = ∑_{j<i} m i j · (x + tⱼ)⁻¹` (theorem `f_eq_sum`).  The proof
divides the Lagrange interpolation identity `∑ⱼ basisⱼ = 1` (interpolating
the constant `1` at the nodes `-tⱼ`) by `∏_{k<i}(x + tₖ)`.
-/

namespace Erdos266

open Finset

/-- `f i x = 1/∏_{j<i}(x + tⱼ)`, which is `0` at the poles by the junk-value
convention for `(0 : ℝ)⁻¹`, matching the paper's convention. -/
noncomputable def f (i : ℕ) (x : ℝ) : ℝ :=
  (∏ j ∈ range i, (x + (tSeq j : ℝ)))⁻¹

/-- The partial-fraction coefficients `m i j = (∏_{k<i, k≠j} (tₖ - tⱼ))⁻¹`. -/
def m (i j : ℕ) : ℚ :=
  (∏ k ∈ (range i).erase j, (tSeq k - tSeq j))⁻¹

/-- The coefficients are nonzero (this is where injectivity of the
enumeration is used); in particular the diagonal ones, which the triangular
induction divides by. -/
lemma m_ne_zero (i j : ℕ) : m i j ≠ 0 := by
  refine inv_ne_zero (prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr ?_)
  exact fun h => (mem_erase.mp hk).1 (tSeq_injective h)

/-- `f` at a rational point is the cast of an explicit rational — the
correction terms in the reduction are rational because of this. -/
lemma f_ratCast (i : ℕ) (q : ℚ) :
    f i (q : ℝ) = ((∏ j ∈ range i, (q + tSeq j))⁻¹ : ℚ) := by
  rw [f]
  push_cast
  rfl

/-- The partial-fraction identity away from the poles. -/
theorem f_eq_sum {i : ℕ} (hi : 1 ≤ i) {x : ℝ}
    (hx : ∀ j ∈ range i, x + (tSeq j : ℝ) ≠ 0) :
    f i x = ∑ j ∈ range i, (m i j : ℝ) * (x + (tSeq j : ℝ))⁻¹ := by
  classical
  set v : ℕ → ℝ := fun j => -(tSeq j : ℝ) with hv
  have hinj : Set.InjOn v (range i) := by
    intro p _ q _ hpq
    have : (tSeq p : ℚ) = tSeq q := by
      have := neg_injective hpq
      exact_mod_cast this
    exact tSeq_injective this
  have hne : (range i).Nonempty := ⟨0, mem_range.mpr hi⟩
  -- Lagrange: the basis polynomials at the nodes `-tⱼ` sum to 1
  have hsum := congrArg (Polynomial.eval x) (Lagrange.sum_basis hinj hne)
  rw [Polynomial.eval_finsetSum, Polynomial.eval_one] at hsum
  -- each basis polynomial evaluates to `m i j * ∏_{k≠j}(x + tₖ)`
  have hbasis : ∀ j ∈ range i, (Lagrange.basis (range i) v j).eval x
      = (m i j : ℝ) * ∏ k ∈ (range i).erase j, (x + (tSeq k : ℝ)) := by
    intro j hj
    rw [Lagrange.basis, Polynomial.eval_prod]
    have hfact : ∀ k ∈ (range i).erase j,
        (Lagrange.basisDivisor (v j) (v k)).eval x
          = ((tSeq k - tSeq j : ℚ) : ℝ)⁻¹ * (x + (tSeq k : ℝ)) := by
      intro k _
      have heval : (Lagrange.basisDivisor (v j) (v k)).eval x
          = (v j - v k)⁻¹ * (x - v k) := by
        simp [Lagrange.basisDivisor]
      rw [heval]
      simp only [hv]
      push_cast
      congr 1
      · congr 1
        ring
      · ring
    rw [prod_congr rfl hfact, prod_mul_distrib, prod_inv_distrib]
    congr 1
    rw [m]
    push_cast
    rfl
  rw [sum_congr rfl hbasis] at hsum
  -- divide the identity by the full product
  have step : ∀ j ∈ range i, (m i j : ℝ) * (x + (tSeq j : ℝ))⁻¹
      = ((m i j : ℝ) * ∏ k ∈ (range i).erase j, (x + (tSeq k : ℝ)))
        * (∏ k ∈ range i, (x + (tSeq k : ℝ)))⁻¹ := by
    intro j hj
    have he : (∏ k ∈ (range i).erase j, (x + (tSeq k : ℝ))) ≠ 0 :=
      prod_ne_zero_iff.mpr fun k hk => hx k (mem_of_mem_erase hk)
    rw [← mul_prod_erase _ _ hj, mul_inv]
    field_simp
  rw [sum_congr rfl step, ← sum_mul, hsum, one_mul, f]

end Erdos266
