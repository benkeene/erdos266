/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import Erdos266.Defs
import Erdos266.Glue

/-!
# Reduction: from rational `f`-sums to `RationalShifts`

The Kovač–Tao reduction (start of Section 8 of [KoTa24]): if a strictly
increasing sequence of positive integers `a` has `∑ₙ 1/aₙ < ∞` and
`∑ₙ fᵢ(aₙ) ∈ ℚ` for every `i ≥ 1`, then every shifted series
`∑ₙ 1/(aₙ + t)`, `t ∈ ℚ`, has a rational sum — i.e. `RationalShifts a`.

The paper phrases this by inverting the triangular change of variables `U`
on `ℚ^ℕ`; here it is a strong induction on the shift index `j`: the
partial-fraction identity writes `∑ₙ f_{j+1}(aₙ)` as a linear combination
(with rational, nonzero-diagonal coefficients) of the shifted sums for
indices `≤ j`, up to a *finite rational correction* coming from the at most
`j + 1` indices `n` where `aₙ` is a pole of `f_{j+1}` — precisely the
places where the junk-value convention makes the identity fail.  Solving
for the diagonal term completes the induction.

Everything is phrased with Lean's junk values: at a pole both `f` and the
offending shifted term are literally `0`, so all series are well-defined
`HasSum` statements with no side conditions.
-/

namespace Erdos266

open Finset

variable {a : ℕ → ℕ}

/-- Strictly increasing sequences of naturals tend to infinity (as reals). -/
lemma tendsto_cast_atTop (ha : StrictMono a) :
    Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono (fun n => by exact_mod_cast ha.le_apply)
    tendsto_natCast_atTop_atTop

/-- Summability survives a constant shift of the denominators. -/
lemma summable_shift (ha : StrictMono a)
    (hsum : Summable fun n => ((a n : ℝ))⁻¹) (c : ℝ) :
    Summable fun n => ((a n : ℝ) + c)⁻¹ := by
  set N := ⌈2 * |c| + 1⌉₊ with hN
  have hbig : ∀ n : ℕ, N ≤ n → 2 * |c| + 1 ≤ (a n : ℝ) := by
    intro n hn
    calc 2 * |c| + 1 ≤ (N : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ (a n : ℝ) := by exact_mod_cast ha.le_apply
  refine (summable_nat_add_iff N).mp ?_
  change Summable fun n => ((a (n + N) : ℝ) + c)⁻¹
  have hhalf : ∀ n : ℕ, (a (n + N) : ℝ) / 2 ≤ (a (n + N) : ℝ) + c := by
    intro n
    have h1 := hbig (n + N) (Nat.le_add_left N n)
    have h2 : -|c| ≤ c := neg_abs_le c
    nlinarith [abs_nonneg c]
  have hpos : ∀ n : ℕ, 0 < (a (n + N) : ℝ) := by
    intro n
    have h1 := hbig (n + N) (Nat.le_add_left N n)
    nlinarith [abs_nonneg c]
  refine Summable.of_nonneg_of_le
    (fun n => le_of_lt (inv_pos.mpr (lt_of_lt_of_le (half_pos (hpos n)) (hhalf n))))
    (fun n => ?_) ((summable_nat_add_iff N).mpr (hsum.mul_left 2))
  calc ((a (n + N) : ℝ) + c)⁻¹
      ≤ ((a (n + N) : ℝ) / 2)⁻¹ := inv_anti₀ (half_pos (hpos n)) (hhalf n)
  _ = 2 * ((a (n + N) : ℝ))⁻¹ := by
        rw [inv_div, div_eq_mul_inv]

/-- The indices at which `a` hits a pole of `f i` form a finite set. -/
lemma bad_finite (ha : StrictMono a) (i : ℕ) :
    {n : ℕ | ∃ j ∈ range i, (a n : ℚ) + tSeq j = 0}.Finite := by
  have hsub : {n : ℕ | ∃ j ∈ range i, (a n : ℚ) + tSeq j = 0}
      ⊆ ⋃ j ∈ (↑(range i) : Set ℕ), {n : ℕ | (a n : ℚ) + tSeq j = 0} := by
    intro n hn
    obtain ⟨j, hj, hjn⟩ := hn
    exact Set.mem_biUnion (Finset.mem_coe.mpr hj) hjn
  refine Set.Finite.subset (Set.Finite.biUnion (range i).finite_toSet
    fun j _ => ?_) hsub
  refine Set.Subsingleton.finite fun x hx y hy => ?_
  simp only [Set.mem_ofPred_eq] at hx hy
  have hxy : (a x : ℚ) = (a y : ℚ) := by linarith
  exact ha.injective (by exact_mod_cast hxy)

/-- Cast bookkeeping: the shifted term is the cast of an explicit rational. -/
lemma shiftTerm_cast (n k : ℕ) :
    ((a n : ℝ) + (tSeq k : ℝ))⁻¹ = ((((a n : ℚ) + tSeq k)⁻¹ : ℚ) : ℝ) := by
  push_cast
  rfl

/-- Cast bookkeeping: `f i` at `a n` is the cast of an explicit rational. -/
lemma f_cast (i n : ℕ) :
    f i ((a n : ℕ) : ℝ)
      = (((∏ k ∈ range i, ((a n : ℚ) + tSeq k))⁻¹ : ℚ) : ℝ) := by
  have : ((a n : ℕ) : ℝ) = (((a n : ℚ)) : ℝ) := by push_cast; rfl
  rw [this, f_ratCast]

/-- The heart of the reduction: by strong induction on the shift index,
every series `∑ₙ (aₙ + tⱼ)⁻¹` has a rational sum.

(No independent summability hypothesis is needed: the `HasSum` hypotheses on
the `f`-series carry all the required convergence through the induction —
a simplification over the paper's presentation surfaced by formalizing.) -/
theorem shifted_sum_rational (ha : StrictMono a)
    (hf : ∀ i, 1 ≤ i → ∃ q : ℚ, HasSum (fun n => f i (a n)) (q : ℝ)) :
    ∀ j : ℕ, ∃ q : ℚ, HasSum (fun n => ((a n : ℝ) + (tSeq j : ℝ))⁻¹) (q : ℝ) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
  classical
  choose! Q hQ using IH
  obtain ⟨x, hx⟩ := hf (j + 1) (Nat.le_add_left 1 j)
  -- the linear combination of the already-known shifted sums
  have hlin : HasSum
      (fun n => ∑ k ∈ range j, (m (j + 1) k : ℝ) * ((a n : ℝ) + (tSeq k : ℝ))⁻¹)
      (∑ k ∈ range j, (m (j + 1) k : ℝ) * (Q k : ℝ)) :=
    hasSum_sum fun k hk => (hQ k (mem_range.mp hk)).mul_left _
  -- the remainder series, which off the poles is the diagonal term
  set h : ℕ → ℝ := fun n => f (j + 1) (a n)
      - ∑ k ∈ range j, (m (j + 1) k : ℝ) * ((a n : ℝ) + (tSeq k : ℝ))⁻¹ with hh
  set F : ℕ → ℝ := fun n => (m (j + 1) j : ℝ) * ((a n : ℝ) + (tSeq j : ℝ))⁻¹
    with hF
  have hhsum : HasSum h ((x : ℝ) - ∑ k ∈ range j, (m (j + 1) k : ℝ) * (Q k : ℝ)) :=
    hx.sub hlin
  -- off the finite bad set, `h = F`
  set B : Finset ℕ := (bad_finite ha (j + 1)).toFinset with hB
  have hgood : ∀ n ∉ B, h n = F n := by
    intro n hn
    have hnb : ∀ k ∈ range (j + 1), (a n : ℚ) + tSeq k ≠ 0 := by
      intro k hk hzero
      exact hn (by rw [hB, Set.Finite.mem_toFinset]; exact ⟨k, hk, hzero⟩)
    have hnb' : ∀ k ∈ range (j + 1), ((a n : ℕ) : ℝ) + (tSeq k : ℝ) ≠ 0 := by
      intro k hk
      have hcast : ((a n : ℕ) : ℝ) + (tSeq k : ℝ) = (((a n : ℚ) + tSeq k : ℚ) : ℝ) := by
        push_cast
        rfl
      rw [hcast]
      exact_mod_cast hnb k hk
    have hdecomp := f_eq_sum (i := j + 1) (Nat.le_add_left 1 j) hnb'
    simp only [hh, hF]
    rw [hdecomp, sum_range_succ]
    ring
  -- hence the correction series has finite support and a rational sum
  have hcorr : HasSum (fun n => h n - F n) (∑ n ∈ B, (h n - F n)) := by
    refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
    rw [hgood n hn, sub_self]
  have hFsum : HasSum F ((x : ℝ) - ∑ k ∈ range j, (m (j + 1) k : ℝ) * (Q k : ℝ)
      - ∑ n ∈ B, (h n - F n)) := by
    have := hhsum.sub hcorr
    simpa using this
  -- the correction is a cast of an explicit rational
  set rc : ℕ → ℚ := fun n =>
    (∏ k ∈ range (j + 1), ((a n : ℚ) + tSeq k))⁻¹
      - ∑ k ∈ range j, m (j + 1) k * ((a n : ℚ) + tSeq k)⁻¹
      - m (j + 1) j * ((a n : ℚ) + tSeq j)⁻¹ with hrc
  have hcast : ∀ n, h n - F n = ((rc n : ℚ) : ℝ) := by
    intro n
    simp only [hh, hF, hrc]
    rw [f_cast]
    push_cast
    ring
  -- solve for the diagonal term
  have hm : ((m (j + 1) j : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast m_ne_zero (j + 1) j
  refine ⟨(m (j + 1) j)⁻¹ * (x - ∑ k ∈ range j, m (j + 1) k * Q k - ∑ n ∈ B, rc n), ?_⟩
  have hdiag := hFsum.mul_left ((m (j + 1) j : ℝ))⁻¹
  have hfun : (fun n => ((m (j + 1) j : ℝ))⁻¹ * F n)
      = fun n => ((a n : ℝ) + (tSeq j : ℝ))⁻¹ := by
    funext n
    simp only [hF]
    rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]
  rw [hfun] at hdiag
  have hval : ((m (j + 1) j : ℝ))⁻¹ * ((x : ℝ)
        - ∑ k ∈ range j, (m (j + 1) k : ℝ) * (Q k : ℝ) - ∑ n ∈ B, (h n - F n))
      = (((m (j + 1) j)⁻¹
          * (x - ∑ k ∈ range j, m (j + 1) k * Q k - ∑ n ∈ B, rc n) : ℚ) : ℝ) := by
    rw [sum_congr rfl fun n _ => hcast n]
    push_cast
    ring
  rw [hval] at hdiag
  exact hdiag

/-- **The reduction.**  A strictly increasing sequence of naturals with
rational `f`-sums has all its shifted Ahmes series rational. -/
theorem rationalShifts_of_f_sums (ha : StrictMono a)
    (hf : ∀ i, 1 ≤ i → ∃ q : ℚ, HasSum (fun n => f i (a n)) (q : ℝ)) :
    RationalShifts a := by
  intro t _
  obtain ⟨j, hj⟩ := tSeq_surjective t
  obtain ⟨q, hq⟩ := shifted_sum_rational ha hf j
  rw [hj] at hq
  exact ⟨q, by simpa [one_div] using hq⟩

/-- **Milestone.**  The full Kovač–Tao theorem (the remaining Challenge
`sorry`) now follows from the existence of a single sequence with rational
`f`-sums; constructing it is the business of Sections 7–8 of the paper. -/
theorem rational_shifts_of_construction
    (h : ∃ a : ℕ → ℕ, StrictMono a ∧ 1 ≤ a 0 ∧
      ∀ i, 1 ≤ i → ∃ q : ℚ, HasSum (fun n => f i (a n)) (q : ℝ)) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ a 0 ≥ 1 ∧
      (∀ t : ℚ, (¬ ∃ n : ℕ, t = -(a n)) →
        (∃ q : ℚ, HasSum (fun n : ℕ => ((1 : ℝ) / ((a n) + t))) q)) := by
  obtain ⟨a, ha, h0, hf⟩ := h
  exact ⟨a, ha, h0, rationalShifts_of_f_sums ha hf⟩

end Erdos266
