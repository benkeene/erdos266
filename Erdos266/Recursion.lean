/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import Erdos266.Algorithm

/-!
# The construction: the recursion

The algorithm of Section 8 of [KoTa24], as a state machine.  The state
carries the shifts chosen for every past block and the rational targets
chosen for every dimension that has entered; the invariant (8.5) says that
for every active dimension `i < dOf k`, the finished partial sum plus the
tail of unshifted anchors sits within the radius
`εA (dOf k) · M k / N k ^ (i+2)` of the target `x i`.

One step: apply the lattice lemma to steer the next block so the invariant
survives with radius index `k+1` (the growth condition `mseq_cond` makes
the lattice error fit), and, when a new dimension enters at `k+1`, choose
its rational target inside the fresh interval (`exists_rat_near`).

The step function takes the good branch only when the invariant holds
(`dite`), so the state type stays simple; `inv_run` then shows the good
branch is always taken from `k = 2` on.  Extraction of the sequence and
the convergence proof live in `Convergence.lean`.
-/

namespace Erdos266

open Finset

/-- The algorithm state: shifts for every block, and rational targets. -/
abbrev AlgSt := (ℕ → ℕ → ℤ) × (ℕ → ℚ)

/-- The initial state. -/
def initSt : AlgSt := (fun _ _ => 0, fun _ => 0)

/-- The sample point of block `l`, slot `j`, after shifting. -/
noncomputable def elemR (S : ℕ → ℕ → ℤ) (l j : ℕ) : ℝ :=
  (((j + 1) * bigN l : ℕ) : ℝ) + (S l j : ℝ)

/-- The finished partial sum at level `i+1` over the first `k` blocks. -/
noncomputable def finSum (i k : ℕ) (S : ℕ → ℕ → ℤ) : ℝ :=
  ∑ l ∈ range k, ∑ j ∈ range (dOf l), f (i + 1) (elemR S l j)

lemma finSum_congr {i k : ℕ} {S S' : ℕ → ℕ → ℤ}
    (h : ∀ l, l < k → ∀ j, j < dOf l → S l j = S' l j) :
    finSum i k S = finSum i k S' := by
  refine sum_congr rfl fun l hl => sum_congr rfl fun j hj => ?_
  rw [elemR, elemR, h l (mem_range.mp hl) j (mem_range.mp hj)]

lemma finSum_succ (i k : ℕ) (S : ℕ → ℕ → ℤ) :
    finSum i (k + 1) S = finSum i k S + ∑ j ∈ range (dOf k), f (i + 1) (elemR S k j) :=
  sum_range_succ _ k

/-- The invariant (8.5): every past shift is in range, and every active
target is within the current radius of the running sum. -/
def Inv (k : ℕ) (st : AlgSt) : Prop :=
  2 ≤ k ∧
  (∀ l, l < k → ∀ j, j < dOf l → |st.1 l j| ≤ (bigM l : ℤ)) ∧
  ∀ i, i < dOf k →
    |finSum i k st.1 + tailAnchor (i + 1) k - (st.2 i : ℝ)|
      ≤ εA (dOf k) * bigM k / (bigN k : ℝ) ^ (i + 2)

/-- The lattice target vector at step `k`. -/
noncomputable def Xvec (k : ℕ) (st : AlgSt) : Fin (dOf k) → ℝ :=
  fun i => (st.2 i.val : ℝ) - finSum i.val k st.1 - tailAnchor (i.val + 1) (k + 1)

lemma four_dOf_le (k : ℕ) : 4 * dOf k * bigM k ≤ bigN k := by
  calc 4 * dOf k * bigM k ≤ 4 * k * bigM k := by
        have := dOf_le k
        exact Nat.mul_le_mul_right _ (by omega)
  _ ≤ bigN k := four_mul_bigM_le k

/-- The invariant puts the lattice targets inside the lattice hypothesis. -/
lemma step_hyp {k : ℕ} {st : AlgSt} (h : Inv k st) :
    ∀ i : Fin (dOf k),
      |Xvec k st i - ∑ j : Fin (dOf k), f (i.val + 1) (((j.val + 1) * bigN k : ℕ) : ℝ)|
        ≤ εL (dOf k) * bigM k / (bigN k : ℝ) ^ (i.val + 2) := by
  obtain ⟨hk, _, hinv⟩ := h
  intro i
  have hanch : ∑ j : Fin (dOf k), f (i.val + 1) (((j.val + 1) * bigN k : ℕ) : ℝ)
      = blockAnchor (i.val + 1) k := by
    rw [blockAnchor]
    exact Fin.sum_univ_eq_sum_range
      (fun j => f (i.val + 1) (((j + 1) * bigN k : ℕ) : ℝ)) (dOf k)
  have htail := tailAnchor_succ (i := i.val + 1) (by omega) k
  have hi := hinv i.val i.isLt
  have hstep : Xvec k st i - ∑ j : Fin (dOf k), f (i.val + 1) (((j.val + 1) * bigN k : ℕ) : ℝ)
      = -(finSum i.val k st.1 + tailAnchor (i.val + 1) k - (st.2 i.val : ℝ)) := by
    rw [hanch, Xvec, htail]
    ring
  rw [hstep, abs_neg]
  refine hi.trans ?_
  have hM0 : (0:ℝ) ≤ (bigM k : ℝ) := Nat.cast_nonneg _
  have hN0 : (0:ℝ) < (bigN k : ℝ) ^ (i.val + 2) := by
    have := bigN_pos k
    positivity
  have hεε := εA_le_εL (dOf k)
  apply div_le_div_of_nonneg_right ?_ hN0.le
  exact mul_le_mul_of_nonneg_right hεε hM0

/-- The invariant radius at the next step is positive. -/
lemma next_radius_pos {k : ℕ} (hk : 2 ≤ k) (d : ℕ) :
    0 < εA (dOf (k + 1)) * bigM (k + 1) / (bigN (k + 1) : ℝ) ^ (d + 2) := by
  have h1 : (0:ℝ) < εA (dOf (k + 1)) := εA_pos _
  have h2 : (1:ℝ) ≤ (bigM (k + 1) : ℝ) := by
    exact_mod_cast one_le_bigM (show 2 ≤ k + 1 by omega)
  have h3 : (0:ℝ) < (bigN (k + 1) : ℝ) ^ (d + 2) := by
    have := bigN_pos (k + 1)
    positivity
  positivity

/-- The block chosen by the lattice lemma at step `k`. -/
noncomputable def blk (k : ℕ) (st : AlgSt) (h : Inv k st) : Fin (dOf k) → ℤ :=
  (latt (dOf k) (bigN k) (bigM k) (one_le_bigN k) (four_dOf_le k)
    (Xvec k st) (step_hyp h)).choose

lemma blk_bound {k : ℕ} {st : AlgSt} (h : Inv k st) :
    ∀ j, |blk k st h j| ≤ (bigM k : ℤ) :=
  (latt (dOf k) (bigN k) (bigM k) (one_le_bigN k) (four_dOf_le k)
    (Xvec k st) (step_hyp h)).choose_spec.1

lemma blk_close {k : ℕ} {st : AlgSt} (h : Inv k st) :
    ∀ i : Fin (dOf k),
      |Xvec k st i - ∑ j : Fin (dOf k),
          f (i.val + 1) ((((j.val + 1) * bigN k : ℕ) : ℝ) + (blk k st h j : ℝ))|
        ≤ DL (dOf k) * (1 / (bigN k : ℝ) ^ (i.val + 2)
            + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i.val + 3)) :=
  (latt (dOf k) (bigN k) (bigM k) (one_le_bigN k) (four_dOf_le k)
    (Xvec k st) (step_hyp h)).choose_spec.2

/-- The shifts after step `k`: the chosen block is installed at slot `k`. -/
noncomputable def newS (k : ℕ) (st : AlgSt) (h : Inv k st) : ℕ → ℕ → ℤ :=
  fun l j =>
    if l = k then (if hj : j < dOf k then blk k st h ⟨j, hj⟩ else 0) else st.1 l j

/-- The rational target chosen for a newly entered dimension. -/
noncomputable def newQ (k : ℕ) (st : AlgSt) (h : Inv k st) : ℚ :=
  (exists_rat_near
    (finSum (dOf k) (k + 1) (newS k st h) + tailAnchor (dOf k + 1) (k + 1))
    (next_radius_pos h.1 (dOf k))).choose

lemma newQ_close {k : ℕ} {st : AlgSt} (h : Inv k st) :
    |finSum (dOf k) (k + 1) (newS k st h) + tailAnchor (dOf k + 1) (k + 1)
        - (newQ k st h : ℝ)|
      < εA (dOf (k + 1)) * bigM (k + 1) / (bigN (k + 1) : ℝ) ^ (dOf k + 2) :=
  (exists_rat_near
    (finSum (dOf k) (k + 1) (newS k st h) + tailAnchor (dOf k + 1) (k + 1))
    (next_radius_pos h.1 (dOf k))).choose_spec

open Classical in
/-- One step of the algorithm. -/
noncomputable def stepSt (k : ℕ) (st : AlgSt) : AlgSt :=
  if h : Inv k st then
    (newS k st h,
      if dOf (k + 1) = dOf k + 1
        then Function.update st.2 (dOf k) (newQ k st h)
        else st.2)
  else st

lemma stepSt_eq {k : ℕ} {st : AlgSt} (h : Inv k st) :
    stepSt k st = (newS k st h,
      if dOf (k + 1) = dOf k + 1
        then Function.update st.2 (dOf k) (newQ k st h)
        else st.2) :=
  dite_eq_left h

/-- The run of the algorithm from the initial state. -/
noncomputable def run : ℕ → AlgSt
  | 0 => initSt
  | k + 1 => if k < 2 then initSt else stepSt k (run k)

lemma run_succ {k : ℕ} (hk : 2 ≤ k) : run (k + 1) = stepSt k (run k) := by
  rw [run, ite_eq_right (by omega)]

lemma dOf_lt_two {k : ℕ} (hk : k < 2) : dOf k = 0 := by
  rw [dOf, Nat.findGreatest_eq_zero_iff]
  intro d hd _
  have := two_le_mseq d
  omega

lemma dOf_two : dOf 2 = 0 := by
  have h1 : dOf 2 < 1 := by
    rw [dOf_lt_iff le_rfl]
    have := add_two_le_mseq 1
    omega
  omega

lemma inv_init : Inv 2 initSt := by
  refine ⟨le_rfl, ?_, ?_⟩
  · intro l hl j hj
    rw [dOf_lt_two hl] at hj
    omega
  · intro i hi
    rw [dOf_two] at hi
    omega

lemma newS_eq_of_lt {k : ℕ} {st : AlgSt} (h : Inv k st) {l : ℕ} (hl : l ≠ k) (j : ℕ) :
    newS k st h l j = st.1 l j := by
  rw [newS, ite_eq_right hl]

lemma newS_eq_blk {k : ℕ} {st : AlgSt} (h : Inv k st) {j : ℕ} (hj : j < dOf k) :
    newS k st h k j = blk k st h ⟨j, hj⟩ := by
  rw [newS, ite_eq_left rfl, dite_eq_left hj]

/-- The new-block part of the updated partial sum is the lattice's shifted
sample sum. -/
lemma finSum_step {k : ℕ} {st : AlgSt} (h : Inv k st) (i : ℕ) :
    finSum i (k + 1) (newS k st h)
      = finSum i k st.1 + ∑ j : Fin (dOf k),
          f (i + 1) ((((j.val + 1) * bigN k : ℕ) : ℝ) + (blk k st h j : ℝ)) := by
  rw [finSum_succ]
  congr 1
  · exact (finSum_congr fun l hl j _ => (newS_eq_of_lt h (by omega) j).symm).symm
  · rw [← Fin.sum_univ_eq_sum_range
      (fun j => f (i + 1) (elemR (newS k st h) k j)) (dOf k)]
    refine Fintype.sum_congr _ _ fun j => ?_
    rw [elemR, newS_eq_blk h j.isLt]

/-- **The invariant survives one step.** -/
theorem inv_step {k : ℕ} {st : AlgSt} (h : Inv k st) : Inv (k + 1) (stepSt k st) := by
  rw [stepSt_eq h]
  have hk : 2 ≤ k := h.1
  have hd2 : dOf (k + 1) ≤ dOf k + 1 := dOf_succ_le k
  refine ⟨by omega, ?_, ?_⟩
  · -- the shift bounds
    intro l hl j hj
    by_cases hlk : l = k
    · subst hlk
      change |newS l st h l j| ≤ _
      rw [newS_eq_blk h hj]
      exact blk_bound h ⟨j, hj⟩
    · change |newS k st h l j| ≤ _
      rw [newS_eq_of_lt h hlk]
      exact h.2.1 l (by omega) j hj
  · -- the target estimates
    intro i hi
    change |finSum i (k+1) (newS k st h) + tailAnchor (i+1) (k+1)
        - (((if dOf (k + 1) = dOf k + 1
            then Function.update st.2 (dOf k) (newQ k st h)
            else st.2) i : ℚ) : ℝ)|
      ≤ εA (dOf (k+1)) * bigM (k+1) / (bigN (k+1) : ℝ) ^ (i + 2)
    have hNpos1 : (0:ℝ) < (bigN (k+1) : ℝ) ^ (i + 2) := by
      have := bigN_pos (k+1)
      positivity
    have hM1 : (0:ℝ) ≤ (bigM (k+1) : ℝ) := Nat.cast_nonneg _
    by_cases hcase : i < dOf k
    · -- a dimension that was already active
      have hx : (if dOf (k + 1) = dOf k + 1
            then Function.update st.2 (dOf k) (newQ k st h)
            else st.2) i = st.2 i := by
        split_ifs with hnew
        · exact Function.update_of_ne (by omega) _ _
        · rfl
      rw [hx, finSum_step h i]
      have hkey : finSum i k st.1 + (∑ j : Fin (dOf k),
            f (i + 1) ((((j.val + 1) * bigN k : ℕ) : ℝ) + (blk k st h j : ℝ)))
            + tailAnchor (i+1) (k+1) - (st.2 i : ℝ)
          = -(Xvec k st ⟨i, hcase⟩ - ∑ j : Fin (dOf k),
              f (i + 1) ((((j.val + 1) * bigN k : ℕ) : ℝ) + (blk k st h j : ℝ))) := by
        rw [Xvec]
        ring
      rw [hkey, abs_neg]
      refine (blk_close h ⟨i, hcase⟩).trans ?_
      -- the growth condition, then the antitone envelope
      obtain ⟨d', hd'⟩ : ∃ d', dOf k = d' + 1 := ⟨dOf k - 1, by omega⟩
      have hcond := mseq_cond d' k (by rw [← hd']; exact mseq_dOf_le hk) i (by omega)
      rw [show d' + 2 = dOf k + 1 from by omega, ← hd'] at hcond
      refine hcond.trans ?_
      have hεε : εA (dOf k + 1) ≤ εA (dOf (k + 1)) := εA_antitone hd2
      apply div_le_div_of_nonneg_right ?_ hNpos1.le
      exact mul_le_mul_of_nonneg_right hεε hM1
    · -- the newly entered dimension
      have hieq : i = dOf k := by omega
      have hnew : dOf (k + 1) = dOf k + 1 := by omega
      subst hieq
      rw [ite_eq_left hnew, Function.update_self]
      exact (newQ_close h).le

/-- **The invariant holds along the whole run.** -/
theorem inv_run (k : ℕ) (hk : 2 ≤ k) : Inv k (run k) := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h2 : run 2 = initSt := by
      rw [run, ite_eq_left (by norm_num)]
    rw [h2]
    exact inv_init
  | succ k hk ih =>
    rw [run_succ hk]
    exact inv_step ih

end Erdos266
