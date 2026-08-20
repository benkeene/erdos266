/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import Erdos266.Recursion
import Erdos266.Reduction

/-!
# The construction: extraction and convergence

The run of the algorithm stabilizes: the shifts of block `l` never change
after step `l + 1`, and the target of dimension `i + 1` never changes after
its entry step `mseq (i + 1)`.  This yields the limit objects `Sinf` and
`xinf`, for which the invariant holds at every step.

The sequence itself enumerates the blocks in order (`cnt`, `kOf`, `aSeq`);
it is strictly monotone (inside a block by `2M < N`, across blocks by the
separation of scales) and positive.  Its partial sums at block boundaries
are exactly `finSum`, which converges to the targets since both the
invariant radius and the anchor tails vanish; a squeeze upgrades this to
convergence of all partial sums, and eventual nonnegativity of the terms
upgrades that to `HasSum`.  Feeding the result into the reduction closes
the main theorem.
-/

namespace Erdos266

open Finset Filter Topology

/-! ### Stability of the run -/

lemma run_one : run 1 = initSt := by
  rw [run, ite_eq_left (by norm_num)]

lemma run_two : run 2 = initSt := by
  rw [run, ite_eq_left (by norm_num)]

lemma stepSt_fst_apply {k : ℕ} {st : AlgSt} (h : Inv k st) {l : ℕ} (hl : l ≠ k) (j : ℕ) :
    (stepSt k st).1 l j = st.1 l j := by
  rw [stepSt_eq h]
  exact newS_eq_of_lt h hl j

lemma stepSt_snd_apply {k : ℕ} {st : AlgSt} (h : Inv k st) {i : ℕ} (hi : i < dOf k) :
    (stepSt k st).2 i = st.2 i := by
  rw [stepSt_eq h]
  change (if dOf (k + 1) = dOf k + 1
      then Function.update st.2 (dOf k) (newQ k st h) else st.2) i = st.2 i
  split_ifs with hnew
  · exact Function.update_of_ne (by omega) _ _
  · rfl

lemma run_shift_stable {k k' : ℕ} (h2 : 2 ≤ k) (hkk : k ≤ k') {l : ℕ} (hl : l < k) (j : ℕ) :
    (run k').1 l j = (run k).1 l j := by
  induction k', hkk using Nat.le_induction with
  | base => rfl
  | succ k' hk' ih =>
    rw [run_succ (by omega), stepSt_fst_apply (inv_run k' (by omega)) (by omega) j]
    exact ih

lemma run_target_stable {k k' : ℕ} (h2 : 2 ≤ k) (hkk : k ≤ k') {i : ℕ} (hi : i < dOf k) :
    (run k').2 i = (run k).2 i := by
  induction k', hkk using Nat.le_induction with
  | base => rfl
  | succ k' hk' ih =>
    have hik' : i < dOf k' := lt_of_lt_of_le hi (dOf_mono hk')
    rw [run_succ (by omega), stepSt_snd_apply (inv_run k' (by omega)) hik']
    exact ih

/-! ### The limit objects -/

/-- The final shifts. -/
noncomputable def Sinf : ℕ → ℕ → ℤ := fun l j => (run (l + 1)).1 l j

/-- The final targets: `xinf i` is the sum the level-`(i+1)` series will
have. -/
noncomputable def xinf : ℕ → ℚ := fun i => (run (mseq (i + 1))).2 i

lemma Sinf_eq {k l : ℕ} (h2 : 2 ≤ k) (hl : l < k) (j : ℕ) :
    (run k).1 l j = Sinf l j := by
  rcases Nat.lt_or_ge l 1 with h | h
  · have hl0 : l = 0 := by omega
    subst hl0
    have e1 : (run k).1 0 j = (run 2).1 0 j :=
      run_shift_stable le_rfl h2 (by norm_num) j
    change (run k).1 0 j = (run 1).1 0 j
    rw [e1, run_two, run_one]
  · exact run_shift_stable (by omega) (by omega) (by omega) j

lemma xinf_eq {k i : ℕ} (hk : mseq (i + 1) ≤ k) : (run k).2 i = xinf i := by
  have h1 : i < dOf (mseq (i + 1)) :=
    lt_of_lt_of_le (Nat.lt_succ_self i) (le_dOf le_rfl)
  exact run_target_stable (two_le_mseq _) hk h1

/-- Positive dimension count forces the block index past the first entry. -/
lemma mseq_one_le_of_dOf_pos {l : ℕ} (h : 0 < dOf l) : mseq 1 ≤ l := by
  by_contra hc
  push Not at hc
  rcases Nat.lt_or_ge l 2 with h2 | h2
  · rw [dOf_lt_two h2] at h
    omega
  · have := (dOf_lt_iff h2).mpr hc
    omega

lemma two_le_of_dOf_pos {l : ℕ} (h : 0 < dOf l) : 2 ≤ l := by
  have h1 := mseq_one_le_of_dOf_pos h
  have h2 := add_two_le_mseq 1
  omega

/-- The invariant, for the limit objects. -/
lemma inv_inf {k : ℕ} (hk : 2 ≤ k) {i : ℕ} (hi : i < dOf k) :
    |finSum i k Sinf + tailAnchor (i + 1) k - (xinf i : ℝ)|
      ≤ εA (dOf k) * bigM k / (bigN k : ℝ) ^ (i + 2) := by
  have h := (inv_run k hk).2.2 i hi
  have e1 : finSum i k (run k).1 = finSum i k Sinf :=
    finSum_congr fun l hl j _ => Sinf_eq hk hl j
  have e2 : (run k).2 i = xinf i := by
    refine xinf_eq (le_trans (mseq_strictMono.monotone ?_) (mseq_dOf_le hk))
    omega
  rw [e1, e2] at h
  exact h

lemma Sinf_bound {l j : ℕ} (hj : j < dOf l) : |Sinf l j| ≤ (bigM l : ℤ) := by
  have h2 : 2 ≤ l := two_le_of_dOf_pos (by omega)
  exact (inv_run (l + 1) (by omega)).2.1 l (Nat.lt_succ_self l) j hj

/-! ### The sequence -/

/-- The number of sequence elements before block `k`. -/
noncomputable def cnt (k : ℕ) : ℕ := ∑ l ∈ range k, dOf l

lemma cnt_succ (k : ℕ) : cnt (k + 1) = cnt k + dOf k := sum_range_succ _ k

lemma cnt_mono : Monotone cnt := by
  apply monotone_nat_of_le_succ
  intro k
  rw [cnt_succ]
  omega

lemma le_cnt (m : ℕ) : m + 1 ≤ cnt (mseq 1 + m + 1) := by
  induction m with
  | zero =>
    rw [show mseq 1 + 0 + 1 = mseq 1 + 1 from rfl, cnt_succ]
    have h1 : 1 ≤ dOf (mseq 1) := le_dOf le_rfl
    omega
  | succ m ih =>
    rw [show mseq 1 + (m + 1) + 1 = (mseq 1 + m + 1) + 1 from by omega, cnt_succ]
    have h1 : 1 ≤ dOf (mseq 1 + m + 1) := le_dOf (by omega)
    omega

lemma cnt_unbounded (n : ℕ) : ∃ k, n < cnt (k + 1) := by
  refine ⟨mseq 1 + n, ?_⟩
  have := le_cnt n
  omega

/-- The block containing position `n`. -/
noncomputable def kOf (n : ℕ) : ℕ := Nat.find (cnt_unbounded n)

lemma kOf_spec (n : ℕ) : n < cnt (kOf n + 1) := Nat.find_spec (cnt_unbounded n)

lemma cnt_kOf_le (n : ℕ) : cnt (kOf n) ≤ n := by
  rcases Nat.eq_zero_or_pos (kOf n) with h | h
  · rw [h]
    simp [cnt]
  · have hmin := Nat.find_min (cnt_unbounded n) (show kOf n - 1 < kOf n by omega)
    rw [show kOf n - 1 + 1 = kOf n by omega] at hmin
    omega

lemma jOf_lt (n : ℕ) : n - cnt (kOf n) < dOf (kOf n) := by
  have h1 := kOf_spec n
  have h2 := cnt_kOf_le n
  rw [cnt_succ] at h1
  omega

lemma kOf_le_of_lt {n k : ℕ} (h : n < cnt (k + 1)) : kOf n ≤ k :=
  Nat.find_min' (cnt_unbounded n) h

lemma le_kOf_of_cnt_le {n k : ℕ} (h : cnt k ≤ n) : k ≤ kOf n := by
  by_contra hc
  push Not at hc
  have h1 : kOf n + 1 ≤ k := by omega
  have h2 : cnt (kOf n + 1) ≤ cnt k := cnt_mono h1
  have h3 := kOf_spec n
  omega

/-- Position `cnt k + j` lies in block `k`, slot `j`. -/
lemma kOf_cnt_add {k j : ℕ} (hj : j < dOf k) : kOf (cnt k + j) = k := by
  have h1 : kOf (cnt k + j) ≤ k := by
    apply kOf_le_of_lt
    rw [cnt_succ]
    omega
  have h2 : k ≤ kOf (cnt k + j) := le_kOf_of_cnt_le (by omega)
  omega

/-- The sequence element of block `l`, slot `j`, as an integer. -/
noncomputable def elemZ (l j : ℕ) : ℤ := ((j + 1) * bigN l : ℕ) + Sinf l j

/-- **The constructed sequence.** -/
noncomputable def aSeq (n : ℕ) : ℕ := (elemZ (kOf n) (n - cnt (kOf n))).toNat

lemma elemZ_lb {l j : ℕ} (hj : j < dOf l) : (bigN l : ℤ) - bigM l ≤ elemZ l j := by
  have h1 : (bigN l : ℤ) ≤ ((j + 1) * bigN l : ℕ) := by
    exact_mod_cast Nat.le_mul_of_pos_left _ (by omega : 0 < j + 1)
  have h2 := (abs_le.mp (Sinf_bound hj)).1
  rw [elemZ]
  omega

lemma elemZ_ub {l j : ℕ} (hj : j < dOf l) : elemZ l j ≤ (l * bigN l : ℤ) + bigM l := by
  have h1 : ((j + 1) * bigN l : ℕ) ≤ (l * bigN l : ℕ) := by
    have hd := dOf_le l
    exact Nat.mul_le_mul_right _ (by omega)
  have h1' : (((j + 1) * bigN l : ℕ) : ℤ) ≤ ((l * bigN l : ℕ) : ℤ) := by exact_mod_cast h1
  have h2 := (abs_le.mp (Sinf_bound hj)).2
  rw [elemZ]
  push_cast at h1' ⊢
  omega

lemma elemZ_pos {l j : ℕ} (hj : j < dOf l) : 0 < elemZ l j := by
  have h2 : 2 ≤ l := two_le_of_dOf_pos (by omega)
  have h3 := two_mul_bigM_lt h2
  have h4 := elemZ_lb hj
  have h3' : 2 * (bigM l : ℤ) < (bigN l : ℤ) := by exact_mod_cast h3
  have h5 : (0 : ℤ) ≤ (bigM l : ℤ) := by positivity
  omega

lemma aSeq_cast (n : ℕ) : (aSeq n : ℤ) = elemZ (kOf n) (n - cnt (kOf n)) :=
  Int.toNat_of_nonneg (elemZ_pos (jOf_lt n)).le

lemma one_le_aSeq (n : ℕ) : 1 ≤ aSeq n := by
  have h1 := elemZ_pos (jOf_lt n)
  have h2 := aSeq_cast n
  omega

/-- Doubling bound extracted from the cross-block estimate. -/
lemma twice_succ_le_bigN (k : ℕ) : 2 * (k + 1) * bigN k ≤ bigN (k + 1) := by
  rw [bigN_succ]
  have h4 : 2 * (k + 1) ≤ 2 ^ (2 * k + 1) := by
    have h5 := succ_le_two_pow (2 * k)
    calc 2 * (k + 1) ≤ 2 * (2 * k + 1) := by omega
    _ ≤ 2 * 2 ^ (2 * k) := by omega
    _ = 2 ^ (2 * k + 1) := by ring
  exact Nat.mul_le_mul_right _ h4

/-- Monotonicity within a block. -/
lemma elemZ_lt_within {l j : ℕ} (hj : j + 1 < dOf l) : elemZ l j < elemZ l (j + 1) := by
  have h2 : 2 ≤ l := two_le_of_dOf_pos (by omega)
  have h3 : 2 * (bigM l : ℤ) < (bigN l : ℤ) := by exact_mod_cast two_mul_bigM_lt h2
  have hb1 := (abs_le.mp (Sinf_bound (by omega : j < dOf l))).1
  have hb2 := (abs_le.mp (Sinf_bound hj)).1
  have hb3 := (abs_le.mp (Sinf_bound (by omega : j < dOf l))).2
  have hb4 := (abs_le.mp (Sinf_bound hj)).2
  rw [elemZ, elemZ]
  have e1 : (((j + 1 + 1) * bigN l : ℕ) : ℤ) = ((j + 1) * bigN l : ℕ) + (bigN l : ℤ) := by
    push_cast
    ring
  rw [e1]
  omega

/-- Monotonicity across blocks. -/
lemma elemZ_cross {l l' j j' : ℕ} (hll : l < l') (hj : j < dOf l) (hj' : j' < dOf l') :
    elemZ l j < elemZ l' j' := by
  have h2 : 2 ≤ l := two_le_of_dOf_pos (by omega)
  have h2' : 2 ≤ l' := by omega
  have hub := elemZ_ub hj
  have hlb := elemZ_lb hj'
  -- `l·N l + M l < N l' - M l'` via the doubling bound and `2M < N`
  have key : (l * bigN l : ℤ) + bigM l < (bigN l' : ℤ) - bigM l' := by
    have hA : 2 * ((l : ℤ) * bigN l + bigM l) ≤ (bigN (l + 1) : ℤ) := by
      have h5 : (bigM l : ℤ) < bigN l := by
        have := two_mul_bigM_lt h2
        have h6 : (0:ℤ) ≤ (bigM l : ℤ) := by positivity
        exact_mod_cast by omega
      have h7 : 2 * (l + 1) * bigN l ≤ bigN (l + 1) := twice_succ_le_bigN l
      have h7' : (2 * (l + 1) * bigN l : ℤ) ≤ (bigN (l + 1) : ℤ) := by exact_mod_cast h7
      nlinarith [show (0:ℤ) ≤ (l : ℤ) from by positivity,
        show (0:ℤ) < (bigN l : ℤ) from by exact_mod_cast bigN_pos l]
    have hB : (bigN (l + 1) : ℤ) ≤ (bigN l' : ℤ) := by
      exact_mod_cast bigN_strictMono.monotone (by omega : l + 1 ≤ l')
    have hC : 2 * (bigM l' : ℤ) < (bigN l' : ℤ) := by
      exact_mod_cast two_mul_bigM_lt h2'
    omega
  omega

/-- **The sequence is strictly monotone.** -/
lemma aSeq_strictMono : StrictMono aSeq := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hZ : elemZ (kOf n) (n - cnt (kOf n)) < elemZ (kOf (n + 1)) (n + 1 - cnt (kOf (n + 1))) := by
    rcases Nat.lt_or_ge (n + 1) (cnt (kOf n + 1)) with hsame | hbound
    · -- same block, next slot
      have hk : kOf (n + 1) = kOf n := by
        have h1 : kOf (n + 1) ≤ kOf n := kOf_le_of_lt hsame
        have h2 : kOf n ≤ kOf (n + 1) := le_kOf_of_cnt_le (le_trans (cnt_kOf_le n) (by omega))
        omega
      have hj : n + 1 - cnt (kOf n) = (n - cnt (kOf n)) + 1 := by
        have := cnt_kOf_le n
        omega
      rw [hk, hj]
      apply elemZ_lt_within
      have h3 := jOf_lt (n + 1)
      rw [hk, hj] at h3
      exact h3
    · -- block boundary
      have hk : kOf n < kOf (n + 1) := by
        by_contra hc
        push Not at hc
        have h1 : cnt (kOf (n + 1) + 1) ≤ cnt (kOf n + 1) := cnt_mono (by omega)
        have h2 := kOf_spec (n + 1)
        omega
      exact elemZ_cross hk (jOf_lt n) (jOf_lt (n + 1))
  have h1 := aSeq_cast n
  have h2 := aSeq_cast (n + 1)
  omega

/-! ### Partial sums along blocks -/

/-- The sequence element at position `cnt k + j` is the block-`k` sample. -/
lemma aSeq_block {k j : ℕ} (hj : j < dOf k) :
    ((aSeq (cnt k + j) : ℕ) : ℝ) = elemR Sinf k j := by
  have hk := kOf_cnt_add hj
  have hcast := aSeq_cast (cnt k + j)
  rw [hk, show cnt k + j - cnt k = j from by omega] at hcast
  have h2 : ((aSeq (cnt k + j) : ℤ) : ℝ) = ((elemZ k j : ℤ) : ℝ) := by
    rw [hcast]
  push_cast at h2
  rw [h2, elemZ, elemR]
  push_cast
  ring

/-- Partial sums of the series at block boundaries are the `finSum`s. -/
lemma partial_regroup (i' k : ℕ) :
    ∑ n ∈ range (cnt k), f (i' + 1) ((aSeq n : ℕ) : ℝ) = finSum i' k Sinf := by
  induction k with
  | zero => simp [cnt, finSum]
  | succ k ih =>
    rw [cnt_succ, sum_range_add, ih, finSum_succ]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [aSeq_block (mem_range.mp hj)]

/-! ### The limit of the partial sums -/

lemma εA_le_one (d : ℕ) : εA d ≤ 1 :=
  le_trans (εA_antitone (Nat.zero_le d)) (εL_le_one 0)

/-- The invariant radius is dominated by `1/N k`. -/
lemma radius_le {k i : ℕ} (_hk : 2 ≤ k) :
    εA (dOf k) * bigM k / (bigN k : ℝ) ^ (i + 2) ≤ ((bigN k : ℝ))⁻¹ := by
  have hN1 : (1:ℝ) ≤ (bigN k : ℝ) := by exact_mod_cast one_le_bigN k
  have hN0 : (0:ℝ) < (bigN k : ℝ) := by linarith
  have hM : (bigM k : ℝ) ≤ (bigN k : ℝ) := by
    have h1 : bigM k ≤ bigN k :=
      le_trans (bigM_le_sqrt k) (Nat.sqrt_le_self _)
    exact_mod_cast h1
  have hpow : (bigN k : ℝ) ^ 2 ≤ (bigN k : ℝ) ^ (i + 2) :=
    pow_le_pow_right₀ hN1 (by omega)
  have hM0 : (0:ℝ) ≤ (bigM k : ℝ) := Nat.cast_nonneg _
  have h2 : εA (dOf k) * (bigM k : ℝ) ≤ (bigN k : ℝ) := by
    calc εA (dOf k) * (bigM k : ℝ) ≤ 1 * (bigM k : ℝ) :=
          mul_le_mul_of_nonneg_right (εA_le_one _) hM0
    _ = (bigM k : ℝ) := one_mul _
    _ ≤ (bigN k : ℝ) := hM
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (bigN k : ℝ) ^ (i + 2)),
    inv_mul_eq_div, le_div_iff₀ hN0]
  calc εA (dOf k) * (bigM k : ℝ) * (bigN k : ℝ)
      ≤ (bigN k : ℝ) * (bigN k : ℝ) :=
        mul_le_mul_of_nonneg_right h2 hN0.le
  _ = (bigN k : ℝ) ^ 2 := by ring
  _ ≤ (bigN k : ℝ) ^ (i + 2) := hpow

lemma le_bigN (k : ℕ) : k ≤ bigN k := by
  have h4 := succ_le_two_pow k
  have h5 : (2:ℕ) ^ k ≤ bigN k := by
    rw [bigN]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_self_pow (by norm_num) k)
  omega

lemma bigN_tendsto : Tendsto (fun k => (bigN k : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
  exact_mod_cast le_bigN k

lemma tailAnchor_nonneg {i k : ℕ} (h2i : 2 * i ≤ bigN k) : 0 ≤ tailAnchor i k := by
  refine tsum_nonneg fun l => ?_
  apply blockAnchor_nonneg
  have h1 : bigN k ≤ bigN (k + l) := bigN_strictMono.monotone (by omega)
  have h2 : (2 * i : ℕ) ≤ bigN (k + l) := by omega
  exact_mod_cast h2

/-- **The block partial sums converge to the targets.** -/
lemma finSum_tendsto (i' : ℕ) :
    Tendsto (fun k => finSum i' k Sinf) atTop (𝓝 ((xinf i' : ℚ) : ℝ)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hbound : ∀ᶠ k in atTop, ‖finSum i' k Sinf - ((xinf i' : ℚ) : ℝ)‖
      ≤ ((bigN k : ℝ))⁻¹ + tailAnchor (i' + 1) k := by
    rw [eventually_atTop]
    refine ⟨max (mseq (i' + 1)) (2 * i' + 2), fun k hk => ?_⟩
    have hk1 : mseq (i' + 1) ≤ k := le_trans (le_max_left _ _) hk
    have hk2 : 2 ≤ k := le_trans (two_le_mseq _) hk1
    have hdk : i' < dOf k := lt_of_lt_of_le (Nat.lt_succ_self i') (le_dOf hk1)
    have h2i : 2 * (i' + 1) ≤ bigN k := by
      have h3 : k + 1 ≤ bigN k := by
        have h4 := succ_le_two_pow k
        have h5 : (2:ℕ) ^ k ≤ bigN k := by
          rw [bigN]
          exact Nat.pow_le_pow_right (by norm_num) (Nat.le_self_pow (by norm_num) k)
        omega
      have h6 : 2 * i' + 2 ≤ k := le_trans (le_max_right _ _) hk
      omega
    have htail0 : 0 ≤ tailAnchor (i' + 1) k := tailAnchor_nonneg h2i
    have hinv := inv_inf hk2 hdk
    rw [Real.norm_eq_abs]
    calc |finSum i' k Sinf - ((xinf i' : ℚ) : ℝ)|
        = |(finSum i' k Sinf + tailAnchor (i' + 1) k - ((xinf i' : ℚ) : ℝ))
            + (-(tailAnchor (i' + 1) k))| := by
          congr 1
          ring
    _ ≤ |finSum i' k Sinf + tailAnchor (i' + 1) k - ((xinf i' : ℚ) : ℝ)|
          + |(-(tailAnchor (i' + 1) k))| := abs_add_le _ _
    _ ≤ ((bigN k : ℝ))⁻¹ + tailAnchor (i' + 1) k := by
          refine add_le_add (hinv.trans (radius_le hk2)) ?_
          rw [abs_neg, abs_of_nonneg htail0]
  refine squeeze_zero_norm' hbound ?_
  have h1 : Tendsto (fun k => ((bigN k : ℝ))⁻¹) atTop (𝓝 0) :=
    bigN_tendsto.inv_tendsto_atTop
  have h2 := tailAnchor_tendsto (i' + 1)
  simpa using h1.add h2

/-! ### From block partial sums to `HasSum` -/

/-- The partial sums of the constructed series. -/
noncomputable def pSum (i' n : ℕ) : ℝ := ∑ m ∈ range n, f (i' + 1) ((aSeq m : ℕ) : ℝ)

lemma pSum_regroup (i' k : ℕ) : pSum i' (cnt k) = finSum i' k Sinf :=
  partial_regroup i' k

/-- Beyond the threshold block the sequence values dominate `2(i'+1)`. -/
lemma aSeq_large {i' m : ℕ} (hm : cnt (4 * i' + 4) ≤ m) :
    (2 * (i' + 1) : ℝ) ≤ ((aSeq m : ℕ) : ℝ) := by
  have hk : 4 * i' + 4 ≤ kOf m := le_kOf_of_cnt_le hm
  have hN : (4 * (i' + 1) : ℕ) ≤ bigN (kOf m) := by
    have := le_bigN (kOf m)
    omega
  have hM : 2 * bigM (kOf m) < bigN (kOf m) := two_mul_bigM_lt (by omega)
  have hlb := elemZ_lb (jOf_lt m)
  have hcast := aSeq_cast m
  have hZ : (2 * (i' + 1) : ℤ) ≤ (aSeq m : ℤ) := by
    have hN' : (4 * (i' + 1) : ℤ) ≤ (bigN (kOf m) : ℤ) := by exact_mod_cast hN
    have hM' : 2 * (bigM (kOf m) : ℤ) < (bigN (kOf m) : ℤ) := by exact_mod_cast hM
    omega
  exact_mod_cast hZ

lemma term_nonneg {i' m : ℕ} (hm : cnt (4 * i' + 4) ≤ m) :
    0 ≤ f (i' + 1) ((aSeq m : ℕ) : ℝ) := by
  have h1 := aSeq_large hm
  have h2 : (0:ℝ) < ((aSeq m : ℕ) : ℝ) := by
    have := one_le_aSeq m
    exact_mod_cast by omega
  have h3 : (2 * (i' + 1) : ℝ) = 2 * ((i' + 1 : ℕ) : ℝ) := by push_cast; ring
  exact (f_pos (by rw [← h3]; exact_mod_cast h1) h2).le

lemma pSum_mono {i' r s : ℕ} (hr : cnt (4 * i' + 4) ≤ r) (hrs : r ≤ s) :
    pSum i' r ≤ pSum i' s := by
  have hs : pSum i' (r + (s - r))
      = pSum i' r + ∑ x ∈ range (s - r), f (i' + 1) ((aSeq (r + x) : ℕ) : ℝ) := by
    rw [pSum, sum_range_add]
    rfl
  have h1 : 0 ≤ ∑ x ∈ range (s - r), f (i' + 1) ((aSeq (r + x) : ℕ) : ℝ) :=
    sum_nonneg fun x _ => term_nonneg (by omega)
  calc pSum i' r ≤ pSum i' r + ∑ x ∈ range (s - r), f (i' + 1) ((aSeq (r + x) : ℕ) : ℝ) := by
        linarith
  _ = pSum i' (r + (s - r)) := hs.symm
  _ = pSum i' s := by rw [show r + (s - r) = s from by omega]

lemma kOf_tendsto : Tendsto kOf atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨cnt b, fun a ha => le_kOf_of_cnt_le ha⟩

/-- **All partial sums converge to the target.** -/
lemma pSum_tendsto (i' : ℕ) :
    Tendsto (fun n => pSum i' n) atTop (𝓝 ((xinf i' : ℚ) : ℝ)) := by
  have hL : Tendsto (fun n => finSum i' (kOf n) Sinf) atTop (𝓝 ((xinf i' : ℚ) : ℝ)) :=
    (finSum_tendsto i').comp kOf_tendsto
  have hU : Tendsto (fun n => finSum i' (kOf n + 1) Sinf) atTop (𝓝 ((xinf i' : ℚ) : ℝ)) :=
    (finSum_tendsto i').comp ((tendsto_add_atTop_nat 1).comp kOf_tendsto)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · rw [eventually_atTop]
    refine ⟨cnt (4 * i' + 4), fun n hn => ?_⟩
    rw [← pSum_regroup]
    refine pSum_mono ?_ (cnt_kOf_le n)
    exact cnt_mono (le_kOf_of_cnt_le hn)
  · rw [eventually_atTop]
    refine ⟨cnt (4 * i' + 4), fun n hn => ?_⟩
    rw [← pSum_regroup]
    refine pSum_mono hn ?_
    exact (kOf_spec n).le

/-- Every partial sum beyond the threshold is at most the target. -/
lemma pSum_le {i' n : ℕ} (hn : cnt (4 * i' + 4) ≤ n) :
    pSum i' n ≤ ((xinf i' : ℚ) : ℝ) := by
  refine ge_of_tendsto (pSum_tendsto i') ?_
  rw [eventually_atTop]
  exact ⟨n, fun s hs => pSum_mono hn hs⟩

/-- **The constructed series has the chosen rational sums.** -/
theorem hasSum_aSeq (i' : ℕ) :
    HasSum (fun n => f (i' + 1) ((aSeq n : ℕ) : ℝ)) ((xinf i' : ℚ) : ℝ) := by
  set n₀ : ℕ := cnt (4 * i' + 4) with hn₀
  have hsum : Summable (fun n => f (i' + 1) ((aSeq n : ℕ) : ℝ)) := by
    refine (summable_nat_add_iff n₀).mp ?_
    refine summable_of_sum_range_le (c := ((xinf i' : ℚ) : ℝ) - pSum i' n₀)
      (fun m => term_nonneg (by omega)) fun m => ?_
    have e1 : ∑ x ∈ range m, f (i' + 1) ((aSeq (x + n₀) : ℕ) : ℝ)
        = pSum i' (n₀ + m) - pSum i' n₀ := by
      rw [pSum, sum_range_add, ← pSum]
      have e2 : ∀ x ∈ range m, f (i' + 1) ((aSeq (n₀ + x) : ℕ) : ℝ)
          = f (i' + 1) ((aSeq (x + n₀) : ℕ) : ℝ) := by
        intro x _
        rw [Nat.add_comm n₀ x]
      rw [sum_congr rfl e2]
      ring
    rw [e1]
    have h3 := pSum_le (i' := i') (n := n₀ + m) (by omega)
    linarith
  have h4 := hsum.hasSum
  have h5 := h4.tendsto_sum_nat
  have h6 : (∑' n, f (i' + 1) ((aSeq n : ℕ) : ℝ)) = ((xinf i' : ℚ) : ℝ) := by
    refine tendsto_nhds_unique h5 ?_
    have : (fun n => ∑ m ∈ range n, f (i' + 1) ((aSeq m : ℕ) : ℝ))
        = fun n => pSum i' n := rfl
    rw [this]
    exact pSum_tendsto i'
  rwa [h6] at h4

/-- **The construction exists** — the input the reduction needs. -/
theorem construction_exists :
    ∃ a : ℕ → ℕ, StrictMono a ∧ 1 ≤ a 0 ∧
      ∀ i, 1 ≤ i → ∃ q : ℚ, HasSum (fun n => f i (a n)) (q : ℝ) := by
  refine ⟨aSeq, aSeq_strictMono, one_le_aSeq 0, fun i hi => ?_⟩
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  exact ⟨xinf i', hasSum_aSeq i'⟩

end Erdos266
