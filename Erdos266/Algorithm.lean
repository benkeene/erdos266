/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import Erdos266.LatticeLemma
import Erdos266.Growth

/-!
# The construction: setup layer

This file assembles the data the recursive construction (Section 8 of
[KoTa24]) runs on:

* `εL d`, `DL d` — the constants of the lattice lemma at dimension `d`,
  extracted by choice, and the antitone envelope `εA d = min_{d' ≤ d} εL d'`
  (the invariant radius uses `εA` so that it can only shrink when a new
  dimension enters);
* `mseq d` — the step at which dimension `d` enters: recursively the least
  step past `mseq (d-1)` from which the lattice-step error at dimension `d`
  fits inside the next invariant radius (`growth_eventually`);
* `dOf k` — the dimension active at step `k`: the largest `d` with
  `mseq d ≤ k`;
* `blockAnchor i l` — the unshifted sample sum `∑_{j < dOf l} fᵢ((j+1)Nₗ)`
  of block `l`, its summability over `l`, and the tails
  `tailAnchor i k = ∑_{l ≥ k} blockAnchor i l` with their recursion
  `tailAnchor k = blockAnchor k + tailAnchor (k+1)` and decay to `0`.

The recursion itself and the extraction of the sequence live in
`Convergence.lean`.
-/

namespace Erdos266

open Finset

/-! ### Lattice constants and the antitone envelope -/

/-- The `ε` of the lattice lemma at dimension `d`. -/
noncomputable def εL (d : ℕ) : ℝ := (lattice_lemma d).choose

/-- The `D` of the lattice lemma at dimension `d`. -/
noncomputable def DL (d : ℕ) : ℝ := (lattice_lemma d).choose_spec.choose

lemma εL_pos (d : ℕ) : 0 < εL d := (lattice_lemma d).choose_spec.choose_spec.1

lemma εL_le_one (d : ℕ) : εL d ≤ 1 := (lattice_lemma d).choose_spec.choose_spec.2.1

lemma one_le_DL (d : ℕ) : 1 ≤ DL d := (lattice_lemma d).choose_spec.choose_spec.2.2.1

lemma DL_pos (d : ℕ) : 0 < DL d := lt_of_lt_of_le one_pos (one_le_DL d)

/-- The lattice lemma, with its constants named. -/
lemma latt (d : ℕ) :
    ∀ (N M : ℕ), 1 ≤ N → 4 * d * M ≤ N →
      ∀ x : Fin d → ℝ,
        (∀ i : Fin d, |x i - ∑ j : Fin d, f (i.val + 1) (((j.val + 1) * N : ℕ) : ℝ)|
          ≤ εL d * M / (N : ℝ) ^ (i.val + 2)) →
        ∃ n : Fin d → ℤ, (∀ j, |n j| ≤ (M : ℤ)) ∧
          ∀ i : Fin d,
            |x i - ∑ j : Fin d, f (i.val + 1) ((((j.val + 1) * N : ℕ) : ℝ) + (n j : ℝ))|
              ≤ DL d * (1 / (N : ℝ) ^ (i.val + 2) + (M : ℝ) ^ 2 / (N : ℝ) ^ (i.val + 3)) :=
  (lattice_lemma d).choose_spec.choose_spec.2.2.2

/-- The antitone envelope of the lattice `ε`s. -/
noncomputable def εA : ℕ → ℝ
  | 0 => εL 0
  | d + 1 => min (εA d) (εL (d + 1))

lemma εA_pos (d : ℕ) : 0 < εA d := by
  induction d with
  | zero => exact εL_pos 0
  | succ d ih => exact lt_min ih (εL_pos (d + 1))

lemma εA_le_εL (d : ℕ) : εA d ≤ εL d := by
  cases d with
  | zero => exact le_rfl
  | succ d => exact min_le_right _ _

lemma εA_succ_le (d : ℕ) : εA (d + 1) ≤ εA d := min_le_left _ _

lemma εA_antitone : Antitone εA :=
  antitone_nat_of_succ_le εA_succ_le

/-! ### Entry thresholds and the active dimension -/

/-- The step at which dimension `d` enters the construction. -/
noncomputable def mseq : ℕ → ℕ
  | 0 => 2
  | d + 1 => max (mseq d + 1)
      (growth_eventually (d + 1) (DL (d + 1)) (εA (d + 2)) (DL_pos (d + 1))
        (εA_pos (d + 2))).choose

lemma mseq_lt_succ (d : ℕ) : mseq d < mseq (d + 1) :=
  lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)

lemma mseq_strictMono : StrictMono mseq :=
  strictMono_nat_of_lt_succ mseq_lt_succ

lemma two_le_mseq (d : ℕ) : 2 ≤ mseq d := by
  induction d with
  | zero => exact le_rfl
  | succ d ih => exact le_trans ih (mseq_lt_succ d).le

lemma add_two_le_mseq (d : ℕ) : d + 2 ≤ mseq d := by
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    have := mseq_lt_succ d
    omega

/-- The domination condition available from step `mseq d` on (for `d ≥ 1`):
the lattice-step error at dimension `d` fits inside the next invariant
radius, measured with the envelope `εA (d + 1)`. -/
lemma mseq_cond (d : ℕ) : ∀ k, mseq (d + 1) ≤ k → ∀ i : ℕ, i < d + 1 →
    DL (d + 1) * (1 / (bigN k : ℝ) ^ (i + 2) + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i + 3))
      ≤ εA (d + 2) * (bigM (k + 1) : ℝ) / (bigN (k + 1) : ℝ) ^ (i + 2) := by
  intro k hk i hi
  have hspec := (growth_eventually (d + 1) (DL (d + 1)) (εA (d + 2)) (DL_pos (d + 1))
    (εA_pos (d + 2))).choose_spec
  refine hspec.2 k ?_ i hi
  exact le_trans (le_max_right _ _) hk

/-- The dimension active at step `k`: the largest `d` with `mseq d ≤ k`. -/
noncomputable def dOf (k : ℕ) : ℕ := Nat.findGreatest (fun d => mseq d ≤ k) k

lemma dOf_le (k : ℕ) : dOf k ≤ k := Nat.findGreatest_le k

lemma mseq_dOf_le {k : ℕ} (hk : 2 ≤ k) : mseq (dOf k) ≤ k :=
  Nat.findGreatest_spec (P := fun d => mseq d ≤ k) (Nat.zero_le k) hk

lemma le_dOf {d k : ℕ} (hm : mseq d ≤ k) : d ≤ dOf k := by
  refine Nat.le_findGreatest ?_ hm
  have := add_two_le_mseq d
  omega

lemma lt_mseq_succ_dOf {k : ℕ} : k < mseq (dOf k + 1) := by
  by_contra h
  push Not at h
  have h1 : dOf k + 1 ≤ dOf k := le_dOf h
  omega

lemma dOf_lt_iff {d k : ℕ} (hk : 2 ≤ k) : dOf k < d ↔ k < mseq d := by
  constructor
  · intro h
    by_contra h2
    push Not at h2
    exact absurd (le_dOf h2) (by omega)
  · intro h
    by_contra h2
    push Not at h2
    have h3 : mseq d ≤ mseq (dOf k) := mseq_strictMono.monotone h2
    have h4 := mseq_dOf_le hk
    omega

lemma dOf_mono : Monotone dOf := by
  intro a b hab
  rcases Nat.lt_or_ge a 2 with h | h
  · have : dOf a = 0 := by
      rw [dOf, Nat.findGreatest_eq_zero_iff]
      intro d hd hdle
      have := two_le_mseq d
      omega
    omega
  · exact le_dOf (le_trans (mseq_dOf_le h) hab)

lemma dOf_succ_le (k : ℕ) : dOf (k + 1) ≤ dOf k + 1 := by
  rcases Nat.lt_or_ge (k + 1) 2 with h | h
  · have hk0 : k = 0 := by omega
    subst hk0
    have h1 : dOf 1 = 0 := by
      rw [dOf, Nat.findGreatest_eq_zero_iff]
      intro d hd _
      have := two_le_mseq d
      omega
    change dOf 1 ≤ dOf 0 + 1
    omega
  · by_contra hcon
    push Not at hcon
    have h1 : mseq (dOf k + 2) ≤ k + 1 := by
      have := mseq_strictMono.monotone (show dOf k + 2 ≤ dOf (k + 1) by omega)
      have h2 := mseq_dOf_le h
      omega
    have h2 : mseq (dOf k + 1) < mseq (dOf k + 2) := mseq_lt_succ _
    have h3 : mseq (dOf k + 1) ≤ k := by omega
    have := le_dOf h3
    omega

/-! ### Block anchors and tails -/

/-- The unshifted sample sum of block `l` at level `i`. -/
noncomputable def blockAnchor (i l : ℕ) : ℝ :=
  ∑ j ∈ range (dOf l), f i (((j + 1) * bigN l : ℕ) : ℝ)

lemma sample_ge {j l : ℕ} : (bigN l : ℝ) ≤ (((j + 1) * bigN l : ℕ) : ℝ) := by
  have h : bigN l ≤ (j + 1) * bigN l := Nat.le_mul_of_pos_left _ (by omega)
  exact_mod_cast h

lemma blockAnchor_nonneg {i l : ℕ} (h2i : (2 * i : ℝ) ≤ (bigN l : ℝ)) :
    0 ≤ blockAnchor i l := by
  refine sum_nonneg fun j _ => ?_
  have h1 : (2 * i : ℝ) ≤ (((j + 1) * bigN l : ℕ) : ℝ) := le_trans h2i sample_ge
  have h0 : (0:ℝ) < (((j + 1) * bigN l : ℕ) : ℝ) := by
    have := bigN_pos l
    have h2 : 0 < (j + 1) * bigN l := by positivity
    exact_mod_cast h2
  exact (f_pos h1 h0).le

lemma blockAnchor_le {i l : ℕ} (h2i : (2 * i : ℝ) ≤ (bigN l : ℝ)) (hi : 1 ≤ i)
    (hN2 : (2 : ℝ) ≤ (bigN l : ℝ)) :
    blockAnchor i l ≤ (l : ℝ) * (2 / (bigN l : ℝ)) := by
  have hNpos : (0:ℝ) < (bigN l : ℝ) := by linarith
  have hterm : ∀ j ∈ range (dOf l), f i (((j + 1) * bigN l : ℕ) : ℝ) ≤ 2 / (bigN l : ℝ) := by
    intro j _
    have h1 : (2 * i : ℝ) ≤ (((j + 1) * bigN l : ℕ) : ℝ) := le_trans h2i sample_ge
    have h0 : (0:ℝ) < (((j + 1) * bigN l : ℕ) : ℝ) := lt_of_lt_of_le hNpos sample_ge
    have h2 := f_le h1 h0
    have h3 : (2 / (((j + 1) * bigN l : ℕ) : ℝ)) ^ i ≤ (2 / (bigN l : ℝ)) ^ i := by
      apply pow_le_pow_left₀ (by positivity)
      apply div_le_div_of_nonneg_left (by norm_num) hNpos sample_ge
    have h4 : (2 / (bigN l : ℝ)) ^ i ≤ (2 / (bigN l : ℝ)) ^ 1 := by
      apply pow_le_pow_of_le_one (by positivity) ?_ hi
      rw [div_le_one hNpos]
      exact hN2
    rw [pow_one] at h4
    exact h2.trans (h3.trans h4)
  calc blockAnchor i l ≤ ∑ _j ∈ range (dOf l), (2 / (bigN l : ℝ)) := sum_le_sum hterm
  _ = (dOf l : ℝ) * (2 / (bigN l : ℝ)) := by
      rw [sum_const, card_range, nsmul_eq_mul]
  _ ≤ (l : ℝ) * (2 / (bigN l : ℝ)) := by
      have h5 : (dOf l : ℝ) ≤ (l : ℝ) := by exact_mod_cast dOf_le l
      exact mul_le_mul_of_nonneg_right h5 (by positivity)

/-- The block anchors are summable in the block index. -/
lemma summable_blockAnchor {i : ℕ} (hi : 1 ≤ i) :
    Summable (fun l => blockAnchor i l) := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = 2 * i + 2 := ⟨_, rfl⟩
  refine (summable_nat_add_iff L).mp ?_
  have hgeom : Summable (fun l : ℕ => 2 * ((l + L : ℝ) * (1 / 2) ^ (l + L))) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖(1/2 : ℝ)‖ < 1 by rw [Real.norm_eq_abs]; rw [abs_of_pos] <;> norm_num)
    have h2 := ((summable_nat_add_iff L).mpr h).mul_left 2
    refine h2.congr fun l => ?_
    push_cast
    rw [pow_one]
  have hLpow : ∀ l : ℕ, (2:ℕ) ^ (l + L) ≤ bigN (l + L) := by
    intro l
    rw [bigN]
    exact Nat.pow_le_pow_right (by norm_num)
      (Nat.le_self_pow (by norm_num) _)
  refine Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_) hgeom
  · apply blockAnchor_nonneg
    have h1 : 2 * i ≤ 2 ^ (l + L) := by
      have h2 := succ_le_two_pow (l + L)
      omega
    exact_mod_cast le_trans h1 (hLpow l)
  · have hpowR : ((2:ℝ)) ^ (l + L) ≤ (bigN (l + L) : ℝ) := by
      calc ((2:ℝ)) ^ (l + L) = ((2 ^ (l + L) : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (bigN (l + L) : ℝ) := by exact_mod_cast hLpow l
    have hNpos : (0:ℝ) < (bigN (l + L) : ℝ) := by exact_mod_cast bigN_pos (l + L)
    have h2N : (2 : ℝ) ≤ (bigN (l + L) : ℝ) := by
      calc (2:ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (l + L) := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
      _ ≤ (bigN (l + L) : ℝ) := hpowR
    have h2i : (2 * i : ℝ) ≤ (bigN (l + L) : ℝ) := by
      have h1 : (2 * i : ℕ) ≤ 2 ^ (l + L) := by
        have h2 := succ_le_two_pow (l + L)
        omega
      calc (2 * i : ℝ) = ((2 * i : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ (l + L) : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ (bigN (l + L) : ℝ) := by exact_mod_cast hLpow l
    calc blockAnchor i (l + L) ≤ ((l + L : ℕ) : ℝ) * (2 / (bigN (l + L) : ℝ)) :=
          blockAnchor_le h2i hi h2N
    _ ≤ ((l + L : ℕ) : ℝ) * (2 / (2:ℝ) ^ (l + L)) := by
          apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hpowR
    _ = 2 * ((l + L : ℝ) * (1 / 2) ^ (l + L)) := by
          push_cast
          rw [div_pow, one_pow]
          field_simp

/-- The tail of the anchors from block `k` on. -/
noncomputable def tailAnchor (i k : ℕ) : ℝ := ∑' l : ℕ, blockAnchor i (k + l)

lemma tailAnchor_succ {i : ℕ} (hi : 1 ≤ i) (k : ℕ) :
    tailAnchor i k = blockAnchor i k + tailAnchor i (k + 1) := by
  have hsum : Summable (fun l => blockAnchor i (k + l)) := by
    have h := summable_blockAnchor hi (i := i)
    exact ((summable_nat_add_iff k).mpr h).congr fun l => by rw [Nat.add_comm l k]
  have h2 : ∑' (b : ℕ), blockAnchor i (k + (b + 1)) = tailAnchor i (k + 1) := by
    rw [tailAnchor]
    exact tsum_congr fun b => by congr 1; omega
  rw [tailAnchor, hsum.tsum_eq_zero_add, Nat.add_zero, h2]

/-- The tails tend to `0`. -/
lemma tailAnchor_tendsto (i : ℕ) :
    Filter.Tendsto (fun k => tailAnchor i k) Filter.atTop (nhds 0) := by
  have h := tendsto_sum_nat_add (f := fun l => blockAnchor i l)
  refine h.congr fun k => ?_
  rw [tailAnchor]
  exact tsum_congr fun l => by rw [Nat.add_comm]

end Erdos266
