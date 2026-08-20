/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import Erdos266.Defs

/-!
# Growth data for the construction

The sequence of sample scales is `N k = 2^(k²)` (design decision 1 of
`docs/plan.md`, replacing the paper's spliced factorials), with block width
`M k = min (N k / 4k) (√(N k))`.  This file proves the elementary
arithmetic the algorithm needs:

* `bigN_succ`: `N (k+1) = 2^(2k+1) · N k` — hence very fast growth;
* `bigM` bounds: `4k·M k ≤ N k`, `M k ² ≤ N k`, positivity from `k ≥ 2`,
  `2·M k < N k`, and the cross-block separation
  `k·N k + M k + M (k+1) < N (k+1)`;
* `growth_eventually`: for any fixed dimension `d` and constants
  `D, ε > 0`, the lattice-step error `D(1/N_k^(i+2) + M_k²/N_k^(i+3))`
  is eventually dominated by the next radius `ε·M_(k+1)/N_(k+1)^(i+2)`,
  uniformly in `i < d` — the condition (7.17) of [KoTa24] that decides
  when dimension `d` may enter the construction;
* crude bounds for `f`: positivity and `f i x ≤ (2/x)^i` for `x ≥ 2i`,
  which the tail estimates of the convergence step use.
-/

namespace Erdos266

open Finset

/-- The sample scale `N k = 2^(k²)`. -/
def bigN (k : ℕ) : ℕ := 2 ^ (k ^ 2)

/-- The block width `M k = min (N k / 4k) (√(N k))`. -/
def bigM (k : ℕ) : ℕ := min (bigN k / (4 * k)) (Nat.sqrt (bigN k))

lemma one_le_bigN (k : ℕ) : 1 ≤ bigN k := Nat.one_le_two_pow

lemma bigN_pos (k : ℕ) : 0 < bigN k := one_le_bigN k

lemma bigN_succ (k : ℕ) : bigN (k + 1) = 2 ^ (2 * k + 1) * bigN k := by
  rw [bigN, bigN, ← pow_add]
  congr 1
  ring

lemma bigN_strictMono : StrictMono bigN := by
  intro a b hab
  apply Nat.pow_lt_pow_right (by norm_num)
  exact Nat.pow_lt_pow_left hab (by norm_num)

lemma four_mul_bigM_le (k : ℕ) : 4 * k * bigM k ≤ bigN k := by
  calc 4 * k * bigM k ≤ 4 * k * (bigN k / (4 * k)) := by
        exact Nat.mul_le_mul_left _ (min_le_left _ _)
  _ ≤ bigN k := Nat.mul_div_le _ _

lemma bigM_sq_le (k : ℕ) : bigM k * bigM k ≤ bigN k := by
  have h := Nat.sqrt_le' (bigN k)
  rw [pow_two] at h
  exact le_trans (Nat.mul_le_mul (min_le_right _ _) (min_le_right _ _)) h

lemma bigM_le_sqrt (k : ℕ) : bigM k ≤ Nat.sqrt (bigN k) := min_le_right _ _

/-- `2^k` dominates `k+1`. -/
lemma succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self

lemma one_le_bigM {k : ℕ} (hk : 2 ≤ k) : 1 ≤ bigM k := by
  rw [bigM, le_min_iff]
  constructor
  · -- N k ≥ 4k, so the quotient is at least 1
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h1 : k + 2 ≤ k ^ 2 := by nlinarith
    calc 1 * (4 * k) = 4 * k := by ring
    _ ≤ 4 * 2 ^ k := by
        have := succ_le_two_pow k
        omega
    _ = 2 ^ (k + 2) := by ring
    _ ≤ 2 ^ (k ^ 2) := Nat.pow_le_pow_right (by norm_num) h1
    _ = bigN k := rfl
  · -- √(N k) ≥ 1 since N k ≥ 1
    have h := one_le_bigN k
    exact Nat.le_sqrt.mpr (by omega)

lemma sixteen_le_bigN {k : ℕ} (hk : 2 ≤ k) : 16 ≤ bigN k := by
  calc (16:ℕ) = 2 ^ 4 := by norm_num
  _ ≤ 2 ^ (k ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  _ = bigN k := rfl

lemma two_mul_bigM_lt {k : ℕ} (hk : 2 ≤ k) : 2 * bigM k < bigN k := by
  have h16 := sixteen_le_bigN hk
  have hs : 4 ≤ Nat.sqrt (bigN k) := Nat.le_sqrt.mpr (by omega)
  have hM := bigM_le_sqrt k
  have h1 : 4 * Nat.sqrt (bigN k) ≤ Nat.sqrt (bigN k) * Nat.sqrt (bigN k) :=
    Nat.mul_le_mul_right _ hs
  have h2 : Nat.sqrt (bigN k) * Nat.sqrt (bigN k) ≤ bigN k := by
    have h := Nat.sqrt_le' (bigN k)
    rwa [pow_two] at h
  omega

/-- Cross-block separation: everything in block `k` (at most `k·N k + M k`)
is strictly below everything in block `k+1` (at least `N (k+1) - M (k+1)`). -/
lemma cross_block {k : ℕ} (hk : 2 ≤ k) :
    k * bigN k + bigM k + bigM (k + 1) < bigN (k + 1) := by
  have h1 : bigM k < bigN k := by
    have := two_mul_bigM_lt hk
    omega
  have h2 : 2 * bigM (k + 1) < bigN (k + 1) := two_mul_bigM_lt (by omega)
  have h3 : 2 * (k + 1) * bigN k ≤ bigN (k + 1) := by
    rw [bigN_succ]
    have h4 : 2 * (k + 1) ≤ 2 ^ (2 * k + 1) := by
      have h5 := succ_le_two_pow (2 * k)
      have : 2 * (k + 1) ≤ 2 * (2 * k + 1) := by omega
      calc 2 * (k + 1) ≤ 2 * (2 * k + 1) := this
      _ ≤ 2 * 2 ^ (2 * k) := by omega
      _ = 2 ^ (2 * k + 1) := by ring
    exact Nat.mul_le_mul_right _ h4
  nlinarith [bigN_pos k, bigN_pos (k + 1)]

/-- Linear functions are eventually dominated by `k²`. -/
lemma quad_dom (c₀ c₁ : ℕ) : ∀ k, c₀ + c₁ + 2 ≤ k → c₁ * k + c₀ ≤ k * k := by
  intro k hk
  calc c₁ * k + c₀ ≤ c₁ * k + k := by omega
  _ = (c₁ + 1) * k := by ring
  _ ≤ k * k := Nat.mul_le_mul_right k (by omega)

/-- **The eventual-domination condition** that admits dimension `d` into the
construction: for large `k` the lattice-step error at scale `k` fits inside
the invariant radius at scale `k+1`, uniformly in the coordinate `i < d`. -/
theorem growth_eventually (d : ℕ) (Dc εc : ℝ) (hD : 0 < Dc) (hε : 0 < εc) :
    ∃ K₀ : ℕ, 2 ≤ K₀ ∧ ∀ k, K₀ ≤ k → ∀ i : ℕ, i < d →
      Dc * (1 / (bigN k : ℝ) ^ (i + 2) + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i + 3))
        ≤ εc * (bigM (k + 1) : ℝ) / (bigN (k + 1) : ℝ) ^ (i + 2) := by
  -- a power of two absorbing the ratio of the constants
  obtain ⟨r₀, hr₀⟩ := pow_unbounded_of_one_lt (2 * Dc / εc) (by norm_num : (1:ℝ) < 2)
  set K₀ : ℕ := (2 * (d + 1) + 2 * r₀ + (d + 1) + r₀ + 3) + (4 * (d + 1) + 2 * (d + 1) + 1) + 4
    with hK₀def
  refine ⟨K₀, by omega, ?_⟩
  intro k hk i hi
  have hNpos : (0:ℝ) < (bigN k : ℝ) := by exact_mod_cast bigN_pos k
  have hNpos' : (0:ℝ) < (bigN (k+1) : ℝ) := by exact_mod_cast bigN_pos (k+1)
  have hMpos' : (1:ℝ) ≤ (bigM (k+1) : ℝ) := by
    exact_mod_cast one_le_bigM (show 2 ≤ k + 1 by omega)
  -- Step 1: the error is at most `2Dc/N_k^(i+2)` because `M_k² ≤ N_k`
  have hstep1 : Dc * (1 / (bigN k : ℝ) ^ (i + 2) + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i + 3))
      ≤ 2 * Dc / (bigN k : ℝ) ^ (i + 2) := by
    have hM2 : (bigM k : ℝ) ^ 2 ≤ (bigN k : ℝ) := by
      have := bigM_sq_le k
      have h := this
      rw [pow_two]
      exact_mod_cast h
    have h2 : (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i + 3) ≤ 1 / (bigN k : ℝ) ^ (i + 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      calc (bigM k : ℝ) ^ 2 * (bigN k : ℝ) ^ (i + 2)
          ≤ (bigN k : ℝ) * (bigN k : ℝ) ^ (i + 2) :=
            mul_le_mul_of_nonneg_right hM2 (by positivity)
      _ = (bigN k : ℝ) ^ (i + 3) := by
            rw [← pow_succ']
    have h3 : Dc * (1 / (bigN k : ℝ) ^ (i + 2) + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i + 3))
        ≤ Dc * (1 / (bigN k : ℝ) ^ (i + 2) + 1 / (bigN k : ℝ) ^ (i + 2)) := by
      refine mul_le_mul_of_nonneg_left (by linarith) hD.le
    calc Dc * (1 / (bigN k : ℝ) ^ (i + 2) + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i + 3))
        ≤ Dc * (1 / (bigN k : ℝ) ^ (i + 2) + 1 / (bigN k : ℝ) ^ (i + 2)) := h3
    _ = 2 * Dc / (bigN k : ℝ) ^ (i + 2) := by ring
  refine hstep1.trans ?_
  -- Step 2: reduce to an inequality about `M (k+1)` and powers of two
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- `2Dc · N_(k+1)^(i+2) ≤ εc · M_(k+1) · N_k^(i+2)`
  have hNratio : (bigN (k+1) : ℝ) ^ (i + 2)
      = (2:ℝ) ^ ((2 * k + 1) * (i + 2)) * (bigN k : ℝ) ^ (i + 2) := by
    rw [show bigN (k+1) = 2 ^ (2 * k + 1) * bigN k from bigN_succ k]
    push_cast
    rw [mul_pow, ← pow_mul]
  rw [hNratio]
  -- key: `2Dc · 2^((2k+1)(i+2)) ≤ εc · M_(k+1)`
  have hkey : 2 * Dc * (2:ℝ) ^ ((2 * k + 1) * (i + 2)) ≤ εc * (bigM (k+1) : ℝ) := by
    set E : ℕ := (2 * k + 1) * (d + 1) + r₀ with hEdef
    -- `M (k+1) ≥ 2^E` for `k ≥ K₀`
    have hMlow : (2:ℕ) ^ E ≤ bigM (k + 1) := by
      rw [bigM, le_min_iff]
      have hsq : (k + 2) * (k + 2) ≤ (k + 1) ^ 2 * 2 := by nlinarith
      constructor
      · -- division branch: `2^E · 4(k+1) ≤ N (k+1)`
        rw [Nat.le_div_iff_mul_le (by omega)]
        have h4k : 4 * (k + 1) ≤ 2 ^ (k + 3) := by
          have := succ_le_two_pow k
          calc 4 * (k + 1) ≤ 4 * 2 ^ k := by omega
          _ = 2 ^ (k + 2) := by ring
          _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
        calc 2 ^ E * (4 * (k + 1)) ≤ 2 ^ E * 2 ^ (k + 3) :=
              Nat.mul_le_mul_left _ h4k
        _ = 2 ^ (E + (k + 3)) := by rw [← pow_add]
        _ ≤ 2 ^ ((k + 1) ^ 2) := by
              apply Nat.pow_le_pow_right (by norm_num)
              have := quad_dom ((d + 1) + r₀ + 3 + 2 * (d + 1))
                (2 * (d + 1) + 1) k (by omega)
              nlinarith
        _ = bigN (k + 1) := rfl
      · -- square-root branch: `(2^E)² ≤ N (k+1)`
        rw [Nat.le_sqrt]
        calc 2 ^ E * 2 ^ E = 2 ^ (E + E) := by rw [← pow_add]
        _ ≤ 2 ^ ((k + 1) ^ 2) := by
              apply Nat.pow_le_pow_right (by norm_num)
              have := quad_dom (2 * ((d + 1) + r₀))
                (2 * (2 * (d + 1))) k (by omega)
              nlinarith
        _ = bigN (k + 1) := rfl
    have hMlowR : (2:ℝ) ^ E ≤ (bigM (k+1) : ℝ) := by
      have : ((2:ℕ) ^ E : ℝ) ≤ (bigM (k+1) : ℝ) := by exact_mod_cast hMlow
      push_cast at this
      exact this
    -- `2Dc ≤ εc·2^(r₀)` and `(2k+1)(i+2) + r₀ ≤ E`... assemble
    have hexp : (2 * k + 1) * (i + 2) + r₀ ≤ E := by
      rw [hEdef]
      have : (2 * k + 1) * (i + 2) ≤ (2 * k + 1) * (d + 1) := by
        exact Nat.mul_le_mul_left _ (by omega)
      omega
    have hpow_split : (2:ℝ) ^ E
        = (2:ℝ) ^ ((2 * k + 1) * (i + 2)) * 2 ^ (E - (2 * k + 1) * (i + 2)) := by
      rw [← pow_add]
      congr 1
      omega
    have hr₀' : 2 * Dc ≤ εc * 2 ^ r₀ := by
      rw [div_lt_iff₀ hε] at hr₀
      -- hr₀ : 2 * Dc / εc < 2 ^ r₀ — after rw: 2 * Dc < 2 ^ r₀ * εc
      linarith
    have hr₀E : (2:ℝ) ^ r₀ ≤ 2 ^ (E - (2 * k + 1) * (i + 2)) := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    calc 2 * Dc * (2:ℝ) ^ ((2 * k + 1) * (i + 2))
        ≤ (εc * 2 ^ r₀) * (2:ℝ) ^ ((2 * k + 1) * (i + 2)) :=
          mul_le_mul_of_nonneg_right hr₀' (by positivity)
    _ ≤ (εc * 2 ^ (E - (2 * k + 1) * (i + 2))) * (2:ℝ) ^ ((2 * k + 1) * (i + 2)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hr₀E hε.le
    _ = εc * (2:ℝ) ^ E := by
          rw [hpow_split]
          ring
    _ ≤ εc * (bigM (k+1) : ℝ) := mul_le_mul_of_nonneg_left hMlowR hε.le
  calc 2 * Dc * ((2:ℝ) ^ ((2 * k + 1) * (i + 2)) * (bigN k : ℝ) ^ (i + 2))
      = (2 * Dc * (2:ℝ) ^ ((2 * k + 1) * (i + 2))) * (bigN k : ℝ) ^ (i + 2) := by ring
  _ ≤ (εc * (bigM (k+1) : ℝ)) * (bigN k : ℝ) ^ (i + 2) :=
      mul_le_mul_of_nonneg_right hkey (by positivity)
  _ = εc * (bigM (k+1) : ℝ) * (bigN k : ℝ) ^ (i + 2) := by ring

/-! ### Crude bounds for `f` -/

/-- For `x ≥ 2i` every factor of `f i x` is at least `x/2`. -/
lemma factor_ge {i j : ℕ} (hj : j ∈ range i) {x : ℝ} (hx : (2 * i : ℝ) ≤ x) :
    x / 2 ≤ x + (tSeq j : ℝ) := by
  have h1 : |(tSeq j : ℝ)| ≤ (i : ℝ) := by
    have h2 : |tSeq j| ≤ (j : ℚ) + 1 := abs_tSeq_le j
    have h3 : |(tSeq j : ℝ)| ≤ (j : ℝ) + 1 := by exact_mod_cast h2
    have h4 : (j : ℝ) + 1 ≤ i := by exact_mod_cast mem_range.mp hj
    linarith
  rw [abs_le] at h1
  linarith [h1.1]

lemma f_pos {i : ℕ} {x : ℝ} (hx : (2 * i : ℝ) ≤ x) (hx0 : 0 < x) : 0 < f i x := by
  rw [f]
  apply inv_pos.mpr
  apply prod_pos
  intro j hj
  have := factor_ge hj hx
  linarith [half_pos hx0]

lemma f_le {i : ℕ} {x : ℝ} (hx : (2 * i : ℝ) ≤ x) (hx0 : 0 < x) :
    f i x ≤ (2 / x) ^ i := by
  rw [f]
  have hprod : (x / 2) ^ i ≤ ∏ j ∈ range i, (x + (tSeq j : ℝ)) := by
    calc (x / 2) ^ i = ∏ _j ∈ range i, (x / 2) := by rw [prod_const, card_range]
    _ ≤ ∏ j ∈ range i, (x + (tSeq j : ℝ)) :=
        prod_le_prod (fun j _ => (half_pos hx0).le) fun j hj => factor_ge hj hx
  have h1 : (0:ℝ) < (x / 2) ^ i := by positivity
  calc (∏ j ∈ range i, (x + (tSeq j : ℝ)))⁻¹
      ≤ ((x / 2) ^ i)⁻¹ := inv_anti₀ h1 hprod
  _ = (2 / x) ^ i := by
        rw [← inv_pow, inv_div]

end Erdos266
