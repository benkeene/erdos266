/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
import Mathlib

/-!
# A growth-bounded enumeration of `ℚ`

The Kovač–Tao argument fixes an enumeration `(tᵢ)` of `ℚ` with `|tᵢ| ≤ i`
(condition (7.1) of the paper).  This file constructs one, 0-indexed:
`tSeq : ℕ → ℚ` is a bijection with `|tSeq j| ≤ j + 1`.

The construction is greedy over a fixed `Denumerable` enumeration of `ℚ`:
at stage `i`, pick the enumerated rational of least index that has not been
picked before and has absolute value at most `i + 1`.  Such a rational
exists because `[0, 1]` is infinite and the picked prefix is finite.
Injectivity is immediate; surjectivity is a pigeonhole argument: a rational
`q` that is never picked is a candidate at every stage `i ≥ ⌈|q|⌉`, so the
greedy choice at each such stage has enumeration index at most that of `q`,
and there are only finitely many such indices for infinitely many stages.
-/

namespace Erdos266

/-- A fixed enumeration of `ℚ`. -/
def qEnum : ℕ ≃ ℚ := (Denumerable.eqv ℚ).symm

/-- Any finite list of rationals misses some enumerated rational of absolute
value at most `i + 1`. -/
lemma exists_fresh (i : ℕ) (l : List ℚ) :
    ∃ m : ℕ, qEnum m ∉ l ∧ |qEnum m| ≤ (i : ℚ) + 1 := by
  have hIcc : (Set.Icc (0 : ℚ) 1).Infinite :=
    Set.infinite_coe_iff.mp (Set.Icc.infinite (by norm_num))
  have hsub : Set.Icc (0 : ℚ) 1 ⊆ {q : ℚ | |q| ≤ (i : ℚ) + 1} := by
    intro q hq
    have h0 : (0 : ℚ) ≤ (i : ℚ) := Nat.cast_nonneg i
    rw [Set.mem_ofPred_eq, abs_le]
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hdiff : ({q : ℚ | |q| ≤ (i : ℚ) + 1} \ {q | q ∈ l}).Infinite :=
    (hIcc.mono hsub).sdiff l.finite_toSet
  obtain ⟨q, hq⟩ := hdiff.nonempty
  refine ⟨qEnum.symm q, ?_, ?_⟩
  · rw [Equiv.apply_symm_apply]
    exact hq.2
  · rw [Equiv.apply_symm_apply]
    exact hq.1

/-- The list of rationals picked before stage `i`. -/
def picks : ℕ → List ℚ
  | 0 => []
  | i + 1 => picks i ++ [qEnum (Nat.find (exists_fresh i (picks i)))]

/-- The enumeration index picked at stage `i`. -/
def pickIdx (i : ℕ) : ℕ := Nat.find (exists_fresh i (picks i))

/-- The growth-bounded enumeration of `ℚ`. -/
def tSeq (i : ℕ) : ℚ := qEnum (pickIdx i)

lemma picks_succ (i : ℕ) : picks (i + 1) = picks i ++ [tSeq i] := rfl

lemma tSeq_not_mem_picks (i : ℕ) : tSeq i ∉ picks i :=
  (Nat.find_spec (exists_fresh i (picks i))).1

/-- The growth condition (7.1). -/
lemma abs_tSeq_le (i : ℕ) : |tSeq i| ≤ (i : ℚ) + 1 :=
  (Nat.find_spec (exists_fresh i (picks i))).2

lemma mem_picks {q : ℚ} {i : ℕ} : q ∈ picks i ↔ ∃ j < i, tSeq j = q := by
  induction i with
  | zero => simp [picks]
  | succ i ih =>
    rw [picks_succ, List.mem_append, List.mem_singleton, ih]
    constructor
    · rintro (⟨j, hj, rfl⟩ | rfl)
      · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
      · exact ⟨i, Nat.lt_succ_self i, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
      · exact Or.inl ⟨j, h, rfl⟩
      · exact Or.inr rfl

lemma tSeq_injective : Function.Injective tSeq := by
  intro a b hab
  by_contra hne
  wlog h : a < b generalizing a b
  · exact this hab.symm (Ne.symm hne) ((Ne.lt_or_gt hne).resolve_left h)
  exact tSeq_not_mem_picks b (mem_picks.mpr ⟨a, h, hab⟩)

lemma pickIdx_injective : Function.Injective pickIdx := fun _ _ hab =>
  tSeq_injective (congrArg qEnum hab)

lemma tSeq_surjective : Function.Surjective tSeq := by
  intro q
  by_contra hq
  push Not at hq
  set m := qEnum.symm q with hm
  -- at every late enough stage, `q` is a candidate, so the greedy index is `≤ m`
  have key : ∀ i : ℕ, |q| ≤ (i : ℚ) + 1 → pickIdx i ≤ m := by
    intro i hqi
    apply Nat.find_min'
    constructor
    · rw [hm, Equiv.apply_symm_apply, mem_picks]
      rintro ⟨j, _, hjq⟩
      exact hq j hjq
    · rw [hm, Equiv.apply_symm_apply]
      exact hqi
  have hbound : ∀ i, ⌈|q|⌉₊ ≤ i → pickIdx i ≤ m := by
    intro i hi
    apply key
    calc |q| ≤ (⌈|q|⌉₊ : ℚ) := Nat.le_ceil _
    _ ≤ (i : ℚ) := by exact_mod_cast hi
    _ ≤ (i : ℚ) + 1 := by linarith
  -- pigeonhole: `m + 2` stages, at most `m + 1` available indices
  have hmaps : ∀ i ∈ Finset.Icc ⌈|q|⌉₊ (⌈|q|⌉₊ + m + 1),
      pickIdx i ∈ Finset.range (m + 1) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact hbound i (Finset.mem_Icc.mp hi).1
  have hinj : Set.InjOn pickIdx (Finset.Icc ⌈|q|⌉₊ (⌈|q|⌉₊ + m + 1)) :=
    fun a _ b _ h => pickIdx_injective h
  have hcard := Finset.card_le_card_of_injOn pickIdx hmaps hinj
  rw [Nat.card_Icc, Finset.card_range] at hcard
  omega

lemma tSeq_bijective : Function.Bijective tSeq :=
  ⟨tSeq_injective, tSeq_surjective⟩

/-- There is an enumeration of `ℚ` with linear growth: condition (7.1) of
[KoTa24], 0-indexed. -/
theorem exists_growth_enumeration :
    ∃ t : ℕ → ℚ, Function.Bijective t ∧ ∀ j : ℕ, |t j| ≤ (j : ℚ) + 1 :=
  ⟨tSeq, tSeq_bijective, abs_tSeq_le⟩

end Erdos266
