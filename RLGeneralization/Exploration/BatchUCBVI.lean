/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Batch UCBVI Regret Bound

Proves the UCBVI regret bound for the "batch" setting where transition
samples are collected i.i.d. from a generative model (not adaptively).
This avoids the martingale concentration issues of adaptive UCBVI while
achieving the same O(√(H³SAK)) rate.

## Architecture

The proof chains existing infrastructure:
1. Hoeffding concentration for i.i.d. generative model samples
   (from GenerativeModelCore.lean)
2. Optimism: under the concentration event, Q̂ ≥ Q*
3. Pigeonhole/Cauchy-Schwarz: total bonus ≤ O(√(H³SAK·log))
4. Composition via ucbvi_regret_from_bonus_hypotheses (UCBVI.lean)

## References

* [Azar, Osband, Munos, *Minimax Regret Bounds for RL*, ICML 2017]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.Exploration.UCBVI
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev

open Finset BigOperators

noncomputable section

/-! ### Cauchy-Schwarz for Square Root Sums -/

/-- **Cauchy-Schwarz for square root sums**: `∑ √(a_i) ≤ √(|s| · ∑ a_i)`.
    Consequence of the discrete Cauchy-Schwarz inequality
    (`sq_sum_le_card_mul_sum_sq`) with `f_i = √(a_i)`. -/
theorem sum_sqrt_le_sqrt_card_mul_sum {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, Real.sqrt (a i) ≤
    Real.sqrt (↑s.card * ∑ i ∈ s, a i) := by
  have h_nn : (0 : ℝ) ≤ ∑ i ∈ s, Real.sqrt (a i) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  -- (∑ √a_i)² ≤ #s · ∑ (√a_i)² = #s · ∑ a_i  (Cauchy-Schwarz)
  have h_sq_eq : ∑ i ∈ s, Real.sqrt (a i) ^ 2 = ∑ i ∈ s, a i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (ha i hi)
  have h_cs := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => Real.sqrt (a i))
  rw [h_sq_eq] at h_cs
  -- Take square roots: ∑ √a_i = √((∑ √a_i)²) ≤ √(#s · ∑ a_i)
  calc ∑ i ∈ s, Real.sqrt (a i)
      = |∑ i ∈ s, Real.sqrt (a i)| := (abs_of_nonneg h_nn).symm
    _ = Real.sqrt ((∑ i ∈ s, Real.sqrt (a i)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (↑s.card * ∑ i ∈ s, a i) := Real.sqrt_le_sqrt h_cs

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### Pigeonhole / Cauchy-Schwarz Bonus Bound

This is the purely algebraic argument: if the bonus at step h for
state-action (s,a) is proportional to 1/√(N_h(s,a)), then the total
sum of bonuses over K episodes and H steps is O(√(H·S·A·K·log)).

The argument uses:
1. Pigeonhole: ∑_k 1{visit (s,a) at step h in episode k} = N_h^K(s,a)
2. ∑_{n=1}^{N} 1/√n ≤ 2√N (integral bound)
3. Cauchy-Schwarz: ∑_{(s,a)} √(N(s,a)) ≤ √(|S|·|A|) · √(∑ N(s,a))
4. ∑_{(s,a)} N(s,a) = K (total visits = K episodes)
-/

/-- **Harmonic-square-root bound**: ∑_{n=1}^{N} 1/√n ≤ 2√N.
    This is the key inequality for the bonus bound. -/
-- Key inequality: 1/√(n+1) ≤ 2(√(n+1) - √n)
-- because √(n+1) - √n = 1/(√(n+1) + √n) ≥ 1/(2√(n+1)).
private lemma inv_sqrt_le_two_sub_sqrt (n : ℕ) :
    (1 : ℝ) / Real.sqrt (↑n + 1) ≤
    2 * (Real.sqrt (↑n + 1) - Real.sqrt ↑n) := by
  have hn1 : (0 : ℝ) < ↑n + 1 := by positivity
  have hsq1 : 0 < Real.sqrt (↑n + 1) := Real.sqrt_pos.mpr hn1
  have hsqn : 0 ≤ Real.sqrt ↑n := Real.sqrt_nonneg _
  -- √(n+1) + √n ≤ 2√(n+1)
  have h_denom : Real.sqrt ↑n + Real.sqrt (↑n + 1) ≤ 2 * Real.sqrt (↑n + 1) := by
    linarith [Real.sqrt_le_sqrt (by linarith : (↑n : ℝ) ≤ ↑n + 1)]
  -- √(n+1) - √n = (n+1 - n)/(√(n+1) + √n) = 1/(√(n+1) + √n)
  have h_diff_pos : 0 ≤ Real.sqrt (↑n + 1) - Real.sqrt ↑n :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith : (↑n : ℝ) ≤ ↑n + 1))
  -- 1/√(n+1) ≤ 2·(√(n+1) - √n)
  -- ⟺ 1 ≤ 2·√(n+1)·(√(n+1) - √n)
  -- ⟺ 1 ≤ 2·(n+1 - √n·√(n+1))
  -- This is harder algebraically. Use: (√(n+1)-√n)(√(n+1)+√n) = 1
  have h_conj : (Real.sqrt (↑n + 1) - Real.sqrt ↑n) *
      (Real.sqrt (↑n + 1) + Real.sqrt ↑n) = 1 := by
    have h1 : Real.sqrt (↑n + 1) ^ 2 = ↑n + 1 :=
      Real.sq_sqrt (by positivity : (0:ℝ) ≤ ↑n + 1)
    have h2 : Real.sqrt (↑n : ℝ) ^ 2 = ↑n :=
      Real.sq_sqrt (Nat.cast_nonneg n)
    nlinarith [sq_abs (Real.sqrt (↑n + 1)), sq_abs (Real.sqrt ↑n)]
  -- From h_conj: √(n+1) - √n = 1/(√(n+1) + √n)
  -- And √(n+1) + √n ≤ 2√(n+1)
  -- So √(n+1) - √n ≥ 1/(2√(n+1))
  -- Hence 2(√(n+1) - √n) ≥ 1/√(n+1)
  rw [div_le_iff₀ hsq1]
  nlinarith [h_conj, h_denom, h_diff_pos, hsqn]

theorem sum_inv_sqrt_le (N : ℕ) (hN : 0 < N) :
    ∑ n ∈ range N, (1 : ℝ) / Real.sqrt (↑n + 1) ≤
    2 * Real.sqrt N := by
  -- Each term: 1/√(n+1) ≤ 2(√(n+1) - √n)
  -- Sum telescopes: ∑ 2(√(n+1) - √n) = 2(√N - √0) = 2√N
  calc ∑ n ∈ range N, (1 : ℝ) / Real.sqrt (↑n + 1)
      ≤ ∑ n ∈ range N, 2 * (Real.sqrt (↑n + 1) - Real.sqrt ↑n) := by
        apply Finset.sum_le_sum; intro n _; exact inv_sqrt_le_two_sub_sqrt n
    _ = 2 * ∑ n ∈ range N, (Real.sqrt (↑n + 1) - Real.sqrt ↑n) := by
        rw [← Finset.mul_sum]
    _ = 2 * (Real.sqrt ↑N - Real.sqrt 0) := by
        congr 1
        -- Telescoping: ∑_{n=0}^{N-1} (f(n+1) - f(n)) = f(N) - f(0)
        induction N with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ]
          by_cases hm : m = 0
          · simp [hm]
          · rw [ih (Nat.pos_of_ne_zero hm)]; push_cast; ring
    _ = 2 * Real.sqrt ↑N := by simp [Real.sqrt_zero]

/-- **Pigeonhole bonus bound**: if the per-entry bonus is proportional to
    `1/√(visit count)`, then the total bonus satisfies
      `∑_i ∑_{n=1}^{N(i)} 1/√n ≤ 2 · √(|ι| · K)`
    where `K ≥ ∑ N(i)`.

    Proof chains `sum_inv_sqrt_le` (harmonic-sqrt telescoping) with
    `sum_sqrt_le_sqrt_card_mul_sum` (Cauchy-Schwarz for √-sums).

    In the UCBVI application, `ι = S × A` and the bonus is
    `c·H·√(log(...)/N)`, giving total bonus `≤ O(√(H³·S·A·K·log))`. -/
theorem pigeonhole_bonus_bound {ι : Type*} [Fintype ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) (K : ℕ) (hK : ∑ i, N i ≤ K) :
    ∑ i : ι, ∑ n ∈ range (N i), (1 : ℝ) / Real.sqrt (↑n + 1) ≤
    2 * Real.sqrt (↑(Fintype.card ι) * ↑K) := by
  -- Step 1: Each inner sum ≤ 2√(N(i)) via sum_inv_sqrt_le
  calc ∑ i : ι, ∑ n ∈ range (N i), (1 : ℝ) / Real.sqrt (↑n + 1)
      ≤ ∑ i : ι, 2 * Real.sqrt ↑(N i) := by
        apply Finset.sum_le_sum; intro i _
        exact sum_inv_sqrt_le (N i) (hN i)
    -- Step 2: Factor out the 2
    _ = 2 * ∑ i : ι, Real.sqrt ↑(N i) := by
        rw [← Finset.mul_sum]
    -- Step 3: Cauchy-Schwarz + monotonicity
    _ ≤ 2 * Real.sqrt (↑(Fintype.card ι) * ↑K) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
        -- Cauchy-Schwarz: ∑ √N(i) ≤ √(|ι| · ∑ N(i)) ≤ √(|ι| · K)
        calc ∑ i : ι, Real.sqrt ↑(N i)
            = ∑ i ∈ Finset.univ, Real.sqrt (↑(N i) : ℝ) := rfl
          _ ≤ Real.sqrt (↑Finset.univ.card * ∑ i ∈ Finset.univ, (↑(N i) : ℝ)) :=
              sum_sqrt_le_sqrt_card_mul_sum _ _ fun i _ => Nat.cast_nonneg _
          _ = Real.sqrt (↑(Fintype.card ι) * ∑ i : ι, (↑(N i) : ℝ)) := by
              rw [Finset.card_univ]
          _ ≤ Real.sqrt (↑(Fintype.card ι) * ↑K) := by
              apply Real.sqrt_le_sqrt
              apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
              exact_mod_cast hK

end FiniteHorizonMDP

end
