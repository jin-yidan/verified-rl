/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Bellman Rank Auxiliary Results

Trusted structural Bellman-rank definitions and exact bilinear-error bounds.

## Main Results

* `BellmanRankBound` - Bellman-rank structure for an MDP and hypothesis class
* `inner_product_le_of_norm_bound` - Cauchy-Schwarz for finite sums
* `bellman_error_le_of_rank` - Bellman error bounded via bilinear rank
* `episode_bellman_error_le_H` - Per-episode Bellman error bounded by the horizon

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.MDP.FiniteHorizon

open Finset BigOperators

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-- A hypothesis class for value-function approximation:
    a finite set of candidate Q-functions indexed by `Fin n`. -/
structure HypothesisClass where
  /-- Number of hypothesis functions -/
  n : ℕ
  /-- Each hypothesis is a Q-function for each step -/
  f : Fin n → Fin M.H → M.S → M.A → ℝ

/-- The Bellman error of hypothesis `f` at step `h` under policy `pi`,
    averaged over states. -/
def bellmanError (F : M.HypothesisClass) (j : Fin F.n)
    (pi : Fin M.H → M.S → M.A) (h : Fin M.H)
    (s : M.S) : ℝ :=
  let a := pi h s
  (M.r h s a + ∑ s', M.P h s a s' *
    Finset.univ.sup' Finset.univ_nonempty
      (fun a' => F.f j h s' a')) - F.f j h s a

/-- Bellman-rank structure for an MDP and hypothesis class. -/
structure BellmanRankBound where
  /-- The hypothesis class -/
  F : M.HypothesisClass
  /-- Bellman rank dimension -/
  d : ℕ
  /-- Policy-side embedding: each policy maps to `R^d` per step -/
  X : (Fin M.H → M.S → M.A) → Fin M.H → Fin d → ℝ
  /-- Hypothesis-side embedding: each `f` maps to `R^d` per step -/
  W : Fin F.n → Fin M.H → Fin d → ℝ
  /-- Bilinear decomposition: total Bellman error = `<X, W>` -/
  decomp : ∀ (pi : Fin M.H → M.S → M.A) (j : Fin F.n)
    (h : Fin M.H),
    ∑ s : M.S, M.bellmanError F j pi h s =
    ∑ i : Fin d, X pi h i * W j h i
  /-- `X` vectors have bounded norm -/
  X_bound : ∀ pi h, ∑ i : Fin d, (X pi h i) ^ 2 ≤ 1
  /-- `W` vectors have bounded norm -/
  W_bound : ∀ j h, ∑ i : Fin d, (W j h i) ^ 2 ≤ 1

/-- Cauchy-Schwarz inequality for finite-dimensional inner products
with unit-norm bounds. -/
theorem inner_product_le_of_norm_bound {d : ℕ}
    (u v : Fin d → ℝ)
    (hu : ∑ i : Fin d, (u i) ^ 2 ≤ 1)
    (hv : ∑ i : Fin d, (v i) ^ 2 ≤ 1) :
    ∑ i : Fin d, u i * v i ≤ 1 := by
  have h_amgm : ∀ i : Fin d, u i * v i ≤ ((u i) ^ 2 + (v i) ^ 2) / 2 := by
    intro i
    have : 0 ≤ (u i - v i) ^ 2 := sq_nonneg _
    nlinarith
  calc
    ∑ i : Fin d, u i * v i
      ≤ ∑ i : Fin d, ((u i) ^ 2 + (v i) ^ 2) / 2 :=
        Finset.sum_le_sum (fun i _ => h_amgm i)
    _ = (1 / 2) * ∑ i : Fin d, ((u i) ^ 2 + (v i) ^ 2) := by
        simp_rw [div_eq_inv_mul]
        rw [← Finset.mul_sum]
        norm_num
    _ = (1 / 2) * (∑ i : Fin d, (u i) ^ 2 + ∑ i : Fin d, (v i) ^ 2) := by
        rw [← Finset.sum_add_distrib]
    _ ≤ (1 / 2) * (1 + 1) := by
        linarith
    _ = 1 := by
        norm_num

/-- Variant with absolute value: `|<u, v>| ≤ 1` for unit-norm vectors. -/
theorem abs_inner_product_le_of_norm_bound {d : ℕ}
    (u v : Fin d → ℝ)
    (hu : ∑ i : Fin d, (u i) ^ 2 ≤ 1)
    (hv : ∑ i : Fin d, (v i) ^ 2 ≤ 1) :
    |∑ i : Fin d, u i * v i| ≤ 1 := by
  rw [abs_le]
  constructor
  · have h_neg : ∑ i : Fin d, (-u i) * v i ≤ 1 := by
      have hu' : ∑ i : Fin d, (-u i) ^ 2 ≤ 1 := by
        simp only [neg_sq]
        exact hu
      exact inner_product_le_of_norm_bound _ _ hu' hv
    have : ∑ i : Fin d, (-u i) * v i = -(∑ i : Fin d, u i * v i) := by
      simp [neg_mul, Finset.sum_neg_distrib]
    linarith
  · exact inner_product_le_of_norm_bound u v hu hv

/-- Using the bilinear decomposition and Cauchy-Schwarz, the total
Bellman error at any step is bounded by one in absolute value. -/
theorem bellman_error_le_of_rank (brb : M.BellmanRankBound)
    (pi : Fin M.H → M.S → M.A) (j : Fin brb.F.n)
    (h : Fin M.H) :
    |∑ s : M.S, M.bellmanError brb.F j pi h s| ≤ 1 := by
  rw [brb.decomp pi j h]
  exact abs_inner_product_le_of_norm_bound
    (brb.X pi h) (brb.W j h) (brb.X_bound pi h) (brb.W_bound j h)

/-- Non-absolute Bellman-error bound. -/
theorem bellman_error_le_one (brb : M.BellmanRankBound)
    (pi : Fin M.H → M.S → M.A) (j : Fin brb.F.n)
    (h : Fin M.H) :
    ∑ s : M.S, M.bellmanError brb.F j pi h s ≤ 1 := by
  exact le_of_abs_le (M.bellman_error_le_of_rank brb pi j h)

/-- Worst-case per-episode Bellman error bounded by the horizon. -/
theorem episode_bellman_error_le_H (brb : M.BellmanRankBound)
    (pi : Fin M.H → M.S → M.A) (j : Fin brb.F.n) :
    ∑ h : Fin M.H,
      ∑ s : M.S, M.bellmanError brb.F j pi h s ≤ (M.H : ℝ) := by
  calc
    ∑ h : Fin M.H, ∑ s : M.S, M.bellmanError brb.F j pi h s
      ≤ ∑ h : Fin M.H, |∑ s : M.S, M.bellmanError brb.F j pi h s| := by
        gcongr with h _
        exact le_abs_self _
    _ ≤ ∑ h : Fin M.H, (1 : ℝ) := by
        gcongr with h _
        exact M.bellman_error_le_of_rank brb pi j h
    _ = (M.H : ℝ) := by
        simp [Finset.sum_const]

end FiniteHorizonMDP

end
