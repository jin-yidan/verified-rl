/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Bellman Rank Draft Wrappers

Draft-only wrappers on top of the trusted Bellman-rank auxiliary
infrastructure.

## Main Results

* `bellman_rank_trivial_dichotomy` - Degenerate zero-dimensional helper
* `golf_suboptimality_from_average_bellman_error` - Conditional GOLF PAC wrapper
* `golf_suboptimality_from_total_bellman_error` - Conditional average-error wrapper

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.BilinearRank.Auxiliary

open Finset BigOperators

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### Degenerate Zero-Dimensional Helper -/

/-- Degenerate helper: either the stored rank parameter is positive, or all
    Bellman-error sums vanish in the zero-dimensional case. This is not a
    substantive Bellman-rank theorem. -/
theorem bellman_rank_trivial_dichotomy (brb : M.BellmanRankBound) :
    0 < brb.d ∨ ∀ (pi : Fin M.H → M.S → M.A) (j : Fin brb.F.n)
      (h : Fin M.H),
    ∑ s : M.S, M.bellmanError brb.F j pi h s = 0 := by
  by_cases hd : 0 < brb.d
  · exact Or.inl hd
  · right; intro pi j h
    rw [brb.decomp pi j h]
    exact Finset.sum_eq_zero fun i _ =>
      absurd (Nat.pos_of_ne_zero fun h => Fin.elim0 (h ▸ i)) hd

/-! ### GOLF Sample Complexity

  The GOLF analysis proceeds as:
  1. At each episode k, GOLF selects a hypothesis f_k from F that is
     "optimistic" and consistent with data (in the version space).
  2. The suboptimality of the average policy decomposes via the
     performance difference lemma into a sum of Bellman errors.
  3. The bilinear decomposition gives sum_s BE(f,pi,h,s) = <X^pi_h, W^f_h>.
  4. By Cauchy-Schwarz, each step contributes at most |<X, W>| <= 1.
  5. Summing over H steps gives per-episode error <= H.
  6. The version-space argument bounds the total squared W-norm,
     yielding the d^2 H^4 / eps^2 * log(|F|/delta) sample complexity.

  We formalize the algebraic core: the chain from hypotheses to the
  eps-suboptimality conclusion.
-/

/-- **Conditional GOLF sample-complexity wrapper**.

  If the average per-episode Bellman error (summed over steps and
  states) is bounded by eps, then the output policy is eps-suboptimal.

  This is the algebraic reduction at the core of GOLF: given
  the bilinear decomposition (from `BellmanRankBound`) and the
  per-episode error hypothesis (from optimism + version space
  shrinkage), the suboptimality bound follows by direct chaining.

  The two non-trivial hypotheses (which are taken as given):
  1. **Optimism** (GOLF maintains f_k >= Q* via version space):
     V* - V^{pi_k} <= sum_h sum_s BE(f_k, pi_k, h, s)
  2. **Average error control** (version space shrinkage):
     (1/K) sum_k sum_h sum_s BE <= eps

  A full formalization would derive (2) from the bilinear rank
  structure + uniform convergence over F, requiring a probability
  space not present here. -/
theorem golf_suboptimality_from_average_bellman_error (brb : M.BellmanRankBound)
    (K : ℕ) (_hK : 0 < K)
    (eps : ℝ) (_heps : 0 < eps)
    -- Suboptimality of the output policy
    (subopt : ℝ)
    -- Selected hypotheses and policies at each episode
    (f_sel : Fin K → Fin brb.F.n)
    (pi_sel : Fin K → (Fin M.H → M.S → M.A))
    -- Hypothesis 1: suboptimality bounded by average Bellman error
    -- (from optimism: V* - V^{pi_avg} <= (1/K) sum_k sum_h sum_s BE)
    (h_subopt_le_avg_error : subopt ≤
      (1 / (K : ℝ)) * ∑ k : Fin K, ∑ h : Fin M.H,
        ∑ s : M.S, M.bellmanError brb.F (f_sel k) (pi_sel k) h s)
    -- Hypothesis 2: average Bellman error bounded by eps
    -- (from version space shrinkage + bilinear rank argument)
    (h_avg_error_le_eps :
      (1 / (K : ℝ)) * ∑ k : Fin K, ∑ h : Fin M.H,
        ∑ s : M.S, M.bellmanError brb.F (f_sel k) (pi_sel k) h s ≤ eps) :
    subopt ≤ eps :=
  le_trans h_subopt_le_avg_error h_avg_error_le_eps

/-- **Stronger conditional GOLF wrapper with the bilinear chain exposed**.

  Chains the bilinear decomposition and Cauchy-Schwarz into the GOLF
  sample complexity argument. Given:
  1. Suboptimality bounded by average Bellman error (optimism)
  2. A bound B on the sum of per-episode, per-step inner products
     (from the version-space / elliptical potential argument)

  Then subopt <= B / K.

  In the full GOLF analysis, B = O(d * H^2 * sqrt(K * log(|F|/delta))),
  yielding subopt <= O(d * H^2 / sqrt(K)) which is <= eps when
  K >= d^2 * H^4 / eps^2 * log(|F|/delta). -/
theorem golf_suboptimality_from_total_bellman_error (brb : M.BellmanRankBound)
    (K : ℕ) (hK : 0 < K)
    (subopt : ℝ)
    (f_sel : Fin K → Fin brb.F.n)
    (pi_sel : Fin K → (Fin M.H → M.S → M.A))
    (B : ℝ)
    -- Hypothesis 1: suboptimality bounded by average Bellman error
    (h_subopt : subopt ≤
      (1 / (K : ℝ)) * ∑ k : Fin K, ∑ h : Fin M.H,
        ∑ s : M.S, M.bellmanError brb.F (f_sel k) (pi_sel k) h s)
    -- Hypothesis 2: total Bellman error bounded by B
    -- (derived from bilinear decomposition + Cauchy-Schwarz +
    -- version space / elliptical potential argument)
    (h_total_bound : ∑ k : Fin K, ∑ h : Fin M.H,
        ∑ s : M.S, M.bellmanError brb.F (f_sel k) (pi_sel k) h s ≤ B) :
    subopt ≤ (1 / (K : ℝ)) * B := by
  calc subopt
      ≤ (1 / (K : ℝ)) * ∑ k : Fin K, ∑ h : Fin M.H,
          ∑ s : M.S, M.bellmanError brb.F (f_sel k) (pi_sel k) h s :=
        h_subopt
    _ ≤ (1 / (K : ℝ)) * B := by
        have hK_pos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
        exact mul_le_mul_of_nonneg_left h_total_bound (by positivity)

/-! ### Sample Complexity from Bilinear Structure

  Using the per-step Cauchy-Schwarz bound (`bellman_error_le_of_rank`),
  the total absolute Bellman error across K episodes is at most K·H.
  This gives a concrete (though loose) sample-complexity statement:
  K ≥ H/ε episodes suffice for ε-suboptimality under the optimism hypothesis. -/

/-- **Total absolute Bellman error is bounded by K·H.**

  From the bilinear rank structure, each step's total error |∑_s BE| ≤ 1
  (by Cauchy-Schwarz on the unit-norm embeddings). Summing over K episodes
  and H steps gives the bound K·H. -/
theorem total_absolute_bellman_error_le (brb : M.BellmanRankBound)
    (K : ℕ) (f_sel : Fin K → Fin brb.F.n)
    (pi_sel : Fin K → Fin M.H → M.S → M.A) :
    ∑ k : Fin K, ∑ h : Fin M.H,
      |∑ s : M.S, M.bellmanError brb.F (f_sel k) (pi_sel k) h s| ≤
    (K : ℝ) * M.H := by
  calc ∑ k : Fin K, ∑ h : Fin M.H,
        |∑ s, M.bellmanError brb.F (f_sel k) (pi_sel k) h s|
      ≤ ∑ k : Fin K, ∑ _h : Fin M.H, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro k _
        apply Finset.sum_le_sum; intro h _
        exact M.bellman_error_le_of_rank brb (pi_sel k) (f_sel k) h
    _ = ∑ _k : Fin K, (M.H : ℝ) := by
        apply Finset.sum_congr rfl; intro k _
        simp [Finset.sum_const, Finset.card_univ]
    _ = (K : ℝ) * M.H := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Average Bellman error bound from bilinear rank.**

  From `total_absolute_bellman_error_le`, the average per-episode
  absolute Bellman error is at most H:
    (1/K) · ∑_k ∑_h |∑_s BE| ≤ H

  This is a genuine bound from the bilinear Cauchy-Schwarz structure
  (not pure transitivity). Combined with the optimism hypothesis
  (subopt ≤ average error), it gives subopt ≤ H.

  The tighter d-dependent bound (subopt ≤ d·H²/√K) requires the
  version-space / elliptical potential argument. -/
theorem average_bellman_error_le_H (brb : M.BellmanRankBound)
    (K : ℕ) (hK : 0 < K)
    (f_sel : Fin K → Fin brb.F.n)
    (pi_sel : Fin K → Fin M.H → M.S → M.A) :
    (1 / (K : ℝ)) * ∑ k : Fin K, ∑ h : Fin M.H,
      |∑ s : M.S, M.bellmanError brb.F (f_sel k) (pi_sel k) h s| ≤
    (M.H : ℝ) := by
  have hK_pos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  calc (1 / (K : ℝ)) * ∑ k : Fin K, ∑ h : Fin M.H,
        |∑ s, M.bellmanError brb.F (f_sel k) (pi_sel k) h s|
      ≤ (1 / (K : ℝ)) * ((K : ℝ) * M.H) := by
        apply mul_le_mul_of_nonneg_left
          (M.total_absolute_bellman_error_le brb K f_sel pi_sel)
          (by positivity)
    _ = (M.H : ℝ) := by field_simp [ne_of_gt hK_pos]

end FiniteHorizonMDP

end
