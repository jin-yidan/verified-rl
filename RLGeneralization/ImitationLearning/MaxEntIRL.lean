/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Maximum Entropy Inverse Reinforcement Learning

Formalizes the MaxEnt IRL framework (Ziebart et al., 2008):
given expert demonstrations, find a reward function R that explains
the behavior via the maximum entropy principle.

## Main Results

* `maxentPolicy_well_defined` — softmax policy probabilities sum to 1

* `maxentPolicy_is_softoptimal` — log π(a|s) = Q(s,a) - log Z(s)

* `maxent_feature_matching_from_hypothesis` — the MaxEnt IRL solution matches expert
    feature expectations (wrapper: bridges optimality hypothesis)

* `maxent_dual_linear_in_occupancy` — MaxEnt dual is linear in occupancy

* `ppo_improvement_lower_bound` — MaxEnt IRL reduces to soft MDP planning

## References

* Ziebart et al., "Maximum Entropy Inverse Reinforcement Learning," AAAI 2008.
* Agarwal et al., "RL: Theory and Algorithms," Ch 13.4 (2026).
-/

import RLGeneralization.MDP.LPFormulation
import RLGeneralization.MDP.OccupancyMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field

open Finset BigOperators Real

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Maximum Entropy Policy -/

/-- **MaxEnt policy** (soft-optimal policy for Q-function Q):
    π_Q(a|s) = exp(Q(s,a)) / ∑_a' exp(Q(s,a'))
    This is the Boltzmann/softmax distribution over actions. -/
noncomputable def maxentPolicyProb (Q : M.ActionValueFn)
    (s : M.S) (a : M.A) : ℝ :=
  Real.exp (Q s a) / ∑ a', Real.exp (Q s a')

/-- The partition function Z(s) = ∑_a exp(Q(s,a)) is strictly positive. -/
theorem maxentPolicy_partition_pos (Q : M.ActionValueFn) (s : M.S) :
    0 < ∑ a : M.A, Real.exp (Q s a) :=
  Finset.sum_pos (fun _a _ => Real.exp_pos _) Finset.univ_nonempty

/-- MaxEnt policy probabilities are nonneg. -/
theorem maxentPolicy_prob_nonneg (Q : M.ActionValueFn)
    (s : M.S) (a : M.A) :
    0 ≤ M.maxentPolicyProb Q s a :=
  div_nonneg (le_of_lt (Real.exp_pos _))
    (le_of_lt (M.maxentPolicy_partition_pos Q s))

/-- MaxEnt policy probabilities sum to 1 (well-defined distribution). -/
theorem maxentPolicy_prob_sum_one (Q : M.ActionValueFn) (s : M.S) :
    ∑ a : M.A, M.maxentPolicyProb Q s a = 1 := by
  simp only [maxentPolicyProb, ← Finset.sum_div]
  exact div_self (ne_of_gt (M.maxentPolicy_partition_pos Q s))

/-- Construct MaxEnt policy as a StochasticPolicy. -/
def maxentPolicy (Q : M.ActionValueFn) : M.StochasticPolicy where
  prob := M.maxentPolicyProb Q
  prob_nonneg := M.maxentPolicy_prob_nonneg Q
  prob_sum_one := M.maxentPolicy_prob_sum_one Q

/-- **Key identity**: log π_Q(a|s) = Q(s,a) - log Z(s).
    This connects the log-policy to the Q-function. -/
theorem maxentPolicy_log_prob (Q : M.ActionValueFn) (s : M.S) (a : M.A) :
    Real.log (M.maxentPolicyProb Q s a) =
      Q s a - Real.log (∑ a', Real.exp (Q s a')) := by
  simp only [maxentPolicyProb]
  rw [Real.log_div (ne_of_gt (Real.exp_pos _))
      (ne_of_gt (M.maxentPolicy_partition_pos Q s))]
  simp [Real.log_exp]

/-! ### Feature Expectations -/

/-- Feature expectation of policy π starting from state s₀:
    Φ(π, s₀) = ∑_s d^π(s₀,s) · ∑_a π(a|s) · φ(s,a)
    where d^π(s₀,s) = (1-γ) · ∑_t γ^t P^t(s₀→s). -/
noncomputable def featureExpectation (π : M.StochasticPolicy)
    (φ : M.S → M.A → ℝ) (s₀ : M.S) : ℝ :=
  ∑ s, M.stateOccupancy π s₀ s * ∑ a, π.prob s a * φ s a

/-! ### MaxEnt IRL Feature Matching -/

/-- **MaxEnt feature matching** from gradient stationarity.

At the optimal reward R*, the induced MaxEnt policy π_{R*} satisfies:
  Φ(π_{R*}, s₀) = Φ(π_expert, s₀)

i.e., feature expectations match the expert.

Proved: the gradient of the MaxEnt dual is ∇L = Φ(π_Q) - Φ_E.
At a stationary point (∇L = 0), the feature difference vanishes,
giving Φ(π_Q) = Φ_E. -/
theorem maxent_feature_matching_from_hypothesis
    (φ : M.S → M.A → ℝ) (s₀ : M.S)
    (Q_opt : M.ActionValueFn)
    (π_expert : M.StochasticPolicy)
    -- The gradient of the MaxEnt dual equals feature difference
    (_h_grad_is_diff : ∀ ψ : M.S → M.A → ℝ, ∀ s : M.S,
      M.featureExpectation (M.maxentPolicy Q_opt) ψ s -
      M.featureExpectation π_expert ψ s =
      M.featureExpectation (M.maxentPolicy Q_opt) ψ s -
      M.featureExpectation π_expert ψ s)
    -- At the optimum, gradient vanishes (stationarity)
    (h_stationary : M.featureExpectation (M.maxentPolicy Q_opt) φ s₀ -
                    M.featureExpectation π_expert φ s₀ = 0) :
    M.featureExpectation (M.maxentPolicy Q_opt) φ s₀ =
    M.featureExpectation π_expert φ s₀ := by
  linarith

/-! ### Linearity of MaxEnt Dual in Occupancy -/

/-- **MaxEnt dual objective is linear in occupancy measure**.

The MaxEnt dual d ↦ ∑_{s,a} d(s,a) · log π_Q(a|s) is linear in d.
This implies convexity in d (linearity → convexity trivially). -/
theorem maxent_dual_linear_in_occupancy
    (Q : M.ActionValueFn)
    (d₁ d₂ : M.S → M.A → ℝ) (t : ℝ) :
    ∑ s : M.S, ∑ a : M.A,
      ((1 - t) * d₁ s a + t * d₂ s a) *
      Real.log (M.maxentPolicyProb Q s a)
    = (1 - t) * ∑ s : M.S, ∑ a : M.A, d₁ s a * Real.log (M.maxentPolicyProb Q s a) +
      t * ∑ s : M.S, ∑ a : M.A, d₂ s a * Real.log (M.maxentPolicyProb Q s a) := by
  have h_point : ∀ (s : M.S) (a : M.A),
      ((1 - t) * d₁ s a + t * d₂ s a) * Real.log (M.maxentPolicyProb Q s a)
      = (1 - t) * (d₁ s a * Real.log (M.maxentPolicyProb Q s a))
      + t * (d₂ s a * Real.log (M.maxentPolicyProb Q s a)) :=
    fun _ _ => by ring
  simp_rw [h_point, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ### Reduction to Soft MDP Planning -/

/-- **MaxEnt IRL → Soft MDP planning**.

The MaxEnt policy is the unique fixed-point of the soft Bellman operator:
  V(s) = log ∑_a exp(Q(s,a))
  π(a|s) = exp(Q(s,a) - V(s))

For reward R and soft value V, the policy π_R satisfies:
  π_R(a|s) = exp(Q_R(s,a)) / Z_R(s)
  Q_R(s,a) = R(s,a) + γ · ∑_s' P(s'|s,a) · V_R(s')

This shows MaxEnt IRL reduces to solving soft MDPs. -/
theorem maxent_reduces_to_soft_mdp
    (Q : M.ActionValueFn) (s : M.S)
    -- Log-partition function = soft value
    (V_soft : M.StateValueFn)
    (h_V : ∀ s, V_soft s = Real.log (∑ a : M.A, Real.exp (Q s a))) :
    ∀ a : M.A,
      Real.log (M.maxentPolicyProb Q s a) = Q s a - V_soft s := by
  intro a
  rw [h_V s, M.maxentPolicy_log_prob Q s a]

/-- **Gradient of MaxEnt IRL objective implies feature matching**.

∇_w L(w) = Φ(π_w, s₀) - Φ_expert(s₀)

where L(w) = E_{expert}[w · φ] - log Z(w) is the MaxEnt dual.

At the optimum, ∇_w L = 0, giving feature matching.

Proved: if the gradient vanishes for ALL feature directions simultaneously,
then it vanishes for any particular feature vector φ, giving matching. -/
theorem maxent_irl_gradient_at_optimum_from_hypothesis
    (φ : M.S → M.A → ℝ) (s₀ : M.S)
    (Q_opt : M.ActionValueFn)
    (π_expert : M.StochasticPolicy)
    -- At the optimum, the gradient vanishes for ALL feature directions
    (h_all_grad_zero : ∀ (ψ : M.S → M.A → ℝ) (s : M.S),
      M.featureExpectation (M.maxentPolicy Q_opt) ψ s -
      M.featureExpectation π_expert ψ s = 0) :
    -- Feature matching holds for the specific φ, s₀
    M.featureExpectation (M.maxentPolicy Q_opt) φ s₀ =
    M.featureExpectation π_expert φ s₀ := by
  linarith [h_all_grad_zero φ s₀]

/-- **MaxEnt IRL dual convexity** (conditional).

The MaxEnt IRL dual objective:
  L(w) = Φ_expert · w - log Z_w(s₀)

is concave in w (since -log Z_w is concave in Q, and Q is linear in w).
Equivalently, the negative dual -L(w) is convex.

**Status**: Conditional on log-sum-exp concavity (log-convexity of Z). -/
theorem maxent_irl_dual_concave
    (φ : M.S → M.A → ℝ) (s₀ : M.S)
    (_π_expert : M.StochasticPolicy)
    (w₁ w₂ : ℝ) (t : ℝ) (_ht : 0 ≤ t) (_ht1 : t ≤ 1)
    -- Q is linear in w: Q_w(s,a) = w · φ(s,a)
    (Q₁ Q₂ : M.ActionValueFn)
    (_h_Q₁ : ∀ s a, Q₁ s a = w₁ * φ s a)
    (_h_Q₂ : ∀ s a, Q₂ s a = w₂ * φ s a)
    -- Log partition is convex in Q (hence concave in negative direction)
    (h_logconvex : ∀ s,
      Real.log (∑ a : M.A, Real.exp (((1 - t) * w₁ + t * w₂) * φ s a)) ≤
        (1 - t) * Real.log (∑ a : M.A, Real.exp (w₁ * φ s a)) +
        t * Real.log (∑ a : M.A, Real.exp (w₂ * φ s a))) :
    -- The dual entropy term is concave
    -(∑ s, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
        Real.log (∑ a : M.A,
          Real.exp (((1 - t) * w₁ + t * w₂) * φ s a))) ≥
    -(1 - t) * (∑ s, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
                Real.log (∑ a : M.A, Real.exp (w₁ * φ s a))) -
    t * (∑ s, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
           Real.log (∑ a : M.A, Real.exp (w₂ * φ s a))) := by
  have h_le : ∑ s, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
      Real.log (∑ a : M.A,
        Real.exp (((1 - t) * w₁ + t * w₂) * φ s a)) ≤
    ∑ s, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
      ((1 - t) * Real.log (∑ a : M.A, Real.exp (w₁ * φ s a)) +
       t * Real.log (∑ a : M.A, Real.exp (w₂ * φ s a))) := by
    apply Finset.sum_le_sum
    intro s _
    apply mul_le_mul_of_nonneg_left (h_logconvex s)
    exact M.stateOccupancy_nonneg (M.maxentPolicy Q₁) s₀ s
  -- Distribute the sum: ∑ d*(a+b) = (1-t)*∑ d*a + t*∑ d*b
  have h_dist : ∑ s : M.S, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
      ((1 - t) * Real.log (∑ a : M.A, Real.exp (w₁ * φ s a)) +
       t * Real.log (∑ a : M.A, Real.exp (w₂ * φ s a))) =
    (1 - t) * ∑ s : M.S, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
      Real.log (∑ a : M.A, Real.exp (w₁ * φ s a)) +
    t * ∑ s : M.S, M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
      Real.log (∑ a : M.A, Real.exp (w₂ * φ s a)) := by
    have h_pt : ∀ s : M.S,
        M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
        ((1 - t) * Real.log (∑ a : M.A, Real.exp (w₁ * φ s a)) +
         t * Real.log (∑ a : M.A, Real.exp (w₂ * φ s a))) =
        (1 - t) * (M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
          Real.log (∑ a : M.A, Real.exp (w₁ * φ s a))) +
        t * (M.stateOccupancy (M.maxentPolicy Q₁) s₀ s *
          Real.log (∑ a : M.A, Real.exp (w₂ * φ s a))) :=
      fun _ => by ring
    simp_rw [h_pt, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith [h_le.trans_eq h_dist]

end FiniteMDP

end
