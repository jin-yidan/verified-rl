/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Policy Gradient Methods (Definitions and Algebraic Identities)

Definitions and algebraic scaffolding for policy-gradient methods.
The full policy-gradient theorem (differentiation under the integral
sign) is NOT formalized; this module is classified as `weaker` in
`verification_manifest.json`.

## Main Definitions

* `ParameterizedPolicy` - θ-parameterized policy with prob and score
* `softmaxParameterizedPolicy` - Softmax (log-linear) policy
* `policyObjective` - J(θ) = V^{π_θ}(s₀) for a fixed start state s₀
* `scoreFunction` - ψ(a,i) score for the policy gradient
* `policyGradientIdentity` - Algebraic template (definition, not theorem):
  ∇J component = (1/(1-γ)) Σ_s d(s) Σ_a π(a|s) ψ(a,i) Q(s,a)

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.MDP.Basic
import RLGeneralization.MDP.OccupancyMeasure
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Field

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Parameterized Policies -/

/-- A parameterized policy π_θ : S → Δ(A) where θ ∈ ℝ^d.
    The probability π_θ(a|s) depends smoothly on θ. -/
structure ParameterizedPolicy (d : ℕ) where
  /-- Policy probability as a function of parameters -/
  prob : (Fin d → ℝ) → M.S → M.A → ℝ
  /-- Probabilities are nonneg -/
  prob_nonneg : ∀ θ s a, 0 ≤ prob θ s a
  /-- Probabilities sum to 1 -/
  prob_sum_one : ∀ θ s, ∑ a, prob θ s a = 1

/-- Convert a parameterized policy at a specific θ to a
    StochasticPolicy. -/
def ParameterizedPolicy.toStochastic {d : ℕ}
    (pp : M.ParameterizedPolicy d) (θ : Fin d → ℝ) :
    M.StochasticPolicy :=
  ⟨pp.prob θ, pp.prob_nonneg θ, pp.prob_sum_one θ⟩

/-! ### Policy Objective -/

/-- The policy objective `J(θ) = V^{π_θ}(s₀)` for a fixed
    starting state `s₀`. This is the quantity optimized by
    policy-gradient methods. -/
def policyObjective {d : ℕ}
    (_pp : M.ParameterizedPolicy d)
    (V_of : (Fin d → ℝ) → M.StateValueFn)
    (s₀ : M.S) (θ : Fin d → ℝ) : ℝ :=
  V_of θ s₀

/-! ### Score Function (Log-Policy Gradient) -/

/-- The score function `∇_θ log π_θ(a|s)`, represented as a
    `Fin d → ℝ` vector. -/
def scoreFunction {d : ℕ}
    (grad_log_pi : (Fin d → ℝ) → M.S → M.A → Fin d → ℝ)
    (θ : Fin d → ℝ) (s : M.S) (a : M.A) : Fin d → ℝ :=
  grad_log_pi θ s a

/-! ### Policy Gradient Theorem (Statement) -/

/-- **Policy-gradient identity template**.

  ∇J(θ) = (1/(1-γ)) E_{s~d^π_θ, a~π_θ}[∇log π_θ(a|s) · Q^{π_θ}(s,a)]

  This is the foundational result for policy gradient methods.
  It says: the gradient of the objective equals the expected
  score function weighted by the Q-value, averaged over the
  occupancy measure.

  It is encoded as a definition rather than a theorem because the full
  proof requires an exact occupancy measure and differentiation under
  the integral sign, neither of which is formalized here. -/
def policyGradientIdentity {d : ℕ}
    (_pp : M.ParameterizedPolicy d)
    (grad_log_pi : (Fin d → ℝ) → M.S → M.A → Fin d → ℝ)
    (Q_of : (Fin d → ℝ) → M.ActionValueFn)
    (occupancy : (Fin d → ℝ) → M.S → M.A → ℝ)
    (θ : Fin d → ℝ) : Fin d → ℝ :=
  -- ∇J(θ) = (1/(1-γ)) ∑_{s,a} d^π(s,a) · ∇log π(a|s) · Q^π(s,a)
  fun i => (1 / (1 - M.γ)) *
    ∑ s, ∑ a, occupancy θ s a *
      grad_log_pi θ s a i * Q_of θ s a

/-! ### Softmax Policy -/

/-- Softmax (log-linear) policy: `π_θ(a|s) ∝ exp(θᵀφ(s,a))`. -/
def softmaxProb {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ)
    (θ : Fin d → ℝ) (s : M.S) (a : M.A) : ℝ :=
  Real.exp (∑ i, θ i * φ s a i) /
    ∑ a', Real.exp (∑ i, θ i * φ s a' i)

/-- Softmax probabilities are nonneg. -/
theorem softmaxProb_nonneg {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ)
    (θ : Fin d → ℝ) (s : M.S) (a : M.A) :
    0 ≤ M.softmaxProb φ θ s a := by
  unfold softmaxProb
  apply div_nonneg (le_of_lt (Real.exp_pos _))
  apply Finset.sum_nonneg
  intro a' _
  exact le_of_lt (Real.exp_pos _)

/-- Softmax probabilities sum to 1. -/
theorem softmaxProb_sum_one {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ)
    (θ : Fin d → ℝ) (s : M.S)
    (h_pos : 0 < ∑ a', Real.exp (∑ i, θ i * φ s a' i)) :
    ∑ a, M.softmaxProb φ θ s a = 1 := by
  unfold softmaxProb
  show ∑ a, Real.exp (∑ i, θ i * φ s a i) /
    (∑ a', Real.exp (∑ i, θ i * φ s a' i)) = 1
  rw [← Finset.sum_div, div_self (ne_of_gt h_pos)]

/-! ### Softmax Strict Positivity -/

/-- The sum of exponentials is strictly positive (helper). -/
theorem softmax_denom_pos {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ)
    (θ : Fin d → ℝ) (s : M.S) :
    0 < ∑ a', Real.exp (∑ i, θ i * φ s a' i) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- Softmax probabilities are **strictly positive**.
    This is the key property that makes the log-derivative trick
    well-defined: since `π_θ(a|s) > 0` for all actions, the score
    function `∇log π_θ(a|s) = ∇π/π` is finite everywhere. -/
theorem softmaxProb_pos {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ)
    (θ : Fin d → ℝ) (s : M.S) (a : M.A) :
    0 < M.softmaxProb φ θ s a := by
  unfold softmaxProb
  exact div_pos (Real.exp_pos _) (M.softmax_denom_pos φ θ s)

/-! ### Constructing a Softmax ParameterizedPolicy -/

/-- The softmax policy is a valid `ParameterizedPolicy`: it maps
    parameters θ to a well-formed stochastic policy. -/
def softmaxParameterizedPolicy {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) :
    M.ParameterizedPolicy d where
  prob := M.softmaxProb φ
  prob_nonneg := fun θ s a => M.softmaxProb_nonneg φ θ s a
  prob_sum_one := fun θ s =>
    M.softmaxProb_sum_one φ θ s (M.softmax_denom_pos φ θ s)

/-! ### Expected Advantage is Zero Under Current Policy

  This is a fundamental identity in policy gradient theory:
  under the current policy π, the expected advantage is zero:

    ∑_a π(a|s) · A^π(s,a) = ∑_a π(a|s) · (Q^π(s,a) - V^π(s)) = 0

  This follows from V^π(s) = ∑_a π(a|s) · Q^π(s,a) (the
  definition of the value function in terms of Q).

  Consequence: the policy gradient
  can equivalently use advantages instead of Q-values:

    ∇J(θ) = E_{d^π}[∇log π · Q^π]
           = E_{d^π}[∇log π · A^π]

  since ∑_a π(a|s)·∇log π(a|s)·V(s) = V(s)·∑_a ∇π(a|s) = 0.
-/

/-- **Expected advantage is zero under the current policy**.

  If V^π(s) = ∑_a π(a|s) · Q^π(s,a) (i.e., V is consistent with
  Q under policy π), then ∑_a π(a|s) · (Q(s,a) - V(s)) = 0.

  This is the algebraic core of the baseline invariance property. -/
theorem expected_advantage_zero
    (π : M.StochasticPolicy)
    (Q : M.ActionValueFn) (V : M.StateValueFn)
    (hVQ : ∀ s, V s = ∑ a, π.prob s a * Q s a)
    (s : M.S) :
    ∑ a, π.prob s a * (Q s a - V s) = 0 := by
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, π.prob_sum_one, one_mul]
  linarith [hVQ s]

/-- **Softmax advantage identity**.

  For softmax policy: ∑_a softmax(θ)_a · (Q(s,a) - V_softmax(s)) = 0
  where V_softmax(s) = ∑_a softmax(θ)_a · Q(s,a).

  This is the expected advantage = 0 identity specialized to
  softmax policies. It is the algebraic identity behind the
  REINFORCE variance reduction via baselines. -/
theorem softmax_expected_advantage_zero {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ)
    (θ : Fin d → ℝ)
    (Q : M.ActionValueFn) (s : M.S) :
    ∑ a, M.softmaxProb φ θ s a *
      (Q s a - ∑ a', M.softmaxProb φ θ s a' * Q s a') = 0 := by
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    M.softmaxProb_sum_one φ θ s (M.softmax_denom_pos φ θ s),
    one_mul, sub_self]

/-! ### Baseline Invariance (Variance Reduction)

  A key practical insight: adding any state-dependent
  baseline b(s) to the Q-values does not change the expected
  policy gradient, because:

    ∑_a π(a|s) · ψ(a) · b(s) = b(s) · ∑_a π(a|s) · ψ(a)

  If ψ is the score function ∇log π, then ∑_a π · ∇log π = ∑_a ∇π = 0
  (the gradient of a constant). We prove the algebraic version below.
-/

/-- **Baseline invariance**.

  For any policy π and any function b : S → ℝ:

    ∑_a π(a|s) · (Q(s,a) - b(s)) = ∑_a π(a|s) · Q(s,a) - b(s)

  In particular, if we also multiply by a score ψ(a) and if
  ∑_a π(a|s) · ψ(a) = 0 (the score-function identity), then
  the baseline cancels out entirely. This theorem establishes
  the first (algebraic) part. -/
theorem baseline_subtraction
    (π : M.StochasticPolicy)
    (Q : M.ActionValueFn) (b : M.S → ℝ) (s : M.S) :
    ∑ a, π.prob s a * (Q s a - b s) =
    (∑ a, π.prob s a * Q s a) - b s := by
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    π.prob_sum_one, one_mul]

/-- **Score function identity**: if ∑_a π(a|s) = 1 for all s,
    then for any scalar c and function ψ : A → ℝ^d satisfying
    ∑_a π(a|s) · ψ(a) = 0 (the score identity), adding a
    baseline c to Q does not change ∑_a π · ψ · Q.

    ∑_a π(a|s) · ψ(a,i) · (Q(s,a) - c) = ∑_a π(a|s) · ψ(a,i) · Q(s,a)

    when ∑_a π(a|s) · ψ(a,i) = 0.

    This is the full baseline invariance identity for the
    score-weighted policy-gradient term. -/
theorem score_baseline_invariance {d : ℕ}
    (π : M.StochasticPolicy)
    (ψ : M.A → Fin d → ℝ) (Q : M.ActionValueFn)
    (c : ℝ) (s : M.S) (i : Fin d)
    (h_score : ∑ a, π.prob s a * ψ a i = 0) :
    ∑ a, π.prob s a * ψ a i * (Q s a - c) =
    ∑ a, π.prob s a * ψ a i * Q s a := by
  have : ∑ a, π.prob s a * ψ a i * (Q s a - c) =
      (∑ a, π.prob s a * ψ a i * Q s a) -
      c * (∑ a, π.prob s a * ψ a i) := by
    have h1 : ∀ a, π.prob s a * ψ a i * (Q s a - c) =
        π.prob s a * ψ a i * Q s a -
        π.prob s a * ψ a i * c := fun a => by ring
    simp_rw [h1, Finset.sum_sub_distrib]
    congr 1; rw [← Finset.sum_mul]; ring
  rw [this, h_score, mul_zero, sub_zero]

/-! ### Policy Gradient with Advantage

  The policy gradient theorem states:
    ∇J(θ) = (1/(1-γ)) ∑_s d^π(s) ∑_a π(a|s) ∇log π(a|s) Q^π(s,a)

  Combined with baseline invariance (score_baseline_invariance),
  we can replace Q^π(s,a) with the advantage A^π(s,a) = Q^π(s,a) - V^π(s):
    ∇J(θ) = (1/(1-γ)) ∑_s d^π(s) ∑_a π(a|s) ∇log π(a|s) A^π(s,a)

  We prove this algebraic equivalence directly.
-/

/-- **Policy gradient with advantage**.

  The Q-form and advantage-form of the policy gradient are equal,
  provided the score function satisfies the identity
  ∑_a π(a|s) · ∇log π(a|s) = 0.

  Concretely: for each coordinate i of the gradient,
    ∑_{s,a} d(s,a) · ψ(s,a,i) · Q(s,a)
    = ∑_{s,a} d(s,a) · ψ(s,a,i) · A(s,a)

  where A(s,a) = Q(s,a) - V(s) and d is the occupancy measure. -/
theorem policy_gradient_advantage_form {d : ℕ}
    (π : M.StochasticPolicy)
    (ψ : M.S → M.A → Fin d → ℝ)
    (Q : M.ActionValueFn) (V : M.StateValueFn)
    (d_occ : M.S → ℝ)
    (i : Fin d)
    (h_score : ∀ s, ∑ a, π.prob s a * ψ s a i = 0) :
    ∑ s, d_occ s * ∑ a, π.prob s a * ψ s a i * Q s a =
    ∑ s, d_occ s * ∑ a, π.prob s a * ψ s a i *
      (Q s a - V s) := by
  congr 1; funext s
  congr 1
  exact (M.score_baseline_invariance π (ψ s) Q (V s) s i
    (h_score s)).symm

/-! ### One-Step Policy Gradient Identity

  The one-step (inner) policy gradient identity is the core of
  the policy gradient theorem. For a fixed state s:

    ∑_a ∇_θ π_θ(a|s) · Q(s,a) = ∑_a π_θ(a|s) · ∇_θ log π_θ(a|s) · Q(s,a)

  This is the "log-derivative trick": ∇π = π · ∇log π.

  We formalize this as: given that grad_pi(a) = pi(a) * score(a)
  for all a (the log-derivative relation), the above identity holds.
-/

/-- **Log-derivative trick**.

  If ∇π(a|s) = π(a|s) · ∇log π(a|s) for all a (which holds whenever
  π(a|s) > 0), then:

    ∑_a ∇_θ π_θ(a|s)_i · Q(s,a) = ∑_a π_θ(a|s) · ∇log π_θ(a|s)_i · Q(s,a)

  This is immediate from substitution, but it is the algebraic
  identity at the heart of REINFORCE and all policy gradient methods. -/
theorem log_derivative_trick {d : ℕ}
    (π : M.StochasticPolicy)
    (grad_pi : M.A → Fin d → ℝ)
    (score : M.A → Fin d → ℝ)
    (Q : M.ActionValueFn) (s : M.S) (i : Fin d)
    (h_log_deriv : ∀ a, grad_pi a i = π.prob s a * score a i) :
    ∑ a, grad_pi a i * Q s a =
    ∑ a, π.prob s a * score a i * Q s a := by
  congr 1; funext a; rw [h_log_deriv a, mul_assoc]

/-! ### Value Function Decomposition

  V^π(s) = ∑_a π(a|s) · Q^π(s,a) is the fundamental relation
  between value and action-value functions. We prove it from the
  Bellman equation when Q satisfies its defining equation. -/

/-- **V-Q consistency**: `V^π(s) = ∑_a π(a|s) · Q^π(s,a)`
    when both `V` and `Q` satisfy their respective Bellman equations. -/
theorem value_eq_expected_action_value
    (π : M.StochasticPolicy)
    (V : M.StateValueFn) (Q : M.ActionValueFn)
    (hV : M.isValueOf V π)
    (hQ : ∀ s a, Q s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V s')
    (s : M.S) :
    V s = ∑ a, π.prob s a * Q s a := by
  rw [hV s]
  unfold expectedReward expectedNextValue
  simp_rw [hQ, mul_add, Finset.sum_add_distrib]
  congr 1
  -- ∑_a π(a)(γ ∑_{s'} P V) = γ ∑_a π(a) ∑_{s'} P V
  have : ∀ a, π.prob s a * (M.γ * ∑ s', M.P s a s' * V s') =
      M.γ * (π.prob s a * ∑ s', M.P s a s' * V s') :=
    fun a => by ring
  simp_rw [this]
  rw [← Finset.mul_sum]

/-- **Corollary**: Expected advantage is zero when V and Q are
    consistently defined via Bellman equations.

    ∑_a π(a|s) · (Q^π(s,a) - V^π(s)) = 0

    This combines `value_eq_expected_action_value` with
    `expected_advantage_zero`. -/
theorem bellman_advantage_zero
    (π : M.StochasticPolicy)
    (V : M.StateValueFn) (Q : M.ActionValueFn)
    (hV : M.isValueOf V π)
    (hQ : ∀ s a, Q s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V s')
    (s : M.S) :
    ∑ a, π.prob s a * (Q s a - V s) = 0 :=
  M.expected_advantage_zero π Q V
    (fun s => M.value_eq_expected_action_value π V Q hV hQ s) s

/-! ### Policy Gradient Theorem (Algebraic Form)

The full PG theorem ∇J(θ) = (1/(1-γ)) E_{d^π}[∇log π · Q^π] requires
differentiating V^{π_θ} w.r.t. θ, which needs calculus infrastructure.

However, the **algebraic core** — the PDL in occupancy-advantage form —
is already proved. The following theorem combines `pdl_normalized` with
the algebraic identities in this file to state the policy gradient
identity in its standard occupancy-score form.

Specifically: comparing two policies π and π' via the PDL gives
  V^π(s₀) - V^{π'}(s₀) = (1-γ)⁻¹ · ∑_s d^π(s₀,s) · ∑_a π(a|s) · A^{π'}(s,a)
and using the log-derivative trick (∇π = π · ∇log π), the one-step
policy gradient for a fixed state s equals:
  ∑_a ∇π(a|s) · Q(s,a) = ∑_a π(a|s) · ψ(a) · Q(s,a)

These compose to give the algebraic form of the PG theorem. -/

/-- **Performance difference in advantage form (occupancy-weighted).**

  V^π(s₀) - V^{π'}(s₀) = (1-γ)⁻¹ · ∑_s d^π(s₀,s) · ∑_a π(a|s) · A^{π'}(s,a)

  This is `pdl_normalized` restated with the advantage
  `A^{π'}(s,a) = Q^{π'}(s,a) - V^{π'}(s)` made explicit.

  This is the algebraic core of the policy gradient theorem: it shows that the
  value difference between policies equals an occupancy-weighted
  sum of advantages, which is the quantity estimated by
  REINFORCE and actor-critic algorithms. -/
theorem pdl_advantage_occupancy_form
    (π π' : M.StochasticPolicy)
    (V_pi V_pi' : M.StateValueFn)
    (Q_pi' : M.ActionValueFn)
    (hV_pi : M.isValueOf V_pi π)
    (hV_pi' : M.isValueOf V_pi' π')
    (hQ_pi' : ∀ s a, Q_pi' s a =
      M.r s a + M.γ * ∑ s', M.P s a s' * V_pi' s')
    (s₀ : M.S) :
    V_pi s₀ - V_pi' s₀ =
      (1 - M.γ)⁻¹ * ∑ s, M.stateOccupancy π s₀ s *
        ∑ a, π.prob s a * (Q_pi' s a - V_pi' s) := by
  -- This is pdl_normalized with expectedAdvantage expanded
  have h := M.pdl_normalized π π' V_pi V_pi' Q_pi' hV_pi hV_pi' hQ_pi' s₀
  simp only [expectedAdvantage, advantage] at h
  exact h

/-- **Score-weighted policy gradient core.**

  For a fixed state s, the score-weighted sum equals the gradient-weighted sum:
    ∑_a ∇π(a|s)_i · Q(s,a) = ∑_a π(a|s) · ψ(s,a,i) · Q(s,a)
  where ψ = ∇log π is the score function.

  Combined with `pdl_advantage_occupancy_form`, this gives the full
  algebraic structure of the policy gradient theorem. -/
theorem policy_gradient_one_step_score {d : ℕ}
    (π : M.StochasticPolicy)
    (grad_pi : M.S → M.A → Fin d → ℝ)
    (score : M.S → M.A → Fin d → ℝ)
    (Q : M.ActionValueFn) (s : M.S) (i : Fin d)
    (h_log_deriv : ∀ a, grad_pi s a i = π.prob s a * score s a i) :
    ∑ a, grad_pi s a i * Q s a =
    ∑ a, π.prob s a * score s a i * Q s a :=
  M.log_derivative_trick π (grad_pi s) (score s) Q s i h_log_deriv

end FiniteMDP

end
