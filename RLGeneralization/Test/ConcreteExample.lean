/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Concrete MDP Example

Instantiates the lean4-rl library on a concrete 3-state, 2-action MDP
to demonstrate that the theorems produce meaningful results on
specific numerical instances.

This file is excluded from the trusted benchmark root. It is kept as a
worked example rather than as audited theorem surface.

## The MDP

- States: {s₀, s₁, s₂}  (modeled as `Fin 3`)
- Actions: {left, right}  (modeled as `Fin 2`)
- Discount factor: γ = 1/2
- Rewards: r(s₀, left) = 1, r(s₁, right) = 2, others = 0
- Transitions: deterministic (each action sends to a fixed next state)

## Results Demonstrated

1. The MDP satisfies `FiniteMDP` axioms (transitions sum to 1, rewards bounded)
2. Bellman contraction holds with explicit γ = 1/2
3. Value iteration converges to Q*
4. The Banach fixed point exists

## References

* [Agarwal et al., *RL: Theory and Algorithms*][agarwal2026]
-/

import RLGeneralization.MDP.BellmanContraction
import RLGeneralization.MDP.BanachFixedPoint

open Finset BigOperators

noncomputable section

/-! ### A Concrete 3-State, 2-Action MDP -/

/-- A concrete MDP with 3 states and 2 actions.
    States: 0 (start), 1 (good), 2 (bad).
    Actions: 0 (left), 1 (right).
    Transitions are deterministic:
    - From state 0: left → state 1, right → state 2
    - From state 1: left → state 1 (stay), right → state 0
    - From state 2: left → state 0, right → state 2 (stay) -/
def exampleMDP : FiniteMDP where
  S := Fin 3
  A := Fin 2
  P := fun s a s' =>
    -- Deterministic transitions encoded as 0/1 probabilities
    if s = 0 then
      if a = 0 then (if s' = 1 then 1 else 0)  -- left: 0 → 1
      else (if s' = 2 then 1 else 0)            -- right: 0 → 2
    else if s = 1 then
      if a = 0 then (if s' = 1 then 1 else 0)  -- left: 1 → 1 (stay)
      else (if s' = 0 then 1 else 0)            -- right: 1 → 0
    else -- s = 2
      if a = 0 then (if s' = 0 then 1 else 0)  -- left: 2 → 0
      else (if s' = 2 then 1 else 0)            -- right: 2 → 2 (stay)
  r := fun s a =>
    if s = 0 ∧ a = 0 then 1       -- r(s₀, left) = 1
    else if s = 1 ∧ a = 1 then 2  -- r(s₁, right) = 2
    else 0                          -- all others = 0
  γ := 1 / 2
  P_nonneg := by intro s a s'; fin_cases s <;> fin_cases a <;> fin_cases s' <;> simp
  P_sum_one := by intro s a; fin_cases s <;> fin_cases a <;> simp
  r_bound := ⟨2, by norm_num, by intro s a; fin_cases s <;> fin_cases a <;> norm_num⟩
  γ_nonneg := by norm_num
  γ_lt_one := by norm_num

/-- The example MDP has discount factor 1/2. -/
@[simp] lemma exampleMDP_γ : exampleMDP.γ = 1 / 2 := rfl

/-- R_max is positive for this MDP. -/
lemma exampleMDP_R_max_pos : 0 < exampleMDP.R_max :=
  exampleMDP.R_max_pos

/-! ### Instantiate Bellman Contraction -/

/-- Bellman optimality operator contracts with factor 1/2 on this MDP. -/
theorem exampleMDP_bellman_contraction
    (Q₁ Q₂ : exampleMDP.ActionValueFn) :
    exampleMDP.supDistQ (exampleMDP.bellmanOptOp Q₁)
      (exampleMDP.bellmanOptOp Q₂) ≤
    (1 / 2) * exampleMDP.supDistQ Q₁ Q₂ :=
  exampleMDP.bellmanOptOp_contraction Q₁ Q₂

/-! ### Instantiate Banach Fixed Point -/

/-- There exists a Bellman-optimal Q-function for this MDP. -/
theorem exampleMDP_optimal_Q_exists :
    ∃ Q, exampleMDP.isBellmanOptimalQ Q :=
  exampleMDP.exists_bellmanOptimalQ_fixedPoint

/-- There exists an optimal policy for this MDP. -/
theorem exampleMDP_optimal_policy_exists :
    ∃ (π : exampleMDP.StochasticPolicy)
      (V : exampleMDP.StateValueFn),
    exampleMDP.isValueOf V π ∧
    ∀ (π' : exampleMDP.StochasticPolicy)
      (V' : exampleMDP.StateValueFn),
    exampleMDP.isValueOf V' π' → ∀ s, V' s ≤ V s := by
  obtain ⟨Q_star, hQ⟩ := exampleMDP.exists_bellmanOptimalQ_fixedPoint
  have h_opt := exampleMDP.optimal_policy_exists Q_star hQ
  exact ⟨exampleMDP.greedyStochasticPolicy Q_star,
    fun s => Finset.univ.sup' Finset.univ_nonempty (Q_star s),
    h_opt.1, h_opt.2⟩

end
