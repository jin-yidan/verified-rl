/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Imitation Learning

Formalizes basic imitation-learning infrastructure: expert and learner
policies, behavior-cloning style bounds, and DAgger-style wrappers.

## Main Definitions

* `ImitationSetting` - Finite-horizon MDP with expert and learner policies
* `behavior_cloning_bound_from_pdl` - Wrapper from a supplied PDL-style bound
* `DAggerSetting` - DAgger interactive imitation learning setup

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
* [Ross, Gordon, Bagnell, 2011, "A Reduction of Imitation Learning..."]
-/

import RLGeneralization.MDP.FiniteHorizon
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

noncomputable section

/-! ### Imitation Learning Setting -/

/-- An imitation learning setting: a finite-horizon MDP equipped with
    an expert policy and a learner policy, plus per-step classification
    error. The expert policy pi_E is the target; the learner pi_L is
    trained from demonstrations. -/
structure ImitationSetting where
  /-- The underlying finite-horizon MDP -/
  mdp : FiniteHorizonMDP
  /-- Expert policy: maps (step, state) to action -/
  pi_E : Fin mdp.H -> mdp.S -> mdp.A
  /-- Learner policy: maps (step, state) to action -/
  pi_L : Fin mdp.H -> mdp.S -> mdp.A
  /-- Per-step classification error: P[pi_L(s) != pi_E(s)] <= epsilon -/
  epsilon : Real
  epsilon_nonneg : 0 <= epsilon
  epsilon_le_one : epsilon <= 1

namespace ImitationSetting

variable (I : ImitationSetting)

/-! ### Behavior Cloning Error Bound

  If the learner achieves per-step classification error epsilon
  (i.e., at each step, P[pi_L(s) != pi_E(s)] <= epsilon), then
  the value gap satisfies:

    V^{pi_E} - V^{pi_L} <= H^2 * epsilon

  Informal proof sketch: by the performance difference lemma,
  the value gap decomposes as a sum over H steps of the expected
  advantage. At each step, the advantage is nonzero only when the
  learner takes a different action (probability <= epsilon), and the
  maximum one-step cost difference is at most H (since rewards are
  in [0,1] and there are at most H remaining steps). Summing over
  H steps gives H * H * epsilon = H^2 * epsilon.

  The H^2 scaling (rather than H) is the "compounding error" phenomenon
  that motivates DAgger. -/

/-! ### Policy Value Function

  V^π(k, s) = expected total reward starting from state s with k
  remaining steps under deterministic policy π. Uses the same
  "remaining steps" convention as `backwardQ`. -/

/-- Policy value function with k remaining steps under policy π. -/
def policyValue (M : FiniteHorizonMDP) (π : Fin M.H → M.S → M.A) :
    (k : ℕ) → k ≤ M.H → M.S → ℝ
  | 0, _, _ => 0
  | k + 1, hk, s =>
    let h : Fin M.H := ⟨M.H - k - 1, by omega⟩
    M.r h s (π h s) + ∑ s', M.P h s (π h s) s' * policyValue M π k (by omega) s'

/-- Terminal: V^π with 0 remaining steps is 0. -/
@[simp] theorem policyValue_zero (M : FiniteHorizonMDP)
    (π : Fin M.H → M.S → M.A) (hk : 0 ≤ M.H) (s : M.S) :
    policyValue M π 0 hk s = 0 := rfl

/-- Policy values are nonneg (rewards ≥ 0, P ≥ 0). -/
theorem policyValue_nonneg (M : FiniteHorizonMDP) (π : Fin M.H → M.S → M.A) :
    ∀ (k : ℕ) (hk : k ≤ M.H) (s : M.S), 0 ≤ policyValue M π k hk s := by
  intro k; induction k with
  | zero => intro _ s; simp
  | succ n ih =>
    intro hk s; simp only [policyValue]
    apply add_nonneg (M.r_nonneg _ s _)
    exact Finset.sum_nonneg fun s' _ => mul_nonneg (M.P_nonneg _ s _ s') (ih _ s')

/-- Policy value with k remaining steps is at most k. -/
theorem policyValue_le (M : FiniteHorizonMDP) (π : Fin M.H → M.S → M.A) :
    ∀ (k : ℕ) (hk : k ≤ M.H) (s : M.S), policyValue M π k hk s ≤ k := by
  intro k; induction k with
  | zero => intro _ s; simp
  | succ n ih =>
    intro hk s; simp only [policyValue]
    have hr : M.r ⟨M.H - n - 1, by omega⟩ s (π ⟨M.H - n - 1, by omega⟩ s) ≤ 1 :=
      M.r_le_one _ s _
    set h : Fin M.H := ⟨M.H - n - 1, by omega⟩
    have htrans : ∑ s', M.P h s (π h s) s' *
        policyValue M π n (by omega) s' ≤ n := by
      calc ∑ s', M.P h s (π h s) s' * policyValue M π n (by omega) s'
          ≤ ∑ s', M.P h s (π h s) s' * n := by
            apply Finset.sum_le_sum; intro s' _
            exact mul_le_mul_of_nonneg_left (ih _ s') (M.P_nonneg _ s _ s')
        _ = (∑ s', M.P h s (π h s) s') * n := (Finset.sum_mul _ _ _).symm
        _ = n := by rw [M.P_sum_one]; simp
    push_cast; linarith

/-! ### One-Step Value Gap Identity (Finite-Horizon PDL)

  The key telescoping identity for imitation learning:
  V^{π_E}(k+1, s) - V^{π_L}(k+1, s) =
    advantage(h, s) + ∑_{s'} P(h, s, π_L, s') · (V^{π_E}(k, s') - V^{π_L}(k, s'))

  where advantage(h, s) is the one-step reward/transition advantage
  of using π_E's action vs π_L's action, evaluated with V^{π_E}
  as the continuation value. -/

/-- One-step advantage of π_E over π_L at step h, state s.
    Uses V^{π_E} continuation value. -/
def oneStepAdvantage (I : ImitationSetting)
    (k : ℕ) (hk : k + 1 ≤ I.mdp.H) (s : I.mdp.S) : ℝ :=
  let h : Fin I.mdp.H := ⟨I.mdp.H - k - 1, by omega⟩
  let V_E := policyValue I.mdp I.pi_E k (by omega)
  (I.mdp.r h s (I.pi_E h s) + ∑ s', I.mdp.P h s (I.pi_E h s) s' * V_E s')
  - (I.mdp.r h s (I.pi_L h s) + ∑ s', I.mdp.P h s (I.pi_L h s) s' * V_E s')

/-- The one-step advantage is 0 when both policies agree at (h, s). -/
theorem oneStepAdvantage_eq_zero_of_agree (I : ImitationSetting)
    (k : ℕ) (hk : k + 1 ≤ I.mdp.H) (s : I.mdp.S)
    (h_agree : I.pi_L ⟨I.mdp.H - k - 1, by omega⟩ s =
      I.pi_E ⟨I.mdp.H - k - 1, by omega⟩ s) :
    I.oneStepAdvantage k hk s = 0 := by
  simp only [oneStepAdvantage, h_agree, sub_self]

/-- The one-step advantage is bounded by the remaining horizon. -/
theorem oneStepAdvantage_le (I : ImitationSetting)
    (k : ℕ) (hk : k + 1 ≤ I.mdp.H) (s : I.mdp.S) :
    I.oneStepAdvantage k hk s ≤ k + 1 := by
  simp only [oneStepAdvantage]
  set h : Fin I.mdp.H := ⟨I.mdp.H - k - 1, by omega⟩
  -- first term ≤ k+1 (reward ≤ 1, continuation ≤ k)
  have h_upper : I.mdp.r h s (I.pi_E h s) +
      ∑ s', I.mdp.P h s (I.pi_E h s) s' *
        policyValue I.mdp I.pi_E k (by omega) s' ≤ k + 1 := by
    have hr := I.mdp.r_le_one h s (I.pi_E h s)
    have ht : ∑ s', I.mdp.P h s (I.pi_E h s) s' *
        policyValue I.mdp I.pi_E k (by omega) s' ≤ k := by
      calc ∑ s', I.mdp.P h s (I.pi_E h s) s' * policyValue I.mdp I.pi_E k _ s'
          ≤ ∑ s', I.mdp.P h s (I.pi_E h s) s' * k := by
            apply Finset.sum_le_sum; intro s' _
            exact mul_le_mul_of_nonneg_left (policyValue_le _ _ _ _ _) (I.mdp.P_nonneg _ s _ s')
        _ = (∑ s', I.mdp.P h s (I.pi_E h s) s') * k := (Finset.sum_mul _ _ _).symm
        _ = k := by rw [I.mdp.P_sum_one]; simp
    linarith
  -- second term ≥ 0
  have h_lower : 0 ≤ I.mdp.r h s (I.pi_L h s) +
      ∑ s', I.mdp.P h s (I.pi_L h s) s' *
        policyValue I.mdp I.pi_E k (by omega) s' := by
    apply add_nonneg (I.mdp.r_nonneg _ s _)
    exact Finset.sum_nonneg fun s' _ =>
      mul_nonneg (I.mdp.P_nonneg _ s _ s') (policyValue_nonneg _ _ _ _ _)
  linarith

/-- **Finite-horizon performance-difference identity (one step).**

  V^{π_E}(k+1, s) - V^{π_L}(k+1, s) =
    advantage(k, s) + ∑_{s'} P(h, s, π_L, s') · (V^{π_E}(k, s') - V^{π_L}(k, s')) -/
theorem value_gap_one_step (I : ImitationSetting)
    (k : ℕ) (hk : k + 1 ≤ I.mdp.H) (s : I.mdp.S) :
    policyValue I.mdp I.pi_E (k + 1) hk s -
    policyValue I.mdp I.pi_L (k + 1) hk s =
    I.oneStepAdvantage k hk s +
    ∑ s', I.mdp.P ⟨I.mdp.H - k - 1, by omega⟩ s
      (I.pi_L ⟨I.mdp.H - k - 1, by omega⟩ s) s' *
      (policyValue I.mdp I.pi_E k (by omega) s' -
       policyValue I.mdp I.pi_L k (by omega) s') := by
  simp only [policyValue, oneStepAdvantage]
  have h_mul_sub : ∀ s' : I.mdp.S,
      I.mdp.P ⟨I.mdp.H - k - 1, by omega⟩ s
        (I.pi_L ⟨I.mdp.H - k - 1, by omega⟩ s) s' *
        (policyValue I.mdp I.pi_E k (by omega) s' -
         policyValue I.mdp I.pi_L k (by omega) s') =
      I.mdp.P ⟨I.mdp.H - k - 1, by omega⟩ s
        (I.pi_L ⟨I.mdp.H - k - 1, by omega⟩ s) s' *
        policyValue I.mdp I.pi_E k (by omega) s' -
      I.mdp.P ⟨I.mdp.H - k - 1, by omega⟩ s
        (I.pi_L ⟨I.mdp.H - k - 1, by omega⟩ s) s' *
        policyValue I.mdp I.pi_L k (by omega) s' := fun s' => by ring
  simp_rw [h_mul_sub, Finset.sum_sub_distrib]
  ring

/-- **Inductive value gap bound.**

  If the one-step advantage at each step is bounded by `f(j)` for all states,
  then the total value gap V^{π_E}(k) - V^{π_L}(k) ≤ ∑_{j<k} f(j). -/
theorem value_gap_le_sum (I : ImitationSetting)
    (f : ℕ → ℝ) (_f_nonneg : ∀ j, 0 ≤ f j)
    (h_adv : ∀ (j : ℕ) (hj : j + 1 ≤ I.mdp.H) (s : I.mdp.S),
      I.oneStepAdvantage j hj s ≤ f j) :
    ∀ (k : ℕ) (hk : k ≤ I.mdp.H) (s : I.mdp.S),
    policyValue I.mdp I.pi_E k hk s -
    policyValue I.mdp I.pi_L k hk s ≤
    ∑ j ∈ Finset.range k, f j := by
  intro k; induction k with
  | zero => intro _ s; simp
  | succ n ih =>
    intro hk s
    rw [value_gap_one_step I n hk s]
    -- advantage(n, s) ≤ f(n)
    have h1 := h_adv n hk s
    -- ∑ P_L · gap(n) ≤ ∑ P_L · (∑ f) = ∑ f (since ∑ P = 1)
    set h : Fin I.mdp.H := ⟨I.mdp.H - n - 1, by omega⟩
    have h2 : ∑ s', I.mdp.P h s (I.pi_L h s) s' *
        (policyValue I.mdp I.pi_E n (by omega) s' -
         policyValue I.mdp I.pi_L n (by omega) s') ≤
        ∑ j ∈ Finset.range n, f j := by
      calc ∑ s', I.mdp.P h s (I.pi_L h s) s' *
              (policyValue I.mdp I.pi_E n (by omega) s' -
               policyValue I.mdp I.pi_L n (by omega) s')
          ≤ ∑ s', I.mdp.P h s (I.pi_L h s) s' * (∑ j ∈ Finset.range n, f j) := by
            apply Finset.sum_le_sum; intro s' _
            exact mul_le_mul_of_nonneg_left (ih _ s') (I.mdp.P_nonneg _ s _ s')
        _ = (∑ s', I.mdp.P h s (I.pi_L h s) s') * (∑ j ∈ Finset.range n, f j) :=
            (Finset.sum_mul _ _ _).symm
        _ = ∑ j ∈ Finset.range n, f j := by rw [I.mdp.P_sum_one]; simp
    -- Combine: adv + cont ≤ f(n) + ∑_{j<n} f(j) = ∑_{j<n+1} f(j)
    calc I.oneStepAdvantage n hk s + _ ≤ f n + ∑ j ∈ Finset.range n, f j := by linarith
      _ = ∑ j ∈ Finset.range n, f j + f n := by ring
      _ = ∑ j ∈ Finset.range (n + 1), f j := by rw [Finset.sum_range_succ]

/-- **Behavior-cloning value gap bound: V^{π_E} - V^{π_L} ≤ H²ε.**

  If the per-step one-step advantage satisfies `advantage(j, s) ≤ ε·(j+1)`
  for all steps j and states s, then the total value gap is at most H²ε.

  The hypothesis holds when:
  - At each step, with probability ≤ ε, the learner disagrees with expert
  - When disagreeing, the worst-case advantage is ≤ remaining horizon = j+1

  This is the standard behavior-cloning compounding-error bound
  (Theorem 13.1 in Agarwal et al.). -/
theorem behavior_cloning_bound (I : ImitationSetting)
    (h_adv : ∀ (j : ℕ) (hj : j + 1 ≤ I.mdp.H) (s : I.mdp.S),
      I.oneStepAdvantage j hj s ≤ I.epsilon * (↑j + 1))
    (s₀ : I.mdp.S) :
    policyValue I.mdp I.pi_E I.mdp.H le_rfl s₀ -
    policyValue I.mdp I.pi_L I.mdp.H le_rfl s₀ ≤
    (I.mdp.H : ℝ) ^ 2 * I.epsilon := by
  have h_gap := value_gap_le_sum I (fun j => I.epsilon * (↑j + 1))
    (fun j => mul_nonneg I.epsilon_nonneg (by positivity)) h_adv I.mdp.H le_rfl s₀
  calc policyValue I.mdp I.pi_E I.mdp.H le_rfl s₀ -
        policyValue I.mdp I.pi_L I.mdp.H le_rfl s₀
      ≤ ∑ j ∈ Finset.range I.mdp.H, I.epsilon * (↑j + 1) := h_gap
    _ = I.epsilon * ∑ j ∈ Finset.range I.mdp.H, (↑j + 1) := by
        rw [Finset.mul_sum]
    _ ≤ I.epsilon * (I.mdp.H ^ 2 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ I.epsilon_nonneg
        -- ∑_{j<H} (j+1) = H(H+1)/2 ≤ H²
        calc ∑ j ∈ Finset.range I.mdp.H, ((↑j : ℝ) + 1)
            = ∑ j ∈ Finset.range I.mdp.H, (↑j + 1 : ℝ) := by rfl
          _ ≤ ∑ _j ∈ Finset.range I.mdp.H, (I.mdp.H : ℝ) := by
              apply Finset.sum_le_sum; intro j hj
              rw [Finset.mem_range] at hj
              have : j + 1 ≤ I.mdp.H := hj
              exact_mod_cast this
          _ = (I.mdp.H : ℝ) ^ 2 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ = (I.mdp.H : ℝ) ^ 2 * I.epsilon := by ring

/-- Legacy wrapper, kept for compatibility. -/
theorem behavior_cloning_bound_from_pdl
    (V_expert V_learner : Real)
    (_hVE : V_expert <= I.mdp.H)
    (_hVL : 0 <= V_learner)
    (hPDL : V_expert - V_learner <=
      I.mdp.H * (I.epsilon * I.mdp.H)) :
    V_expert - V_learner <= (I.mdp.H : Real) ^ 2 * I.epsilon := by
  calc V_expert - V_learner
      <= I.mdp.H * (I.epsilon * I.mdp.H) := hPDL
    _ = (I.mdp.H : Real) ^ 2 * I.epsilon := by ring

/-! ### DAgger: Dataset Aggregation

  DAgger addresses the compounding error of behavior cloning by
  iteratively collecting data under the learner's policy but
  labeling with the expert. After T rounds:
  - Round t: roll out pi_t, query expert for labels, add to dataset
  - Train pi_{t+1} on the aggregated dataset

  This reduces the H^2 dependence to H. -/

/-- A DAgger setting extends the imitation setting with round and
    sample count parameters. -/
structure DAggerSetting where
  /-- Base imitation setting -/
  base : ImitationSetting
  /-- Number of DAgger rounds -/
  T : Nat
  hT : 0 < T
  /-- Number of samples per round -/
  N : Nat
  hN : 0 < N

end ImitationSetting

end
