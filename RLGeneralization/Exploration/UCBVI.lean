/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# UCB Value Iteration (UCBVI)

Definitions for the UCBVI algorithm and the algebraic core of its
finite-horizon regret analysis.

## Main Definitions

* `UCBVIBonus` - The exploration bonus β_h(s,a)
* `UCBVIQ` - Optimistic Q-function Q̂_h = r_h + P̂_h V̂_{h+1} + bonus
* `regret` - Cumulative regret over K episodes

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.MDP.FiniteHorizon
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

noncomputable section

namespace FiniteHorizonMDP

variable (M : FiniteHorizonMDP)

/-! ### Exploration Bonus -/

/-- Visit count N_h(s,a) = number of times (s,a) visited at step h
    across episodes 1,...,k-1. -/
def visitCount (episodes : ℕ) (history : Fin episodes →
    Fin M.H → M.S × M.A) (h : Fin M.H) (s : M.S) (a : M.A) : ℕ :=
  (Finset.univ.filter (fun ep =>
    (history ep h).1 = s ∧ (history ep h).2 = a)).card

/-- UCBVI exploration bonus:
    `β_h(s,a) = c · H · √(log(SAHK/δ) / max(N_h(s,a), 1))`. -/
def ucbBonus (c H_val : ℝ) (log_term : ℝ) (n : ℕ) : ℝ :=
  c * H_val * Real.sqrt (log_term / max n 1)

/-! ### Optimistic Q-function -/

/-- UCBVI optimistic backward induction (Algorithm 6):
    Q̂_H = 0
    Q̂_h(s,a) = min(r̂_h(s,a) + P̂_h V̂_{h+1}(s,a) + bonus, H-h)
    V̂_h(s) = max_a Q̂_h(s,a)

    The min-clipping at H-h ensures Q̂ is bounded. -/
def ucbviQ (bonus : Fin M.H → M.S → M.A → ℝ)
    (P_hat : Fin M.H → M.S → M.A → M.S → ℝ)
    (r_hat : Fin M.H → M.S → M.A → ℝ) :
    (k : ℕ) → (hk : k ≤ M.H) → M.S → M.A → ℝ
  | 0, _, _, _ => 0
  | k + 1, hk, s, a =>
    let h : Fin M.H := ⟨M.H - k - 1, by omega⟩
    min (r_hat h s a +
      ∑ s', P_hat h s a s' *
        Finset.univ.sup' Finset.univ_nonempty
          (fun a' => ucbviQ bonus P_hat r_hat k (by omega) s' a') +
      bonus h s a) k

/-! ### Regret -/

/-- Per-episode regret: V*_0(s_0) - V^{π_k}_0(s_0)
    where π_k is the greedy policy w.r.t. Q̂^k. -/
def episodeRegret (V_star_0 : M.S → ℝ)
    (V_policy_0 : M.S → ℝ) (s_0 : M.S) : ℝ :=
  V_star_0 s_0 - V_policy_0 s_0

/-- Cumulative regret over K episodes:
    R_K = ∑_{k=1}^K (V*_0(s_0^k) - V^{π_k}_0(s_0^k)) -/
def cumulativeRegret (K : ℕ)
    (V_star_0 : M.S → ℝ)
    (V_policies : Fin K → M.S → ℝ)
    (starts : Fin K → M.S) : ℝ :=
  ∑ k : Fin K, M.episodeRegret V_star_0 (V_policies k) (starts k)

/-- Cumulative regret is nonneg when V* ≥ V^π (optimality). -/
theorem cumulativeRegret_nonneg (K : ℕ)
    (V_star_0 : M.S → ℝ)
    (V_policies : Fin K → M.S → ℝ)
    (starts : Fin K → M.S)
    (h_opt : ∀ k s, V_policies k s ≤ V_star_0 s) :
    0 ≤ M.cumulativeRegret K V_star_0 V_policies starts := by
  unfold cumulativeRegret episodeRegret
  apply Finset.sum_nonneg
  intro k _
  linarith [h_opt k (starts k)]

/-! ### Per-Step Value Gap -/

/-- **Per-step value gap nonnegativity**.

  V*_k(s) - Q*_k(s,a) ≥ 0 for all a, since V*_k = max_a Q*_k.

  This is the pointwise ingredient for the one-episode regret
  decomposition. The full telescoping decomposition
  V*_0(s₀) - V^π_0(s₀) = ∑_h E[...] is NOT proved here. -/
theorem per_step_value_gap_nonneg
    (k : ℕ) (hk : k ≤ M.H) (s : M.S) (a : M.A) :
    Finset.univ.sup' Finset.univ_nonempty
      (fun a' => M.backwardQ k hk s a') -
    M.backwardQ k hk s a ≥ 0 := by
  linarith [Finset.le_sup' (fun a' => M.backwardQ k hk s a')
    (Finset.mem_univ a)]

/-! ### Regret Decomposition

  The one-episode regret decomposition is the core identity used in
  the UCBVI regret analysis. For a deterministic policy π and the
  optimal value V*, the regret at step k decomposes into:
    - an "advantage" term: V*_k(s) - Q*_k(s, π(s)), and
    - a future term: Σ P(s'|s, π(s)) · [V*_{k-1}(s') - V^π_{k-1}(s')].

  This is the core algebraic identity and is also the same
  decomposition used in the simulation lemma / performance difference
  lemma throughout this repository.
-/

/-- Optimal value function: V*_k(s) = max_a Q*_k(s,a).
    (Local copy for UCBVI; same as in LSVI.lean.) -/
def optValFn (k : ℕ) (hk : k ≤ M.H) (s : M.S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a => M.backwardQ k hk s a)

/-- Value function of a deterministic policy π.
    V^π with 0 remaining steps = 0 (terminal).
    V^π with k+1 remaining steps = r_h(s,π(s)) + Σ P(s'|s,π(s)) V^π_k(s'). -/
def policyValueFn (π : Fin M.H → M.S → M.A) :
    (k : ℕ) → (hk : k ≤ M.H) → M.S → ℝ
  | 0, _, _ => 0
  | k + 1, hk, s =>
    let h : Fin M.H := ⟨M.H - k - 1, by omega⟩
    M.r h s (π h s) + ∑ s', M.P h s (π h s) s' *
      policyValueFn π k (by omega) s'

/-- Terminal condition for the policy value function. -/
theorem policyValueFn_zero (π : Fin M.H → M.S → M.A)
    (hk : 0 ≤ M.H) (s : M.S) :
    M.policyValueFn π 0 hk s = 0 := rfl

/-- **One-step regret decomposition**.

  V*_{k+1}(s) - V^π_{k+1}(s)
    = [V*_{k+1}(s) - Q*_{k+1}(s, π(s))]
    + Σ_{s'} P(s'|s, π(s)) · [V*_k(s') - V^π_k(s')]

  The first term is the "advantage" of the optimal policy over π
  at state s; it is nonneg because V* = max Q*.
  The second term propagates the regret from future steps.

  This is the key algebraic identity underlying the regret
  decomposition used in the UCBVI analysis. -/
theorem regret_decomposition_step
    (π : Fin M.H → M.S → M.A)
    (k : ℕ) (hk : k + 1 ≤ M.H) (s : M.S) :
    M.optValFn (k + 1) hk s -
    M.policyValueFn π (k + 1) hk s =
    (M.optValFn (k + 1) hk s -
      M.backwardQ (k + 1) hk s (π ⟨M.H - k - 1, by omega⟩ s)) +
    ∑ s', M.P ⟨M.H - k - 1, by omega⟩ s
        (π ⟨M.H - k - 1, by omega⟩ s) s' *
      (M.optValFn k (by omega) s' -
       M.policyValueFn π k (by omega) s') := by
  -- Q*_{k+1}(s, π(s)) = r(s,π(s)) + Σ P V*_k
  -- V^π_{k+1}(s)     = r(s,π(s)) + Σ P V^π_k
  -- So Q*(s,π(s)) - V^π(s) = Σ P (V*_k - V^π_k)
  -- Therefore: V* - V^π = (V* - Q*(π(s))) + Σ P (V*_k - V^π_k)
  set a_pi := π ⟨M.H - k - 1, by omega⟩ s
  have h_Q_star : M.backwardQ (k + 1) hk s a_pi =
      M.r ⟨M.H - k - 1, by omega⟩ s a_pi +
      ∑ s', M.P ⟨M.H - k - 1, by omega⟩ s a_pi s' *
        M.optValFn k (by omega) s' := by
    unfold backwardQ optValFn; rfl
  have h_V_pi : M.policyValueFn π (k + 1) hk s =
      M.r ⟨M.H - k - 1, by omega⟩ s a_pi +
      ∑ s', M.P ⟨M.H - k - 1, by omega⟩ s a_pi s' *
        M.policyValueFn π k (by omega) s' := by
    simp only [policyValueFn]; rfl
  -- Q*(a_pi) - V^pi = sum P (V*_k - V^pi_k)
  have h_diff : M.backwardQ (k + 1) hk s a_pi -
      M.policyValueFn π (k + 1) hk s =
      ∑ s', M.P ⟨M.H - k - 1, by omega⟩ s a_pi s' *
        (M.optValFn k (by omega) s' -
         M.policyValueFn π k (by omega) s') := by
    rw [h_Q_star, h_V_pi, add_sub_add_left_eq_sub]
    rw [← Finset.sum_sub_distrib]
    congr 1; ext s'; ring
  -- V* - V^pi = (V* - Q*(a_pi)) + (Q*(a_pi) - V^pi)
  linarith

/-- The advantage term in the regret decomposition is nonneg:
    V*_{k}(s) - Q*_{k}(s, a) ≥ 0 for any action a.

    This is a restatement of `per_step_value_gap_nonneg` using
    `optValFn`. -/
theorem advantage_nonneg
    (k : ℕ) (hk : k ≤ M.H) (s : M.S) (a : M.A) :
    0 ≤ M.optValFn k hk s - M.backwardQ k hk s a := by
  unfold optValFn
  linarith [Finset.le_sup' (fun a' => M.backwardQ k hk s a')
    (Finset.mem_univ a)]

/-- **Regret nonnegativity from decomposition**.

  V*_k(s) - V^π_k(s) ≥ 0, proved by induction using the
  one-step decomposition. Each step contributes a nonneg
  advantage term, and future terms are nonneg by IH.

  This gives an alternative proof of backward induction
  optimality via the regret decomposition. -/
theorem regret_nonneg_inductive
    (π : Fin M.H → M.S → M.A) :
    ∀ (k : ℕ) (hk : k ≤ M.H) (s : M.S),
    0 ≤ M.optValFn k hk s - M.policyValueFn π k hk s := by
  intro k
  induction k with
  | zero =>
    intro hk s
    simp [optValFn, policyValueFn, backwardQ]
  | succ n ih =>
    intro hk s
    -- Use the one-step decomposition
    rw [M.regret_decomposition_step π n hk s]
    apply add_nonneg
    · -- Advantage term is nonneg
      exact M.advantage_nonneg (n + 1) hk s
        (π ⟨M.H - n - 1, by omega⟩ s)
    · -- Future term: Σ P · (nonneg) ≥ 0
      apply Finset.sum_nonneg; intro s' _
      apply mul_nonneg (M.P_nonneg _ _ _ s')
      exact ih (by omega) s'

/-- **Uniform advantage bound**.

  If the per-step advantage satisfies V*_k(s) - Q*_k(s, pi(s)) <= epsilon
  uniformly over all steps k and states s, then:

    V*_k(s) - V^pi_k(s) <= k * epsilon

  Proved by induction using `regret_decomposition_step`. Each step
  contributes at most epsilon from the advantage, and the future
  terms are bounded by the inductive hypothesis weighted by
  transition probabilities (which sum to 1).

  **Caveat**: This is the deterministic algebraic ingredient for
  the full UCBVI regret proof. The full analysis replaces epsilon with the
  sum of exploration bonuses along the trajectory. -/
theorem regret_from_uniform_advantage_bound
    (π : Fin M.H → M.S → M.A)
    (ε : ℝ)
    (h_adv : ∀ (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S),
      M.optValFn (j + 1) hj s -
      M.backwardQ (j + 1) hj s
        (π ⟨M.H - j - 1, by omega⟩ s) ≤ ε) :
    ∀ (k : ℕ) (hk : k ≤ M.H) (s : M.S),
    M.optValFn k hk s -
    M.policyValueFn π k hk s ≤ k * ε := by
  intro k
  induction k with
  | zero =>
    intro hk s
    simp [optValFn, policyValueFn, backwardQ]
  | succ n ih =>
    intro hk s
    -- Decompose via the one-step identity
    rw [M.regret_decomposition_step π n hk s]
    -- Advantage term ≤ ε
    have h1 : M.optValFn (n + 1) hk s -
        M.backwardQ (n + 1) hk s
          (π ⟨M.H - n - 1, by omega⟩ s) ≤ ε :=
      h_adv n hk s
    -- Future term ≤ n · ε
    have h2 : ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s
          (π ⟨M.H - n - 1, by omega⟩ s) s' *
        (M.optValFn n (by omega) s' -
         M.policyValueFn π n (by omega) s') ≤ n * ε := by
      calc ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s
              (π ⟨M.H - n - 1, by omega⟩ s) s' *
            (M.optValFn n (by omega) s' -
             M.policyValueFn π n (by omega) s')
          ≤ ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s
              (π ⟨M.H - n - 1, by omega⟩ s) s' *
            (↑n * ε) := by
            apply Finset.sum_le_sum; intro s' _
            apply mul_le_mul_of_nonneg_left (ih (by omega) s')
              (M.P_nonneg _ _ _ s')
        _ = (∑ s', M.P ⟨M.H - n - 1, by omega⟩ s
              (π ⟨M.H - n - 1, by omega⟩ s) s') *
            (↑n * ε) := (Finset.sum_mul _ _ _).symm
        _ = ↑n * ε := by rw [M.P_sum_one, one_mul]
    -- Combine: ε + n·ε = (n+1)·ε
    calc (M.optValFn (n + 1) hk s -
            M.backwardQ (n + 1) hk s
              (π ⟨M.H - n - 1, by omega⟩ s)) +
          ∑ s', M.P ⟨M.H - n - 1, by omega⟩ s
              (π ⟨M.H - n - 1, by omega⟩ s) s' *
            (M.optValFn n (by omega) s' -
             M.policyValueFn π n (by omega) s')
        ≤ ε + ↑n * ε := add_le_add h1 h2
      _ = (↑(n + 1) : ℝ) * ε := by push_cast; ring

/-- **Episode regret bound for UCBVI**.

  If the UCBVI exploration bonus ensures that at each step h the
  advantage gap V*(s) - Q*(s,π(s)) ≤ ε, then the per-episode
  regret V*_H(s) - V^π_H(s) ≤ H · ε.

  In the full UCBVI analysis, ε is replaced by the
  sum of exploration bonuses along the trajectory, yielding the
  O(√(H³SAK)) cumulative regret bound. -/
theorem episode_regret_bound
    (π : Fin M.H → M.S → M.A) (s₀ : M.S)
    (ε : ℝ)
    (h_adv : ∀ (j : ℕ) (hj : j + 1 ≤ M.H) (s : M.S),
      M.optValFn (j + 1) hj s -
      M.backwardQ (j + 1) hj s
        (π ⟨M.H - j - 1, by omega⟩ s) ≤ ε) :
    M.optValFn M.H le_rfl s₀ -
    M.policyValueFn π M.H le_rfl s₀ ≤ M.H * ε :=
  M.regret_from_uniform_advantage_bound π ε h_adv M.H le_rfl s₀

/-! ### Optimism and UCBVI Regret Bound

  The UCBVI regret analysis proceeds in three steps:

  1. **Optimism**: The UCB bonuses ensure Q̂_h^k(s,a) ≥ Q*_h(s,a)
     with high probability.

  2. **Per-episode regret ≤ sum of bonuses**: Under optimism, the
     greedy policy π_k w.r.t. Q̂^k satisfies
       V*_H(s) - V^{π_k}_H(s) ≤ ∑_h bonus_h^k(s_h, a_h).

  3. **Total bonus control**: By the pigeonhole / Cauchy-Schwarz
     argument on visit counts,
       ∑_k ∑_h bonus ≤ O(√(H³·|S|·|A|·K)).

  We formalize the optimism property as a hypothesis, prove the
  regret-to-bonus reduction, and state the full regret wrapper. -/

/-- **Optimism hypothesis**.

  The UCB Q-values upper-bound Q* at every episode, step,
  state, and action.  In the full proof this follows from the
  exploration bonus being at least the estimation error;
  here we take it as a hypothesis. -/
def isOptimistic
    (Q_ucb : ℕ → Fin M.H → M.S → M.A → ℝ) : Prop :=
  ∀ (k : ℕ) (h : Fin M.H) (s : M.S) (a : M.A),
    M.backwardQ (M.H - h.val) (by omega) s a ≤ Q_ucb k h s a

/-- **Cumulative regret bounded by total bonuses**.

  If each episode's regret is bounded by the sum of bonuses
  (hypothesis `h_per_ep`), then cumulative regret over K episodes
  is bounded by the total bonus sum:
    Regret(K) ≤ ∑_{k} ∑_{h} bonus_k_h -/
theorem cumulative_regret_le_total_bonuses
    (K : ℕ)
    (V_star_0 : M.S → ℝ)
    (V_policies : Fin K → M.S → ℝ)
    (starts : Fin K → M.S)
    (bonus : Fin K → Fin M.H → ℝ)
    (h_per_ep : ∀ k : Fin K,
      V_star_0 (starts k) - V_policies k (starts k) ≤
      ∑ h : Fin M.H, bonus k h) :
    M.cumulativeRegret K V_star_0 V_policies starts ≤
    ∑ k : Fin K, ∑ h : Fin M.H, bonus k h := by
  unfold cumulativeRegret episodeRegret
  exact Finset.sum_le_sum (fun k _ => h_per_ep k)

/-- **Total bonus bound** (pigeonhole + Cauchy-Schwarz).

  The UCBVI bonus at step h, state s, action a in episode k is
    β = c · H · √(log(HSAK/δ) / N_h^k(s,a)).

  By the pigeonhole argument on visit counts (Lemma B.5):
    ∑_k ∑_h β_h^k(s_h^k, a_h^k) ≤ c' · √(H³ · |S| · |A| · K · log(...))

  We state this as a hypothesis for the final regret wrapper. -/
def totalBonusBound
    (bonus : Fin K → Fin M.H → ℝ)
    (C : ℝ) (δ : ℝ) : Prop :=
  ∑ k : Fin K, ∑ h : Fin M.H, bonus k h ≤
    C * Real.sqrt (M.H ^ 3 * (Fintype.card M.S) * (Fintype.card M.A) *
      K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ))

/-- **Algebraic core of the UCBVI regret proof**.

  Chains two hypotheses into the UCBVI regret bound:
    Regret(K) ≤ C · √(H³·|S|·|A|·K·log(HSAK/δ))

  **Caveat**: This is NOT the full UCBVI proof. Both the
  per-episode bound (h_per_ep, from optimism) and the total
  bonus bound (h_bonus, from pigeonhole/Cauchy-Schwarz) are
  taken as hypotheses. The `isOptimistic` definition is stated
  but not used in this theorem. A full formalization would need
  to derive these from the UCBVI algorithm + Hoeffding/Azuma,
  which requires a probability space not present here. -/
theorem ucbvi_regret_from_bonus_hypotheses
    (K : ℕ)
    (V_star_0 : M.S → ℝ)
    (V_policies : Fin K → M.S → ℝ)
    (starts : Fin K → M.S)
    (bonus : Fin K → Fin M.H → ℝ)
    (C : ℝ) (δ : ℝ) (_hδ : 0 < δ)
    -- Hypothesis 1: per-episode regret ≤ sum of bonuses (from optimism)
    (h_per_ep : ∀ k : Fin K,
      V_star_0 (starts k) - V_policies k (starts k) ≤
      ∑ h : Fin M.H, bonus k h)
    -- Hypothesis 2: total bonus bound (from pigeonhole/Cauchy-Schwarz)
    (h_bonus : M.totalBonusBound bonus C δ) :
    M.cumulativeRegret K V_star_0 V_policies starts ≤
    C * Real.sqrt (M.H ^ 3 * (Fintype.card M.S) * (Fintype.card M.A) *
      K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ)) := by
  calc M.cumulativeRegret K V_star_0 V_policies starts
      ≤ ∑ k : Fin K, ∑ h : Fin M.H, bonus k h :=
        M.cumulative_regret_le_total_bonuses K V_star_0 V_policies starts
          bonus h_per_ep
    _ ≤ C * Real.sqrt (M.H ^ 3 * (Fintype.card M.S) * (Fintype.card M.A) *
          K * Real.log (M.H * (Fintype.card M.S) * (Fintype.card M.A) * K / δ)) :=
        h_bonus

end FiniteHorizonMDP

end
