/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Generative Model Probability Space

Constructs the product probability space for the generative model
(i.i.d. categorical samples from an MDP's transition kernel) and
connects it to the minimax sample complexity theorem.

## Architecture

The generative model draws N i.i.d. samples from P(.|s,a) for each
(s,a) pair. The full sample space is:

    Omega = forall (idx : S x A x Fin N), S

with the product measure `pi_{idx} P(.|s_idx, a_idx)`.

### What Mathlib provides (as of v4.28):

1. `PMF alpha` -- probability mass functions on alpha
2. `PMF.toMeasure` -- converts PMF to a MeasureTheory.Measure
3. `PMF.toMeasure.isProbabilityMeasure` -- the result is a probability measure
4. `Measure.pi` -- finite product of measures on `forall i, alpha i`
5. `pi.instIsProbabilityMeasure` -- product of prob measures is a prob measure
6. `iIndepFun_pi` -- projections from a product space are independent
7. `iIndepFun.mgf_sum` -- MGF factors for independent r.v.s

### What this module adds on top of `GenerativeModelCore`:

* `empiricalApproxMDPRV` / `empiricalModelMDP` -- canonical empirical models
* `empiricalModelValueFromQ` -- convert empirical Q-fixed points to values
* `empiricalGreedyPolicy` / `empiricalGreedyValue` -- canonical greedy-side witnesses
* `bernstein_per_entry` -- conditional Bernstein helper
* `minimax_from_generative_model` -- deterministic minimax reduction
* high-probability minimax corollaries with increasingly canonical witnesses

## References

* [Azar, Munos, Kappen, *Minimax PAC bounds on the sample complexity
  of RL with a generative model*][azar2013]
* [Agarwal et al., *RL: Theory and Algorithms*]
-/

import RLGeneralization.Concentration.GenerativeModelCore
import RLGeneralization.Generalization.MinimaxSampleComplexity
import RLGeneralization.MDP.BanachFixedPoint
import RLGeneralization.MDP.PolicyIteration

open Finset BigOperators MeasureTheory ProbabilityTheory ENNReal

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-- The canonical empirical approximate MDP extracted from a generative-model
    sample point, using the empirical transition kernel and the true reward. -/
def empiricalApproxMDPRV {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) : M.ApproxMDP where
  P_hat := M.empiricalTransitionRV hN ω
  r_hat := M.r
  P_hat_nonneg := M.empiricalTransitionRV_nonneg hN ω
  P_hat_sum_one := M.empiricalTransitionRV_sum_one hN ω

/-- The empirical sample point viewed as an actual finite MDP with the empirical
    transition kernel and the true reward function. -/
def empiricalModelMDP {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) : FiniteMDP where
  S := M.S
  A := M.A
  P := M.empiricalTransitionRV hN ω
  r := M.r
  γ := M.γ
  P_nonneg := M.empiricalTransitionRV_nonneg hN ω
  P_sum_one := M.empiricalTransitionRV_sum_one hN ω
  r_bound := M.r_bound
  γ_nonneg := M.γ_nonneg
  γ_lt_one := M.γ_lt_one

/-- Reuse a policy on the true MDP as a policy on the empirical-model MDP
    extracted from a sample point. -/
def toEmpiricalModelPolicy {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) (π : M.StochasticPolicy) :
    (M.empiricalModelMDP hN ω).StochasticPolicy where
  prob := π.prob
  prob_nonneg := π.prob_nonneg
  prob_sum_one := π.prob_sum_one

/-- Forget a policy on the empirical-model MDP back to the underlying policy on
    the true state-action space. -/
def ofEmpiricalModelPolicy {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (π : (M.empiricalModelMDP hN ω).StochasticPolicy) : M.StochasticPolicy where
  prob := π.prob
  prob_nonneg := π.prob_nonneg
  prob_sum_one := π.prob_sum_one

/-- The greedy policy induced by the canonical Bellman-optimal fixed point of
    the empirical model. -/
def empiricalOptimalPolicy {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) :
    (M.empiricalModelMDP hN ω).StochasticPolicy :=
  (M.empiricalModelMDP hN ω).greedyStochasticPolicy
    ((M.empiricalModelMDP hN ω).optimalQFixedPoint)

/-- The empirical-model greedy policy viewed back on the original MDP state and
    action space. -/
def empiricalGreedyPolicy {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) : M.StochasticPolicy :=
  M.ofEmpiricalModelPolicy hN ω (M.empiricalOptimalPolicy hN ω)

/-- The state-value function induced by an empirical-model action-value function
    under a fixed policy, expressed on the original state space. -/
def empiricalModelValueFromQ {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (π : M.StochasticPolicy)
    (Q : (M.empiricalModelMDP hN ω).ActionValueFn) : M.StateValueFn :=
  fun s => ∑ a, π.prob s a * Q s a

/-- If `Q` is an action-value fixed point for policy `π` in the empirical model,
    then the policy-weighted action values satisfy the empirical Bellman equation. -/
theorem empiricalModelValueFromQ_isValueOf {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (π : M.StochasticPolicy)
    (Q : (M.empiricalModelMDP hN ω).ActionValueFn)
    (hQ :
      (M.empiricalModelMDP hN ω).isActionValueOf Q
        (M.toEmpiricalModelPolicy hN ω π)) :
    (M.empiricalModelMDP hN ω).isValueOf
      (M.empiricalModelValueFromQ hN ω π Q)
      (M.toEmpiricalModelPolicy hN ω π) := by
  intro s
  dsimp [FiniteMDP.isValueOf, empiricalModelValueFromQ,
    FiniteMDP.expectedReward, FiniteMDP.expectedNextValue]
  calc
    ∑ a, π.prob s a * Q s a
      = ∑ a, π.prob s a *
          ((M.empiricalModelMDP hN ω).r s a +
            (M.empiricalModelMDP hN ω).γ * ∑ s',
              (M.empiricalModelMDP hN ω).P s a s' *
                (∑ a', (M.toEmpiricalModelPolicy hN ω π).prob s' a' * Q s' a')) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hQ s a]
    _ = (∑ a, π.prob s a * (M.empiricalModelMDP hN ω).r s a) +
        (M.empiricalModelMDP hN ω).γ *
          (∑ a, π.prob s a *
            ∑ s', (M.empiricalModelMDP hN ω).P s a s' *
              (∑ a', (M.toEmpiricalModelPolicy hN ω π).prob s' a' * Q s' a')) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
          congr 1
          have hγ :
              ∀ a, π.prob s a *
                ((M.empiricalModelMDP hN ω).γ *
                  ∑ s', (M.empiricalModelMDP hN ω).P s a s' *
                    (∑ a', (M.toEmpiricalModelPolicy hN ω π).prob s' a' * Q s' a')) =
                (M.empiricalModelMDP hN ω).γ *
                  (π.prob s a *
                    ∑ s', (M.empiricalModelMDP hN ω).P s a s' *
                      (∑ a', (M.toEmpiricalModelPolicy hN ω π).prob s' a' * Q s' a')) := by
            intro a
            ring
          simp_rw [hγ]
          exact (Finset.mul_sum _ _ _).symm
    _ = (∑ a, (M.toEmpiricalModelPolicy hN ω π).prob s a *
            (M.empiricalModelMDP hN ω).r s a) +
        (M.empiricalModelMDP hN ω).γ *
          (∑ a, (M.toEmpiricalModelPolicy hN ω π).prob s a *
            ∑ s', (M.empiricalModelMDP hN ω).P s a s' *
              (M.empiricalModelValueFromQ hN ω π Q) s') := by
          change
            (∑ a, π.prob s a * (M.empiricalModelMDP hN ω).r s a) +
              (M.empiricalModelMDP hN ω).γ *
                (∑ a, π.prob s a *
                  ∑ s', (M.empiricalModelMDP hN ω).P s a s' *
                    (∑ a', π.prob s' a' * Q s' a')) =
            (∑ a, π.prob s a * (M.empiricalModelMDP hN ω).r s a) +
              (M.empiricalModelMDP hN ω).γ *
                (∑ a, π.prob s a *
                  ∑ s', (M.empiricalModelMDP hN ω).P s a s' *
                    (∑ a', π.prob s' a' * Q s' a'))
          rfl

/-- The canonical true-model value function of the empirical greedy policy,
    obtained by Banach policy evaluation on the original MDP. -/
def empiricalGreedyValue {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) : M.StateValueFn :=
  M.valueFromQ (M.empiricalGreedyPolicy hN ω)
    (M.actionValueFixedPoint (M.empiricalGreedyPolicy hN ω))

/-- The canonical true-model value associated with the empirical greedy policy
    satisfies the Bellman evaluation equation on the original MDP. -/
theorem empiricalGreedyValue_isValueOf {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S) :
    M.isValueOf (M.empiricalGreedyValue hN ω) (M.empiricalGreedyPolicy hN ω) := by
  exact M.valueFromQ_isValueOf (M.empiricalGreedyPolicy hN ω)
    (M.actionValueFixedPoint (M.empiricalGreedyPolicy hN ω))
    (M.actionValueFixedPoint_isActionValueOf (M.empiricalGreedyPolicy hN ω))

/-! ### Bernstein Concentration Machinery

The finite-index Bernstein bridge (`bernstein_sum_fintype`) closes the
`Fin N` versus `ℕ` indexing gap. The following theorems specialize
Bernstein's inequality to the actual empirical transition coordinates
with the exact Bernoulli variance profile, culminating in
`generative_model_pac_bernstein`. -/

/-- **Bernstein concentration for empirical transition entries.**

    Given N i.i.d. centered indicator random variables X_i with
    |X_i| <= 1, E[X_i] = 0, Var(X_i) <= 1/4, the sum satisfies
    the one-sided Bernstein bound.

    Direct application of `bernstein_sum` with b = 1, V = N/4. -/
theorem bernstein_per_entry
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} [IsProbabilityMeasure mu]
    {N : ℕ} (hN : 0 < N)
    (X : ℕ → Omega → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X mu)
    (h_bound : ∀ i, ∀ᵐ omega ∂mu, |X i omega| ≤ 1)
    (h_mean : ∀ i, ∫ omega, X i omega ∂mu = 0)
    (h_var : ∀ i, ∫ omega, (X i omega) ^ 2 ∂mu ≤ 1 / 4)
    {t : ℝ} (ht : 0 < t) :
    mu.real {omega | t ≤ ∑ i ∈ range N, X i omega} ≤
      Real.exp (-t ^ 2 / (2 * (↑N * (1 / 4)) + 2 * 1 * t / 3)) := by
  have h_var_sum : ∑ i ∈ range N, ∫ omega, (X i omega) ^ 2 ∂mu ≤
      ↑N * (1 / 4) := by
    calc ∑ i ∈ range N, ∫ omega, (X i omega) ^ 2 ∂mu
        ≤ ∑ _i ∈ range N, (1 / 4 : ℝ) :=
          Finset.sum_le_sum fun i _ => h_var i
      _ = ↑N * (1 / 4) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact bernstein_sum hN hX_meas h_indep (by positivity : (0 : ℝ) < 1)
    h_bound h_mean (by positivity) h_var_sum ht

/-- A finite-index Bernstein tail bound specialized to independent families
    indexed by a finite type. This closes the `Fin N` versus `ℕ` gap for the
    generative-model product space. -/
theorem bernstein_sum_fintype
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    {b : ℝ} (hb : 0 < b)
    (h_bound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    {V : ℝ} (hV : 0 ≤ V)
    (h_var_sum : ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ ≤ V)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ∑ i, X i ω} ≤
      Real.exp (-t^2 / (2 * V + 2 * b * t / 3)) := by
  classical
  rcases eq_or_lt_of_le hV with rfl | hV_pos
  · have h_nonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ ∫ ω, (X i ω) ^ 2 ∂μ :=
      fun i _ => integral_nonneg fun ω => sq_nonneg _
    have h_sum_zero : ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ = 0 :=
      le_antisymm h_var_sum (Finset.sum_nonneg h_nonneg)
    have h_each_zero : ∀ i ∈ (Finset.univ : Finset ι), ∫ ω, (X i ω) ^ 2 ∂μ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_sum_zero
    have h_Xi_ae : ∀ i ∈ (Finset.univ : Finset ι), X i =ᵐ[μ] 0 := by
      intro i hi
      have h_int_sq : Integrable (fun ω => (X i ω) ^ 2) μ :=
        Integrable.of_bound ((hX_meas i).pow_const 2).aestronglyMeasurable (b ^ 2)
          (by
            filter_upwards [h_bound i] with ω hω
            rw [Real.norm_eq_abs, abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) hω 2)
      have h_sq_ae : (fun ω => (X i ω) ^ 2) =ᵐ[μ] 0 :=
        (integral_eq_zero_iff_of_nonneg_ae
          (ae_of_all μ fun ω => sq_nonneg (X i ω)) h_int_sq).mp
          (h_each_zero i hi)
      filter_upwards [h_sq_ae] with ω hω
      exact sq_eq_zero_iff.mp hω
    have h_sum_ae : ∀ᵐ ω ∂μ, ∑ i, X i ω = 0 := by
      have : ∀ᵐ ω ∂μ, ∀ i, X i ω = 0 := by
        rw [ae_all_iff]
        intro i
        exact h_Xi_ae i (Finset.mem_univ i)
      filter_upwards [this] with ω hω
      exact Finset.sum_eq_zero fun i _ => hω i
    have h_meas_zero : μ {ω | t ≤ ∑ i, X i ω} = 0 := by
      apply measure_mono_null (t := {ω | ∑ i, X i ω ≠ 0})
      · intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        linarith
      · rw [← ae_iff]
        filter_upwards [h_sum_ae] with ω hω
        exact hω
    have h_real_zero : μ.real {ω | t ≤ ∑ i, X i ω} = 0 := by
      rw [measureReal_eq_zero_iff]
      exact h_meas_zero
    rw [h_real_zero]
    exact (Real.exp_pos _).le
  · set D := V + b * t / 3 with hD_def
    have hD_pos : 0 < D := by positivity
    set lam := t / D with hlam_def
    have hlam_pos : 0 < lam := div_pos ht hD_pos
    have hlam_lt : lam < 3 / b := by
      rw [hlam_def, div_lt_div_iff₀ hD_pos hb]
      nlinarith
    have h_S_meas : Measurable (fun ω => ∑ i, X i ω) :=
      Finset.measurable_sum Finset.univ (fun i _ => hX_meas i)
    have h_exp_int : Integrable
        (fun ω => Real.exp (lam * ∑ i, X i ω)) μ := by
      refine Integrable.of_bound
        ((h_S_meas.const_mul lam).exp.aestronglyMeasurable)
        (Real.exp (lam * Fintype.card ι * b)) ?_
      have h_ae : ∀ᵐ ω ∂μ, ∀ i, |X i ω| ≤ b := by
        rw [ae_all_iff]
        intro i
        exact h_bound i
      filter_upwards [h_ae] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h_sum_le : ∑ i, X i ω ≤ Fintype.card ι * b := by
        calc ∑ i, X i ω
            ≤ ∑ _i : ι, b :=
          Finset.sum_le_sum fun i _ => (le_abs_self _).trans (hω i)
          _ = Fintype.card ι * b := by
              rw [Finset.sum_const, Finset.card_univ]
              simp [nsmul_eq_mul]
      nlinarith
    have h_chernoff := measure_ge_le_exp_mul_mgf
      (X := fun ω => ∑ i, X i ω) t hlam_pos.le h_exp_int
    have h_mgf_factor : mgf (fun ω => ∑ i, X i ω) μ lam =
        ∏ i, mgf (X i) μ lam := by
      have := h_indep.mgf_sum hX_meas (Finset.univ : Finset ι) (t := lam)
      simp only [mgf] at this ⊢
      convert this using 2 with ω
      simp
    have h_mgf_le : ∀ i ∈ (Finset.univ : Finset ι), mgf (X i) μ lam ≤
        Real.exp (lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) /
          (2 * (1 - lam * b / 3))) := by
      intro i _
      exact bernstein_mgf_bound (hX_meas i) hb (h_bound i) (h_mean i)
        (integral_nonneg (fun ω => sq_nonneg _)) (le_refl _)
        hlam_pos hlam_lt
    have h_prod_le : ∏ i, mgf (X i) μ lam ≤
        Real.exp (lam ^ 2 * V / (2 * (1 - lam * b / 3))) := by
      set C := 2 * (1 - lam * b / 3) with hC_def
      have hlamb_lt' : lam * b < 3 := by
        calc lam * b < 3 / b * b := mul_lt_mul_of_pos_right hlam_lt hb
          _ = 3 := div_mul_cancel₀ _ hb.ne'
      have hC_pos : 0 < C := by linarith [hC_def]
      have h_step1 : ∏ i, mgf (X i) μ lam ≤
          ∏ i, Real.exp (lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) :=
        Finset.prod_le_prod (fun i _ => mgf_nonneg) h_mgf_le
      have h_step2 : ∏ i,
          Real.exp (lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) =
          Real.exp (∑ i, lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) :=
        (Real.exp_sum _ _).symm
      have h_step3 : ∑ i, lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C =
          lam ^ 2 / C * ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ := by
        rw [Finset.mul_sum]
        congr 1
        ext i
        ring
      have h_step4 : lam ^ 2 / C * ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ ≤
          lam ^ 2 * V / C := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left h_var_sum (sq_nonneg _)) hC_pos.le
      calc ∏ i, mgf (X i) μ lam
          ≤ ∏ i, Real.exp (lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) := h_step1
        _ = Real.exp (∑ i, lam ^ 2 * (∫ ω, (X i ω) ^ 2 ∂μ) / C) := h_step2
        _ = Real.exp (lam ^ 2 / C * ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) := by
            rw [h_step3]
        _ ≤ Real.exp (lam ^ 2 * V / C) := Real.exp_le_exp.mpr h_step4
        _ = Real.exp (lam ^ 2 * V / (2 * (1 - lam * b / 3))) := by
            rw [hC_def]
    calc μ.real {ω | t ≤ ∑ i, X i ω}
        ≤ Real.exp (-lam * t) * mgf (fun ω => ∑ i, X i ω) μ lam := h_chernoff
      _ = Real.exp (-lam * t) * ∏ i, mgf (X i) μ lam := by rw [h_mgf_factor]
      _ ≤ Real.exp (-lam * t) * Real.exp (lam ^ 2 * V / (2 * (1 - lam * b / 3))) := by
          gcongr
      _ = Real.exp (-lam * t + lam ^ 2 * V / (2 * (1 - lam * b / 3))) := by
          rw [← Real.exp_add]
      _ = Real.exp (-t ^ 2 / (2 * V + 2 * b * t / 3)) := by
          have h_arg :
              -lam * t + lam ^ 2 * V / (2 * (1 - lam * b / 3)) =
                -t ^ 2 / (2 * V + 2 * b * t / 3) := by
            rw [hlam_def, hD_def]
            have hD_ne : D ≠ 0 := ne_of_gt hD_pos
            have hb_ne : b ≠ 0 := ne_of_gt hb
            field_simp [hD_ne, hb_ne]
            ring_nf
          rw [h_arg]

/-! ### Bernstein specialization to the generative-model product space -/

/-- A one-sided Bernstein tail bound for the centered indicator family attached
    to a fixed transition entry `(s,a,s')` in the generative-model product
    space. -/
theorem coordinate_indicator_bernstein_upper
    {N : ℕ} (hN : 0 < N)
    (s : M.S) (a : M.A) (s' : M.S)
    {t : ℝ} (ht : 0 < t) :
    (M.generativeModelMeasure N).real
      {ω | t ≤ ∑ i : Fin N,
          (M.transitionIndicator s' (ω (s, a, i)) - M.P s a s')} ≤
      Real.exp (-t ^ 2 /
        (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) + 2 * t / 3)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let μ : Measure (M.SampleIndex N → M.S) := M.generativeModelMeasure N
  let p : ℝ := M.P s a s'
  let Y : Fin N → (M.SampleIndex N → M.S) → ℝ :=
    fun i ω => M.transitionIndicator s' (ω (s, a, i))
  let X : Fin N → (M.SampleIndex N → M.S) → ℝ :=
    fun i ω => Y i ω - p
  have hp_nonneg : 0 ≤ p := by
    simp [p, M.P_nonneg]
  have hp_le_one : p ≤ 1 := by
    calc
      p ≤ ∑ s'', M.P s a s'' := by
        simpa [p] using
          (Finset.single_le_sum (fun s'' _ => M.P_nonneg s a s'') (Finset.mem_univ s') :
            M.P s a s' ≤ ∑ s'', M.P s a s'')
      _ = 1 := M.P_sum_one s a
  have hY_meas : ∀ i, Measurable (Y i) := by
    intro i
    simpa [Y] using
      ((Measurable.of_discrete (f := M.transitionIndicator s')).comp
        (measurable_pi_apply (s, a, i)))
  have hY_bound : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ 1 := by
    intro i
    filter_upwards with ω
    have h_nonneg : 0 ≤ Y i ω := by
      simp [Y, M.transitionIndicator_nonneg]
    have h_le_one : Y i ω ≤ 1 := by
      simp [Y, M.transitionIndicator_le_one]
    rw [abs_of_nonneg h_nonneg]
    exact h_le_one
  have hY_int : ∀ i, Integrable (Y i) μ := by
    intro i
    exact Integrable.of_bound (hY_meas i).aestronglyMeasurable 1 (hY_bound i)
  have hY_sq_int : ∀ i, Integrable (fun ω => (Y i ω) ^ 2) μ := by
    intro i
    exact Integrable.of_bound ((hY_meas i).pow_const 2).aestronglyMeasurable 1 <| by
      filter_upwards [hY_bound i] with ω hω
      rw [Real.norm_eq_abs, abs_pow]
      have h_abs_nonneg : 0 ≤ |Y i ω| := abs_nonneg _
      nlinarith [hω, h_abs_nonneg]
  have h_indep_Y :
      iIndepFun Y μ := by
    simpa [μ, Y] using
      (M.sampleCoords_iIndepFun (N := N) s a).comp
        (g := fun (_ : Fin N) (x : M.S) => M.transitionIndicator s' x)
        (fun _ => Measurable.of_discrete)
  have hX_meas : ∀ i, Measurable (X i) := by
    intro i
    simpa [X] using (hY_meas i).sub measurable_const
  have h_indep_X :
      iIndepFun X μ := by
    simpa [X] using h_indep_Y.comp
      (g := fun (_ : Fin N) (x : ℝ) => x - p)
      (fun _ => measurable_id.sub measurable_const)
  have h_bound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1 := by
    intro i
    filter_upwards [hY_bound i] with ω hω
    have h_nonneg : 0 ≤ Y i ω := by
      simp [Y, M.transitionIndicator_nonneg]
    have h_le_one : Y i ω ≤ 1 := by
      simp [Y, M.transitionIndicator_le_one]
    have h_abs : |Y i ω - p| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> nlinarith [h_nonneg, h_le_one, hp_nonneg, hp_le_one]
    simpa [X] using h_abs
  have h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0 := by
    intro i
    calc
      ∫ ω, X i ω ∂μ = ∫ ω, Y i ω - p ∂μ := by rfl
      _ = ∫ ω, Y i ω ∂μ - ∫ ω, p ∂μ := by
        exact integral_sub (hY_int i) (integrable_const p)
      _ = p - p := by
        rw [show (∫ ω, Y i ω ∂μ) = p by
          simpa [μ, Y, p] using M.coordinate_indicator_expectation (N := N) s a i s']
        simp [integral_const]
      _ = 0 := by ring
  have h_var_eq : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = p - p ^ 2 := by
    intro i
    have h_expY :
        ∫ ω, Y i ω ∂μ = p := by
      simpa [μ, Y, p] using M.coordinate_indicator_expectation (N := N) s a i s'
    have h_expY2 :
        ∫ ω, (Y i ω) ^ 2 ∂μ = p := by
      calc
        ∫ ω, (Y i ω) ^ 2 ∂μ = ∫ ω, Y i ω ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          simpa [Y] using M.indicator_sq_eq s' (ω (s, a, i))
        _ = p := h_expY
    have h_expand :
        ∫ ω, (X i ω) ^ 2 ∂μ =
          (∫ ω, (Y i ω) ^ 2 ∂μ - ∫ ω, (2 * p) * Y i ω ∂μ) +
            ∫ ω, p ^ 2 ∂μ := by
      have h_sub_int : Integrable (fun ω => (Y i ω) ^ 2 - (2 * p) * Y i ω) μ :=
        (hY_sq_int i).sub ((hY_int i).const_mul (2 * p))
      calc
        ∫ ω, (X i ω) ^ 2 ∂μ
          = ∫ ω, ((Y i ω) ^ 2 - (2 * p) * Y i ω + p ^ 2) ∂μ := by
              apply integral_congr_ae
              filter_upwards with ω
              simp [X]
              ring
        _ = (∫ ω, ((Y i ω) ^ 2 - (2 * p) * Y i ω) ∂μ) + ∫ ω, p ^ 2 ∂μ := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (integral_add h_sub_int (integrable_const (p ^ 2)))
        _ = (∫ ω, (Y i ω) ^ 2 ∂μ - ∫ ω, (2 * p) * Y i ω ∂μ) +
              ∫ ω, p ^ 2 ∂μ := by
              rw [integral_sub (hY_sq_int i) ((hY_int i).const_mul (2 * p))]
    calc
      ∫ ω, (X i ω) ^ 2 ∂μ
        = (∫ ω, (Y i ω) ^ 2 ∂μ - ∫ ω, (2 * p) * Y i ω ∂μ) +
            ∫ ω, p ^ 2 ∂μ := h_expand
      _ = (p - (2 * p) * p) + p ^ 2 := by
            rw [h_expY2, integral_const_mul, h_expY]
            simp [integral_const]
      _ = p - p ^ 2 := by ring
  have hp_var_nonneg : 0 ≤ p - p ^ 2 := by
    have h_sq_nonneg : 0 ≤ (p - 1 / 2) ^ 2 := sq_nonneg _
    nlinarith
  have h_var_sum :
      ∑ i : Fin N, ∫ ω, (X i ω) ^ 2 ∂μ ≤ (N : ℝ) * (p - p ^ 2) := by
    rw [show (∑ i : Fin N, ∫ ω, (X i ω) ^ 2 ∂μ) = ∑ _i : Fin N, (p - p ^ 2) by
      apply Finset.sum_congr rfl
      intro i _
      exact h_var_eq i]
    rw [Finset.sum_const, Finset.card_univ]
    simp [nsmul_eq_mul]
  have hb : (0 : ℝ) < 1 := by positivity
  have hV : (0 : ℝ) ≤ (N : ℝ) * (p - p ^ 2) := by
    positivity
  simpa [μ, X, mul_one] using
    (bernstein_sum_fintype (μ := μ) (ι := Fin N) hX_meas h_indep_X
      (hb := hb) h_bound h_mean (hV := hV) h_var_sum ht)

/-- Bernstein upper-tail control for one empirical transition entry in the
    actual generative-model sample space. -/
theorem empirical_transition_entry_bernstein_upper
    {N : ℕ} (hN : 0 < N)
    (s : M.S) (a : M.A) (s' : M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0) :
    (M.generativeModelMeasure N).real
      {ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ≤
      Real.exp (-((N : ℝ) * eps_0) ^ 2 /
        (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
          2 * ((N : ℝ) * eps_0) / 3)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have h_main := M.coordinate_indicator_bernstein_upper hN s a s'
    (t := (N : ℝ) * eps_0) (by positivity)
  have h_subset :
      {ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ⊆
        {ω | (N : ℝ) * eps_0 ≤
            ∑ i : Fin N,
              (M.transitionIndicator s' (ω (s, a, i)) - M.P s a s')} := by
    intro ω hω
    have h_emp :
        M.empiricalTransitionRV hN ω s a s' =
          (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N := by
      simpa [empiricalTransitionRV] using
        M.empirical_as_indicator_sum hN (fun s a i => ω (s, a, i)) s a s'
    have hN_real : (0 : ℝ) < N := by
      exact_mod_cast hN
    have h1 :
        eps_0 ≤
          (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N -
            M.P s a s' := by
      simpa [h_emp] using hω
    have h1' :
        eps_0 + M.P s a s' ≤
          (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N := by
      linarith
    have h2 :
        (eps_0 + M.P s a s') * (N : ℝ) ≤
          ∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i)) := by
      rwa [le_div_iff₀ hN_real] at h1'
    have hsum :
        ∑ i : Fin N, (M.transitionIndicator s' (ω (s, a, i)) - M.P s a s') =
          ∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i)) -
            (N : ℝ) * M.P s a s' := by
      simp [Finset.sum_sub_distrib]
    have htarget :
        (N : ℝ) * eps_0 ≤
          ∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i)) -
            (N : ℝ) * M.P s a s' := by
      nlinarith
    simpa [hsum] using htarget
  have htarget_ne_top :
      (M.generativeModelMeasure N)
        {ω | (N : ℝ) * eps_0 ≤
            ∑ i : Fin N,
              (M.transitionIndicator s' (ω (s, a, i)) - M.P s a s')} ≠ ∞ := by
    have htarget_lt_top :
        (M.generativeModelMeasure N)
          {ω | (N : ℝ) * eps_0 ≤
              ∑ i : Fin N,
                (M.transitionIndicator s' (ω (s, a, i)) - M.P s a s')} < ∞ := by
      calc
        (M.generativeModelMeasure N)
            {ω | (N : ℝ) * eps_0 ≤
                ∑ i : Fin N,
                  (M.transitionIndicator s' (ω (s, a, i)) - M.P s a s')}
            ≤ (M.generativeModelMeasure N) Set.univ := measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  exact (measureReal_mono h_subset htarget_ne_top).trans h_main

/-- Bernstein lower-tail control for one empirical transition entry in the
    actual generative-model sample space. -/
theorem empirical_transition_entry_bernstein_lower
    {N : ℕ} (hN : 0 < N)
    (s : M.S) (a : M.A) (s' : M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0) :
    (M.generativeModelMeasure N).real
      {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'} ≤
      Real.exp (-((N : ℝ) * eps_0) ^ 2 /
        (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
          2 * ((N : ℝ) * eps_0) / 3)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let μ : Measure (M.SampleIndex N → M.S) := M.generativeModelMeasure N
  let p : ℝ := M.P s a s'
  let Y : Fin N → (M.SampleIndex N → M.S) → ℝ :=
    fun i ω => M.transitionIndicator s' (ω (s, a, i))
  let X : Fin N → (M.SampleIndex N → M.S) → ℝ :=
    fun i ω => p - Y i ω
  have hp_nonneg : 0 ≤ p := by
    simp [p, M.P_nonneg]
  have hp_le_one : p ≤ 1 := by
    calc
      p ≤ ∑ s'', M.P s a s'' := by
        simpa [p] using
          (Finset.single_le_sum (fun s'' _ => M.P_nonneg s a s'') (Finset.mem_univ s') :
            M.P s a s' ≤ ∑ s'', M.P s a s'')
      _ = 1 := M.P_sum_one s a
  have hY_meas : ∀ i, Measurable (Y i) := by
    intro i
    simpa [Y] using
      ((Measurable.of_discrete (f := M.transitionIndicator s')).comp
        (measurable_pi_apply (s, a, i)))
  have hY_bound : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ 1 := by
    intro i
    filter_upwards with ω
    have h_nonneg : 0 ≤ Y i ω := by
      simp [Y, M.transitionIndicator_nonneg]
    have h_le_one : Y i ω ≤ 1 := by
      simp [Y, M.transitionIndicator_le_one]
    rw [abs_of_nonneg h_nonneg]
    exact h_le_one
  have hY_int : ∀ i, Integrable (Y i) μ := by
    intro i
    exact Integrable.of_bound (hY_meas i).aestronglyMeasurable 1 (hY_bound i)
  have hY_sq_int : ∀ i, Integrable (fun ω => (Y i ω) ^ 2) μ := by
    intro i
    exact Integrable.of_bound ((hY_meas i).pow_const 2).aestronglyMeasurable 1 <| by
      filter_upwards [hY_bound i] with ω hω
      rw [Real.norm_eq_abs, abs_pow]
      have h_abs_nonneg : 0 ≤ |Y i ω| := abs_nonneg _
      nlinarith [hω, h_abs_nonneg]
  have h_indep_Y :
      iIndepFun Y μ := by
    simpa [μ, Y] using
      (M.sampleCoords_iIndepFun (N := N) s a).comp
        (g := fun (_ : Fin N) (x : M.S) => M.transitionIndicator s' x)
        (fun _ => Measurable.of_discrete)
  have hX_meas : ∀ i, Measurable (X i) := by
    intro i
    simpa [X] using measurable_const.sub (hY_meas i)
  have h_indep_X :
      iIndepFun X μ := by
    simpa [X] using h_indep_Y.comp
      (g := fun (_ : Fin N) (x : ℝ) => p - x)
      (fun _ => measurable_const.sub measurable_id)
  have h_bound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1 := by
    intro i
    filter_upwards [hY_bound i] with ω hω
    have h_nonneg : 0 ≤ Y i ω := by
      simp [Y, M.transitionIndicator_nonneg]
    have h_le_one : Y i ω ≤ 1 := by
      simp [Y, M.transitionIndicator_le_one]
    have h_abs : |p - Y i ω| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> nlinarith [h_nonneg, h_le_one, hp_nonneg, hp_le_one]
    simpa [X] using h_abs
  have h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0 := by
    intro i
    calc
      ∫ ω, X i ω ∂μ = ∫ ω, p - Y i ω ∂μ := by rfl
      _ = ∫ ω, p ∂μ - ∫ ω, Y i ω ∂μ := by
        exact integral_sub (integrable_const p) (hY_int i)
      _ = p - p := by
        rw [show (∫ ω, Y i ω ∂μ) = p by
          simpa [μ, Y, p] using M.coordinate_indicator_expectation (N := N) s a i s']
        simp [integral_const]
      _ = 0 := by ring
  have h_var_eq : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = p - p ^ 2 := by
    intro i
    have h_expY :
        ∫ ω, Y i ω ∂μ = p := by
      simpa [μ, Y, p] using M.coordinate_indicator_expectation (N := N) s a i s'
    have h_expY2 :
        ∫ ω, (Y i ω) ^ 2 ∂μ = p := by
      calc
        ∫ ω, (Y i ω) ^ 2 ∂μ = ∫ ω, Y i ω ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          simpa [Y] using M.indicator_sq_eq s' (ω (s, a, i))
        _ = p := h_expY
    have h_sub_int : Integrable (fun ω => p ^ 2 - (2 * p) * Y i ω) μ :=
      (integrable_const (p ^ 2)).sub ((hY_int i).const_mul (2 * p))
    have h_expand :
        ∫ ω, (X i ω) ^ 2 ∂μ =
          (∫ ω, p ^ 2 - (2 * p) * Y i ω ∂μ) + ∫ ω, (Y i ω) ^ 2 ∂μ := by
      calc
        ∫ ω, (X i ω) ^ 2 ∂μ
          = ∫ ω, (p ^ 2 - (2 * p) * Y i ω + (Y i ω) ^ 2) ∂μ := by
              apply integral_congr_ae
              filter_upwards with ω
              simp [X]
              ring
        _ = (∫ ω, p ^ 2 - (2 * p) * Y i ω ∂μ) + ∫ ω, (Y i ω) ^ 2 ∂μ := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (integral_add h_sub_int (hY_sq_int i))
    calc
      ∫ ω, (X i ω) ^ 2 ∂μ
        = (∫ ω, p ^ 2 - (2 * p) * Y i ω ∂μ) + ∫ ω, (Y i ω) ^ 2 ∂μ := h_expand
      _ = (p ^ 2 - (2 * p) * p) + p := by
            rw [integral_sub (integrable_const (p ^ 2)) ((hY_int i).const_mul (2 * p))]
            rw [integral_const_mul, h_expY, h_expY2]
            simp [integral_const]
      _ = p - p ^ 2 := by ring
  have hp_var_nonneg : 0 ≤ p - p ^ 2 := by
    have h_sq_nonneg : 0 ≤ (p - 1 / 2) ^ 2 := sq_nonneg _
    nlinarith
  have h_var_sum :
      ∑ i : Fin N, ∫ ω, (X i ω) ^ 2 ∂μ ≤ (N : ℝ) * (p - p ^ 2) := by
    rw [show (∑ i : Fin N, ∫ ω, (X i ω) ^ 2 ∂μ) = ∑ _i : Fin N, (p - p ^ 2) by
      apply Finset.sum_congr rfl
      intro i _
      exact h_var_eq i]
    rw [Finset.sum_const, Finset.card_univ]
    simp [nsmul_eq_mul]
  have hb : (0 : ℝ) < 1 := by positivity
  have hV : (0 : ℝ) ≤ (N : ℝ) * (p - p ^ 2) := by positivity
  have h_main := bernstein_sum_fintype (μ := μ) (ι := Fin N) hX_meas h_indep_X
    (hb := hb) h_bound h_mean (hV := hV) h_var_sum (t := (N : ℝ) * eps_0) (by positivity)
  have h_subset :
      {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'} ⊆
        {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, (p - M.transitionIndicator s' (ω (s, a, i)))} := by
    intro ω hω
    have h_emp :
        M.empiricalTransitionRV hN ω s a s' =
          (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N := by
      simpa [empiricalTransitionRV] using
        M.empirical_as_indicator_sum hN (fun s a i => ω (s, a, i)) s a s'
    have hN_real : (0 : ℝ) < N := by
      exact_mod_cast hN
    have h1 :
        eps_0 ≤
          M.P s a s' -
            (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N := by
      simpa [h_emp] using hω
    have h1' :
        eps_0 + (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N ≤
          M.P s a s' := by
      linarith
    have h2 :
        (eps_0 + (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N) * (N : ℝ) ≤
          M.P s a s' * (N : ℝ) := by
      exact mul_le_mul_of_nonneg_right h1' hN_real.le
    have hN_ne : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hN)
    have h2' :
        eps_0 * (N : ℝ) + ∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i)) ≤
          M.P s a s' * (N : ℝ) := by
      have h_expand :
          (eps_0 + (∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i))) / N) * (N : ℝ) =
            eps_0 * (N : ℝ) + ∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i)) := by
        field_simp [hN_ne]
      rwa [h_expand] at h2
    have hsum :
        ∑ i : Fin N, (p - M.transitionIndicator s' (ω (s, a, i))) =
          (N : ℝ) * p - ∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i)) := by
      simp [p, Finset.sum_sub_distrib]
    have htarget :
        (N : ℝ) * eps_0 ≤
          (N : ℝ) * p - ∑ i : Fin N, M.transitionIndicator s' (ω (s, a, i)) := by
      linarith
    simpa [hsum] using htarget
  have htarget_ne_top :
      (M.generativeModelMeasure N)
        {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, (p - M.transitionIndicator s' (ω (s, a, i)))} ≠ ∞ := by
    have htarget_lt_top :
        (M.generativeModelMeasure N)
          {ω | (N : ℝ) * eps_0 ≤
              ∑ i : Fin N, (p - M.transitionIndicator s' (ω (s, a, i)))} < ∞ := by
      calc
        (M.generativeModelMeasure N)
            {ω | (N : ℝ) * eps_0 ≤ ∑ i : Fin N, (p - M.transitionIndicator s' (ω (s, a, i)))}
            ≤ (M.generativeModelMeasure N) Set.univ := measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  exact (measureReal_mono h_subset htarget_ne_top).trans <| by
    simpa [μ, X, p] using h_main

/-- Two-sided Bernstein control for one empirical transition entry in the
    generative-model sample space. -/
theorem empirical_transition_entry_bernstein_concentration
    {N : ℕ} (hN : 0 < N)
    (s : M.S) (a : M.A) (s' : M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0) :
    (M.generativeModelMeasure N).real
      {ω | eps_0 ≤ |M.P s a s' - M.empiricalTransitionRV hN ω s a s'|} ≤
      2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
        (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
          2 * ((N : ℝ) * eps_0) / 3)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have h_upper :
      (M.generativeModelMeasure N).real
        {ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ≤
      Real.exp (-((N : ℝ) * eps_0) ^ 2 /
        (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
          2 * ((N : ℝ) * eps_0) / 3)) :=
    M.empirical_transition_entry_bernstein_upper hN s a s' eps_0 heps_0
  have h_lower :
      (M.generativeModelMeasure N).real
        {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'} ≤
      Real.exp (-((N : ℝ) * eps_0) ^ 2 /
        (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
          2 * ((N : ℝ) * eps_0) / 3)) :=
    M.empirical_transition_entry_bernstein_lower hN s a s' eps_0 heps_0
  have h_abs_subset :
      {ω | eps_0 ≤ |M.P s a s' - M.empiricalTransitionRV hN ω s a s'|} ⊆
        {ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ∪
        {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'} := by
    intro ω hω
    have hω' : eps_0 ≤ |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| := hω
    by_cases hsign : 0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'
    · have hcase : eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s' := by
        rwa [abs_of_nonneg hsign] at hω'
      exact Or.inr hcase
    · have hcase : eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s' := by
        rw [abs_of_neg (by linarith)] at hω'
        linarith
      exact Or.inl hcase
  have h_union_ne_top :
      (M.generativeModelMeasure N)
        ({ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ∪
          {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'}) ≠ ∞ := by
    have h_union_lt_top :
        (M.generativeModelMeasure N)
          ({ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ∪
            {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'}) < ∞ := by
      calc
        (M.generativeModelMeasure N)
            ({ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ∪
              {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'})
            ≤ (M.generativeModelMeasure N) Set.univ := measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt h_union_lt_top
  calc
    (M.generativeModelMeasure N).real
        {ω | eps_0 ≤ |M.P s a s' - M.empiricalTransitionRV hN ω s a s'|}
      ≤ (M.generativeModelMeasure N).real
          ({ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} ∪
            {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'}) :=
          measureReal_mono h_abs_subset h_union_ne_top
    _ ≤ (M.generativeModelMeasure N).real
          {ω | eps_0 ≤ M.empiricalTransitionRV hN ω s a s' - M.P s a s'} +
        (M.generativeModelMeasure N).real
          {ω | eps_0 ≤ M.P s a s' - M.empiricalTransitionRV hN ω s a s'} :=
          measureReal_union_le _ _
    _ ≤ Real.exp (-((N : ℝ) * eps_0) ^ 2 /
          (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
            2 * ((N : ℝ) * eps_0) / 3)) +
        Real.exp (-((N : ℝ) * eps_0) ^ 2 /
          (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
            2 * ((N : ℝ) * eps_0) / 3)) := by
          gcongr
    _ = 2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
          (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
            2 * ((N : ℝ) * eps_0) / 3)) := by
          ring

/-- Full PAC bound for the generative model using the Bernstein per-entry
    concentration bound specialized to the actual transition coordinates. -/
theorem generative_model_pac_bernstein
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s a s',
        |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| < eps_0} ≥
      1 - ∑ p : M.S × M.A × M.S,
        2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
          (2 * ((N : ℝ) * (M.P p.1 p.2.1 p.2.2 - (M.P p.1 p.2.1 p.2.2) ^ 2)) +
            2 * ((N : ℝ) * eps_0) / 3)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have h_meas_good :
      MeasurableSet
        {ω | ∀ s a s',
          |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| < eps_0} := by
    classical
    let goodEntry : M.S × M.A × M.S → Set (M.SampleIndex N → M.S) :=
      fun p => {ω |
        |M.P p.1 p.2.1 p.2.2 - M.empiricalTransitionRV hN ω p.1 p.2.1 p.2.2| < eps_0}
    have h_entry : ∀ p, MeasurableSet (goodEntry p) := by
      intro p
      exact measurableSet_lt
        (measurable_const.sub
          (M.empiricalTransitionRV_measurable hN p.1 p.2.1 p.2.2)).abs
        measurable_const
    have h_eq :
        {ω | ∀ s a s',
          |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| < eps_0} =
        ⋂ p : M.S × M.A × M.S, goodEntry p := by
      ext ω
      simp [goodEntry]
    rw [h_eq]
    exact MeasurableSet.iInter fun p : M.S × M.A × M.S => h_entry p
  set good : Set (M.SampleIndex N → M.S) := {ω | ∀ s a s',
    |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| < eps_0}
  have h_add :
      (M.generativeModelMeasure N).real good +
        (M.generativeModelMeasure N).real goodᶜ =
      (M.generativeModelMeasure N).real Set.univ :=
    measureReal_add_measureReal_compl h_meas_good
  have h_univ : (M.generativeModelMeasure N).real Set.univ = 1 := probReal_univ
  have h_ub :
      (M.generativeModelMeasure N).real goodᶜ ≤
        ∑ p : M.S × M.A × M.S,
          2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
            (2 * ((N : ℝ) * (M.P p.1 p.2.1 p.2.2 - (M.P p.1 p.2.1 p.2.2) ^ 2)) +
              2 * ((N : ℝ) * eps_0) / 3)) := by
    have h_subset : goodᶜ ⊆ ⋃ (p : M.S × M.A × M.S),
        {ω | eps_0 ≤ |M.P p.1 p.2.1 p.2.2 -
          M.empiricalTransitionRV hN ω p.1 p.2.1 p.2.2|} := by
      intro ω hω
      simp only [good, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hω
      obtain ⟨s, a, s', h⟩ := hω
      exact Set.mem_iUnion.mpr ⟨(s, a, s'), h⟩
    calc
      (M.generativeModelMeasure N).real goodᶜ
          ≤ (M.generativeModelMeasure N).real (⋃ (p : M.S × M.A × M.S),
              {ω | eps_0 ≤ |M.P p.1 p.2.1 p.2.2 -
                M.empiricalTransitionRV hN ω p.1 p.2.1 p.2.2|}) :=
            measureReal_mono h_subset
      _ ≤ ∑ p : M.S × M.A × M.S, (M.generativeModelMeasure N).real
            {ω | eps_0 ≤ |M.P p.1 p.2.1 p.2.2 -
              M.empiricalTransitionRV hN ω p.1 p.2.1 p.2.2|} :=
            measureReal_iUnion_fintype_le _
      _ ≤ ∑ p : M.S × M.A × M.S,
            2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
              (2 * ((N : ℝ) * (M.P p.1 p.2.1 p.2.2 - (M.P p.1 p.2.1 p.2.2) ^ 2)) +
                2 * ((N : ℝ) * eps_0) / 3)) := by
              exact Finset.sum_le_sum fun p _ =>
                M.empirical_transition_entry_bernstein_concentration
                  hN p.1 p.2.1 p.2.2 eps_0 heps_0
  linarith

/-! ### Step 9: End-to-end minimax theorem -/

/-- **Minimax sample complexity from generative model (end-to-end).**

    On the good event {forall s a s', |P_hat - P| < eps_0}:

    1. L1 error: sum_{s'} |P_hat - P| <= |S| * eps_0
    2. Deterministic core: V-gap <= 2*gamma*R_max*|S|*eps_0 / (1-gamma)^2

    The probabilistic layer (Steps 1-8) gives the good event with
    high probability. This theorem chains the deterministic steps. -/
theorem minimax_from_generative_model
    (P_hat_omega : M.S → M.A → M.S → ℝ)
    (hP_hat_nonneg : ∀ s a s', 0 ≤ P_hat_omega s a s')
    (hP_hat_sum : ∀ s a, ∑ s', P_hat_omega s a s' = 1)
    (eps_0 : ℝ) (_heps_0 : 0 < eps_0)
    (h_good : ∀ s a s', |M.P s a s' - P_hat_omega s a s'| < eps_0)
    (r_hat : M.S → M.A → ℝ)
    (h_same_r : ∀ s a, M.r s a = r_hat s a)
    (pi_ref pi_hat : M.StochasticPolicy)
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref pi_ref)
    (hV_hat_M : M.isValueOf V_hat_M pi_hat)
    (V_ref_a V_hat_a : M.StateValueFn)
    (hV_ref_a : ∀ s, V_ref_a s =
      (∑ a, pi_ref.prob s a * r_hat s a) +
      M.γ * (∑ a, pi_ref.prob s a *
        ∑ s', P_hat_omega s a s' * V_ref_a s'))
    (hV_hat_a : ∀ s, V_hat_a s =
      (∑ a, pi_hat.prob s a * r_hat s a) +
      M.γ * (∑ a, pi_hat.prob s a *
        ∑ s', P_hat_omega s a s' * V_hat_a s'))
    (h_opt : ∀ s, V_hat_a s ≥ V_ref_a s) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2 := by
  -- Construct the approximate MDP
  set M_hat : M.ApproxMDP := {
    P_hat := P_hat_omega
    r_hat := r_hat
    P_hat_nonneg := hP_hat_nonneg
    P_hat_sum_one := hP_hat_sum
  }
  -- L1 error from pointwise bound
  have h_l1 : M.transitionError M_hat ≤ ↑(Fintype.card M.S) * eps_0 := by
    simp only [transitionError]
    apply Finset.sup'_le; intro s _
    apply Finset.sup'_le; intro a _
    calc ∑ s', |M.P s a s' - P_hat_omega s a s'|
        ≤ ∑ _s' : M.S, eps_0 :=
          Finset.sum_le_sum fun s' _ => le_of_lt (h_good s a s')
      _ = Fintype.card M.S * eps_0 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact M.minimax_deterministic_core M_hat pi_ref pi_hat
    V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a
    h_opt h_same_r (↑(Fintype.card M.S) * eps_0) h_l1

/-- Specialization of `minimax_from_generative_model` to the empirical transition
    kernel extracted from a generative-model sample point. -/
theorem minimax_from_empirical_transition_good_event
    {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (h_good : ∀ s a s', |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| < eps_0)
    (r_hat : M.S → M.A → ℝ)
    (h_same_r : ∀ s a, M.r s a = r_hat s a)
    (pi_ref pi_hat : M.StochasticPolicy)
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref pi_ref)
    (hV_hat_M : M.isValueOf V_hat_M pi_hat)
    (V_ref_a V_hat_a : M.StateValueFn)
    (hV_ref_a : ∀ s, V_ref_a s =
      (∑ a, pi_ref.prob s a * r_hat s a) +
      M.γ * (∑ a, pi_ref.prob s a *
        ∑ s', M.empiricalTransitionRV hN ω s a s' * V_ref_a s'))
    (hV_hat_a : ∀ s, V_hat_a s =
      (∑ a, pi_hat.prob s a * r_hat s a) +
      M.γ * (∑ a, pi_hat.prob s a *
        ∑ s', M.empiricalTransitionRV hN ω s a s' * V_hat_a s'))
    (h_opt : ∀ s, V_hat_a s ≥ V_ref_a s) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2 := by
  exact M.minimax_from_generative_model (M.empiricalTransitionRV hN ω)
    (M.empiricalTransitionRV_nonneg hN ω)
    (M.empiricalTransitionRV_sum_one hN ω)
    eps_0 heps_0 h_good
    r_hat h_same_r pi_ref pi_hat V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a h_opt

/-- Same as `minimax_from_empirical_transition_good_event`, but stated for the
    canonical empirical approximate MDP that keeps the true reward function. -/
theorem minimax_from_empirical_model_good_event
    {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (h_good : ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0)
    (pi_ref pi_hat : M.StochasticPolicy)
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref pi_ref)
    (hV_hat_M : M.isValueOf V_hat_M pi_hat)
    (V_ref_a V_hat_a : M.StateValueFn)
    (hV_ref_a : ∀ s, V_ref_a s =
      (∑ a, pi_ref.prob s a * (M.empiricalApproxMDPRV hN ω).r_hat s a) +
      M.γ * (∑ a, pi_ref.prob s a *
        ∑ s', (M.empiricalApproxMDPRV hN ω).P_hat s a s' * V_ref_a s'))
    (hV_hat_a : ∀ s, V_hat_a s =
      (∑ a, pi_hat.prob s a * (M.empiricalApproxMDPRV hN ω).r_hat s a) +
      M.γ * (∑ a, pi_hat.prob s a *
        ∑ s', (M.empiricalApproxMDPRV hN ω).P_hat s a s' * V_hat_a s'))
    (h_opt : ∀ s, V_hat_a s ≥ V_ref_a s) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2 := by
  exact M.minimax_from_generative_model ((M.empiricalApproxMDPRV hN ω).P_hat)
    ((M.empiricalApproxMDPRV hN ω).P_hat_nonneg)
    ((M.empiricalApproxMDPRV hN ω).P_hat_sum_one)
    eps_0 heps_0 h_good
    M.r (fun s a => rfl) pi_ref pi_hat V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a h_opt

/-- Reduce the empirical-model optimality side to a Bellman fixed point of the
    empirical MDP. This removes the free approximate greedy-policy/value and
    dominance hypotheses from `minimax_from_empirical_model_good_event`. -/
theorem minimax_from_empirical_bellman_fixed_point_good_event
    {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (h_good : ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0)
    (π_ref : M.StochasticPolicy)
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref π_ref)
    (V_ref_a : M.StateValueFn)
    (hV_ref_a :
      (M.empiricalModelMDP hN ω).isValueOf V_ref_a
        (M.toEmpiricalModelPolicy hN ω π_ref))
    (Q_hat : (M.empiricalModelMDP hN ω).ActionValueFn)
    (hQ_hat : ∀ s a, Q_hat s a =
      (M.empiricalModelMDP hN ω).bellmanOptOp Q_hat s a)
    (hV_hat_M :
      M.isValueOf V_hat_M
        (M.ofEmpiricalModelPolicy hN ω
          ((M.empiricalModelMDP hN ω).greedyStochasticPolicy Q_hat))) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2 := by
  let Mω := M.empiricalModelMDP hN ω
  let π_hat_emp : Mω.StochasticPolicy := Mω.greedyStochasticPolicy Q_hat
  let V_hat_a : Mω.StateValueFn :=
    fun s => Finset.univ.sup' Finset.univ_nonempty (Q_hat s)
  have h_opt_exists := Mω.optimal_policy_exists Q_hat hQ_hat
  have hV_hat_a_emp : Mω.isValueOf V_hat_a π_hat_emp := by
    exact h_opt_exists.1
  have h_dom :
      ∀ (π : Mω.StochasticPolicy) (V_pi : Mω.StateValueFn),
        Mω.isValueOf V_pi π → ∀ s, V_pi s ≤ V_hat_a s := by
    exact h_opt_exists.2
  have hV_ref_a_rw :
      ∀ s, V_ref_a s =
        (∑ a, π_ref.prob s a * (M.empiricalApproxMDPRV hN ω).r_hat s a) +
        M.γ * (∑ a, π_ref.prob s a *
          ∑ s', (M.empiricalApproxMDPRV hN ω).P_hat s a s' * V_ref_a s') := by
    simpa [Mω, empiricalModelMDP, toEmpiricalModelPolicy, empiricalApproxMDPRV,
      FiniteMDP.isValueOf, FiniteMDP.expectedReward, FiniteMDP.expectedNextValue]
      using hV_ref_a
  have hV_hat_a_rw :
      ∀ s, V_hat_a s =
        (∑ a, (M.ofEmpiricalModelPolicy hN ω π_hat_emp).prob s a *
          (M.empiricalApproxMDPRV hN ω).r_hat s a) +
        M.γ * (∑ a, (M.ofEmpiricalModelPolicy hN ω π_hat_emp).prob s a *
          ∑ s', (M.empiricalApproxMDPRV hN ω).P_hat s a s' * V_hat_a s') := by
    simpa [Mω, empiricalModelMDP, ofEmpiricalModelPolicy, empiricalApproxMDPRV,
      π_hat_emp, V_hat_a, FiniteMDP.isValueOf, FiniteMDP.expectedReward,
      FiniteMDP.expectedNextValue] using hV_hat_a_emp
  have h_opt :
      ∀ s, V_hat_a s ≥ V_ref_a s := by
    intro s
    exact h_dom (M.toEmpiricalModelPolicy hN ω π_ref) V_ref_a hV_ref_a s
  exact M.minimax_from_empirical_model_good_event hN ω eps_0 heps_0 h_good
    π_ref (M.ofEmpiricalModelPolicy hN ω π_hat_emp) V_ref V_hat_M hV_ref
    hV_hat_M V_ref_a V_hat_a hV_ref_a_rw hV_hat_a_rw h_opt

/-- Further reduce the empirical-model good-event theorem by deriving the
    reference-side empirical value from an empirical action-value fixed point
    for the reference policy. -/
theorem minimax_from_empirical_Q_fixed_points_good_event
    {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (h_good : ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0)
    (π_ref : M.StochasticPolicy)
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref π_ref)
    (Q_ref : (M.empiricalModelMDP hN ω).ActionValueFn)
    (hQ_ref :
      (M.empiricalModelMDP hN ω).isActionValueOf Q_ref
        (M.toEmpiricalModelPolicy hN ω π_ref))
    (Q_hat : (M.empiricalModelMDP hN ω).ActionValueFn)
    (hQ_hat : ∀ s a, Q_hat s a =
      (M.empiricalModelMDP hN ω).bellmanOptOp Q_hat s a)
    (hV_hat_M :
      M.isValueOf V_hat_M
        (M.ofEmpiricalModelPolicy hN ω
          ((M.empiricalModelMDP hN ω).greedyStochasticPolicy Q_hat))) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2 := by
  let V_ref_a := M.empiricalModelValueFromQ hN ω π_ref Q_ref
  have hV_ref_a :
      (M.empiricalModelMDP hN ω).isValueOf V_ref_a
        (M.toEmpiricalModelPolicy hN ω π_ref) := by
    exact M.empiricalModelValueFromQ_isValueOf hN ω π_ref Q_ref hQ_ref
  exact M.minimax_from_empirical_bellman_fixed_point_good_event hN ω eps_0 heps_0
    h_good π_ref V_ref V_hat_M hV_ref V_ref_a hV_ref_a Q_hat hQ_hat hV_hat_M

/-- Further reduce the empirical-model good-event theorem by constructing the
    reference-side empirical action-value fixed point via the Banach
    fixed-point bridge, leaving only the empirical Bellman-optimal fixed point
    on the greedy side as an explicit hypothesis. -/
theorem minimax_from_empirical_eval_and_bellman_fixed_points_good_event
    {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (h_good : ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0)
    (π_ref : M.StochasticPolicy)
    (V_ref V_hat_M : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref π_ref)
    (Q_hat : (M.empiricalModelMDP hN ω).ActionValueFn)
    (hQ_hat : ∀ s a, Q_hat s a =
      (M.empiricalModelMDP hN ω).bellmanOptOp Q_hat s a)
    (hV_hat_M :
      M.isValueOf V_hat_M
        (M.ofEmpiricalModelPolicy hN ω
          ((M.empiricalModelMDP hN ω).greedyStochasticPolicy Q_hat))) :
    ∀ s, V_ref s - V_hat_M s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2 := by
  let Mω := M.empiricalModelMDP hN ω
  let π_ref_emp : Mω.StochasticPolicy := M.toEmpiricalModelPolicy hN ω π_ref
  let Q_ref : Mω.ActionValueFn := Mω.actionValueFixedPoint π_ref_emp
  have hQ_ref : Mω.isActionValueOf Q_ref π_ref_emp := by
    exact Mω.actionValueFixedPoint_isActionValueOf π_ref_emp
  exact M.minimax_from_empirical_Q_fixed_points_good_event hN ω eps_0 heps_0
    h_good π_ref V_ref V_hat_M hV_ref Q_ref hQ_ref Q_hat hQ_hat hV_hat_M

/-- Further reduce the empirical-model good-event theorem by replacing the
    free Bellman-optimal empirical witness with the canonical Banach fixed point
    of the empirical optimality operator. The remaining output-side object is
    the true-model value of the resulting empirical greedy policy. -/
theorem minimax_from_empirical_fixed_points_good_event
    {N : ℕ} (hN : 0 < N)
    (ω : M.SampleIndex N → M.S)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (h_good : ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0)
    (π_ref : M.StochasticPolicy)
    (V_ref : M.StateValueFn)
    (hV_ref : M.isValueOf V_ref π_ref) :
    ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2 := by
  let Mω := M.empiricalModelMDP hN ω
  let Q_hat : Mω.ActionValueFn := Mω.optimalQFixedPoint
  have hQ_hat : ∀ s a, Q_hat s a = Mω.bellmanOptOp Q_hat s a := by
    intro s a
    simpa [Q_hat, FiniteMDP.isBellmanOptimalQ, FiniteMDP.bellmanOptOp] using
      (Mω.optimalQFixedPoint_isBellmanOptimalQ s a)
  have hV_hat_M :
      M.isValueOf (M.empiricalGreedyValue hN ω) (M.empiricalGreedyPolicy hN ω) := by
    exact M.empiricalGreedyValue_isValueOf hN ω
  exact M.minimax_from_empirical_eval_and_bellman_fixed_points_good_event
    hN ω eps_0 heps_0 h_good π_ref V_ref (M.empiricalGreedyValue hN ω)
    hV_ref Q_hat hQ_hat hV_hat_M

/-- **High-probability minimax value-gap bound for the empirical transition model.**

    This packages the exact PAC event from `generative_model_pac` with the
    deterministic good-event reduction from
    `minimax_from_empirical_transition_good_event`.

    The approximate-model policies and value functions may depend on the sample
    point `ω`; the theorem only assumes that, for each `ω`, they satisfy the
    stated Bellman/value hypotheses for the empirical kernel extracted from `ω`.
    This keeps the theorem honest: it is an end-to-end probability statement for
    the empirical model, but it still does not derive those approximate-model
    objects from the data. -/
theorem minimax_value_gap_high_probability
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (r_hat : M.S → M.A → ℝ)
    (h_same_r : ∀ s a, M.r s a = r_hat s a)
    (pi_ref pi_hat : (M.SampleIndex N → M.S) → M.StochasticPolicy)
    (V_ref V_hat_M : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref : ∀ ω, M.isValueOf (V_ref ω) (pi_ref ω))
    (hV_hat_M : ∀ ω, M.isValueOf (V_hat_M ω) (pi_hat ω))
    (V_ref_a V_hat_a : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref_a : ∀ ω s, V_ref_a ω s =
      (∑ a, (pi_ref ω).prob s a * r_hat s a) +
      M.γ * (∑ a, (pi_ref ω).prob s a *
        ∑ s', M.empiricalTransitionRV hN ω s a s' * V_ref_a ω s'))
    (hV_hat_a : ∀ ω s, V_hat_a ω s =
      (∑ a, (pi_hat ω).prob s a * r_hat s a) +
      M.γ * (∑ a, (pi_hat ω).prob s a *
        ∑ s', M.empiricalTransitionRV hN ω s a s' * V_hat_a ω s'))
    (h_opt : ∀ ω s, V_hat_a ω s ≥ V_ref_a ω s) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
          (1 - M.γ) ^ 2} ≥
      1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let good : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s a s', |M.P s a s' - M.empiricalTransitionRV hN ω s a s'| < eps_0}
  let target : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2}
  have h_subset : good ⊆ target := by
    intro ω hω
    dsimp [good, target] at hω ⊢
    exact M.minimax_from_empirical_transition_good_event hN ω eps_0 heps_0
      hω r_hat h_same_r (pi_ref ω) (pi_hat ω) (V_ref ω) (V_hat_M ω)
      (hV_ref ω) (hV_hat_M ω) (V_ref_a ω) (V_hat_a ω)
      (hV_ref_a ω) (hV_hat_a ω) (h_opt ω)
  have h_pac := M.generative_model_pac hN eps_0 heps_0
  have htarget_ne_top : (M.generativeModelMeasure N) target ≠ ∞ := by
    have htarget_lt_top : (M.generativeModelMeasure N) target < ∞ := by
      calc
        (M.generativeModelMeasure N) target ≤ (M.generativeModelMeasure N) Set.univ :=
          measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  calc
    1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2))
      ≤ (M.generativeModelMeasure N).real good := by
        simpa [good] using h_pac
    _ ≤ (M.generativeModelMeasure N).real target :=
        measureReal_mono h_subset htarget_ne_top
    _ = (M.generativeModelMeasure N).real
          {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
            2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
              (1 - M.γ) ^ 2} := by
        rfl

/-- High-probability value-gap bound stated for the canonical empirical
    approximate MDP that keeps the true reward function. -/
theorem minimax_value_gap_high_probability_same_reward
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (pi_ref pi_hat : (M.SampleIndex N → M.S) → M.StochasticPolicy)
    (V_ref V_hat_M : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref : ∀ ω, M.isValueOf (V_ref ω) (pi_ref ω))
    (hV_hat_M : ∀ ω, M.isValueOf (V_hat_M ω) (pi_hat ω))
    (V_ref_a V_hat_a : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref_a : ∀ ω s, V_ref_a ω s =
      (∑ a, (pi_ref ω).prob s a * (M.empiricalApproxMDPRV hN ω).r_hat s a) +
      M.γ * (∑ a, (pi_ref ω).prob s a *
        ∑ s', (M.empiricalApproxMDPRV hN ω).P_hat s a s' * V_ref_a ω s'))
    (hV_hat_a : ∀ ω s, V_hat_a ω s =
      (∑ a, (pi_hat ω).prob s a * (M.empiricalApproxMDPRV hN ω).r_hat s a) +
      M.γ * (∑ a, (pi_hat ω).prob s a *
        ∑ s', (M.empiricalApproxMDPRV hN ω).P_hat s a s' * V_hat_a ω s'))
    (h_opt : ∀ ω s, V_hat_a ω s ≥ V_ref_a ω s) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
          (1 - M.γ) ^ 2} ≥
      1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2)) := by
  exact M.minimax_value_gap_high_probability hN eps_0 heps_0
    M.r (fun s a => rfl) pi_ref pi_hat V_ref V_hat_M hV_ref hV_hat_M
    V_ref_a V_hat_a hV_ref_a hV_hat_a h_opt

/-- High-probability value-gap bound where the empirical greedy policy/value
    side is derived from a Bellman fixed point of the canonical empirical model. -/
theorem minimax_value_gap_high_probability_from_empirical_bellman_fixed_point
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (pi_ref : (M.SampleIndex N → M.S) → M.StochasticPolicy)
    (V_ref V_hat_M : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref : ∀ ω, M.isValueOf (V_ref ω) (pi_ref ω))
    (V_ref_a : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref_a : ∀ ω,
      (M.empiricalModelMDP hN ω).isValueOf (V_ref_a ω)
        (M.toEmpiricalModelPolicy hN ω (pi_ref ω)))
    (Q_hat : (M.SampleIndex N → M.S) → M.ActionValueFn)
    (hQ_hat : ∀ ω s a, Q_hat ω s a =
      (M.empiricalModelMDP hN ω).bellmanOptOp (Q_hat ω) s a)
    (hV_hat_M : ∀ ω,
      M.isValueOf (V_hat_M ω)
        (M.ofEmpiricalModelPolicy hN ω
          ((M.empiricalModelMDP hN ω).greedyStochasticPolicy (Q_hat ω)))) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
          (1 - M.γ) ^ 2} ≥
      1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let good : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0}
  let target : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2}
  have h_subset : good ⊆ target := by
    intro ω hω
    dsimp [good, target] at hω ⊢
    exact M.minimax_from_empirical_bellman_fixed_point_good_event hN ω eps_0 heps_0
      hω (pi_ref ω) (V_ref ω) (V_hat_M ω) (hV_ref ω) (V_ref_a ω)
      (hV_ref_a ω) (Q_hat ω) (hQ_hat ω) (hV_hat_M ω)
  have h_pac := M.generative_model_pac hN eps_0 heps_0
  have htarget_ne_top : (M.generativeModelMeasure N) target ≠ ∞ := by
    have htarget_lt_top : (M.generativeModelMeasure N) target < ∞ := by
      calc
        (M.generativeModelMeasure N) target ≤ (M.generativeModelMeasure N) Set.univ :=
          measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  calc
    1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2))
      ≤ (M.generativeModelMeasure N).real good := by
        simpa [good] using h_pac
    _ ≤ (M.generativeModelMeasure N).real target :=
        measureReal_mono h_subset htarget_ne_top
    _ = (M.generativeModelMeasure N).real
          {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
            2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
              (1 - M.γ) ^ 2} := by
        rfl

/-- High-probability value-gap bound where the reference-side empirical value is
    derived from an empirical action-value fixed point and the empirical greedy
    side is derived from an empirical Bellman fixed point. -/
theorem minimax_value_gap_high_probability_from_empirical_Q_fixed_points
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (pi_ref : (M.SampleIndex N → M.S) → M.StochasticPolicy)
    (V_ref V_hat_M : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref : ∀ ω, M.isValueOf (V_ref ω) (pi_ref ω))
    (Q_ref : (M.SampleIndex N → M.S) → M.ActionValueFn)
    (hQ_ref : ∀ ω,
      (M.empiricalModelMDP hN ω).isActionValueOf (Q_ref ω)
        (M.toEmpiricalModelPolicy hN ω (pi_ref ω)))
    (Q_hat : (M.SampleIndex N → M.S) → M.ActionValueFn)
    (hQ_hat : ∀ ω s a, Q_hat ω s a =
      (M.empiricalModelMDP hN ω).bellmanOptOp (Q_hat ω) s a)
    (hV_hat_M : ∀ ω,
      M.isValueOf (V_hat_M ω)
        (M.ofEmpiricalModelPolicy hN ω
          ((M.empiricalModelMDP hN ω).greedyStochasticPolicy (Q_hat ω)))) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
          (1 - M.γ) ^ 2} ≥
      1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let good : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0}
  let target : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2}
  have h_subset : good ⊆ target := by
    intro ω hω
    dsimp [good, target] at hω ⊢
    exact M.minimax_from_empirical_Q_fixed_points_good_event hN ω eps_0 heps_0
      hω (pi_ref ω) (V_ref ω) (V_hat_M ω) (hV_ref ω)
      (Q_ref ω) (hQ_ref ω) (Q_hat ω) (hQ_hat ω) (hV_hat_M ω)
  have h_pac := M.generative_model_pac hN eps_0 heps_0
  have htarget_ne_top : (M.generativeModelMeasure N) target ≠ ∞ := by
    have htarget_lt_top : (M.generativeModelMeasure N) target < ∞ := by
      calc
        (M.generativeModelMeasure N) target ≤ (M.generativeModelMeasure N) Set.univ :=
          measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  calc
    1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2))
      ≤ (M.generativeModelMeasure N).real good := by
        simpa [good] using h_pac
    _ ≤ (M.generativeModelMeasure N).real target :=
        measureReal_mono h_subset htarget_ne_top
    _ = (M.generativeModelMeasure N).real
          {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
            2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
              (1 - M.γ) ^ 2} := by
        rfl

/-- High-probability value-gap bound where the reference-side empirical action
    value is constructed canonically from the empirical model and the
    reference policy, leaving only the empirical Bellman-optimal fixed point as
    an explicit greedy-side hypothesis. -/
theorem minimax_value_gap_high_probability_from_empirical_eval_and_bellman_fixed_point
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (pi_ref : (M.SampleIndex N → M.S) → M.StochasticPolicy)
    (V_ref V_hat_M : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref : ∀ ω, M.isValueOf (V_ref ω) (pi_ref ω))
    (Q_hat : (M.SampleIndex N → M.S) → M.ActionValueFn)
    (hQ_hat : ∀ ω s a, Q_hat ω s a =
      (M.empiricalModelMDP hN ω).bellmanOptOp (Q_hat ω) s a)
    (hV_hat_M : ∀ ω,
      M.isValueOf (V_hat_M ω)
        (M.ofEmpiricalModelPolicy hN ω
          ((M.empiricalModelMDP hN ω).greedyStochasticPolicy (Q_hat ω)))) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
          (1 - M.γ) ^ 2} ≥
      1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let good : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0}
  let target : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2}
  have h_subset : good ⊆ target := by
    intro ω hω
    dsimp [good, target] at hω ⊢
    exact M.minimax_from_empirical_eval_and_bellman_fixed_points_good_event
      hN ω eps_0 heps_0 hω (pi_ref ω) (V_ref ω) (V_hat_M ω)
      (hV_ref ω) (Q_hat ω) (hQ_hat ω) (hV_hat_M ω)
  have h_pac := M.generative_model_pac hN eps_0 heps_0
  have htarget_ne_top : (M.generativeModelMeasure N) target ≠ ∞ := by
    have htarget_lt_top : (M.generativeModelMeasure N) target < ∞ := by
      calc
        (M.generativeModelMeasure N) target ≤ (M.generativeModelMeasure N) Set.univ :=
          measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  calc
    1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2))
      ≤ (M.generativeModelMeasure N).real good := by
        simpa [good] using h_pac
    _ ≤ (M.generativeModelMeasure N).real target :=
        measureReal_mono h_subset htarget_ne_top
    _ = (M.generativeModelMeasure N).real
          {ω | ∀ s, V_ref ω s - V_hat_M ω s ≤
            2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
              (1 - M.γ) ^ 2} := by
        rfl

/-- High-probability value-gap bound where both empirical-model fixed points
    are canonical: the reference-side value is built from Banach policy
    evaluation in the empirical model, and the greedy side uses the canonical
    Bellman-optimal empirical fixed point together with canonical policy
    evaluation back in the true MDP. -/
theorem minimax_value_gap_high_probability_from_empirical_fixed_points
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (pi_ref : (M.SampleIndex N → M.S) → M.StochasticPolicy)
    (V_ref : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref : ∀ ω, M.isValueOf (V_ref ω) (pi_ref ω)) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref ω s - M.empiricalGreedyValue hN ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
          (1 - M.γ) ^ 2} ≥
      1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let good : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0}
  let target : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s, V_ref ω s - M.empiricalGreedyValue hN ω s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2}
  have h_subset : good ⊆ target := by
    intro ω hω
    dsimp [good, target] at hω ⊢
    exact M.minimax_from_empirical_fixed_points_good_event
      hN ω eps_0 heps_0 hω (pi_ref ω) (V_ref ω) (hV_ref ω)
  have h_pac := M.generative_model_pac hN eps_0 heps_0
  have htarget_ne_top : (M.generativeModelMeasure N) target ≠ ∞ := by
    have htarget_lt_top : (M.generativeModelMeasure N) target < ∞ := by
      calc
        (M.generativeModelMeasure N) target ≤ (M.generativeModelMeasure N) Set.univ :=
          measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  calc
    1 - Fintype.card M.S * Fintype.card M.S *
        Fintype.card M.A * (2 * Real.exp (-2 * (N : ℝ) * eps_0 ^ 2))
      ≤ (M.generativeModelMeasure N).real good := by
        simpa [good] using h_pac
    _ ≤ (M.generativeModelMeasure N).real target :=
        measureReal_mono h_subset htarget_ne_top
    _ = (M.generativeModelMeasure N).real
          {ω | ∀ s, V_ref ω s - M.empiricalGreedyValue hN ω s ≤
            2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
              (1 - M.γ) ^ 2} := by
        rfl

/-- Bernstein-flavored high-probability value-gap bound where both
    empirical-model fixed points are canonical. The probabilistic layer now
    comes from the in-file Bernstein specialization with the exact Bernoulli
    variance profile for each transition entry. -/
theorem minimax_value_gap_high_probability_from_empirical_fixed_points_bernstein
    {N : ℕ} (hN : 0 < N)
    (eps_0 : ℝ) (heps_0 : 0 < eps_0)
    (pi_ref : (M.SampleIndex N → M.S) → M.StochasticPolicy)
    (V_ref : (M.SampleIndex N → M.S) → M.StateValueFn)
    (hV_ref : ∀ ω, M.isValueOf (V_ref ω) (pi_ref ω)) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref ω s - M.empiricalGreedyValue hN ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
          (1 - M.γ) ^ 2} ≥
      1 - ∑ p : M.S × M.A × M.S,
        2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
          (2 * ((N : ℝ) * (M.P p.1 p.2.1 p.2.2 - (M.P p.1 p.2.1 p.2.2) ^ 2)) +
            2 * ((N : ℝ) * eps_0) / 3)) := by
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let good : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s a s', |M.P s a s' - (M.empiricalApproxMDPRV hN ω).P_hat s a s'| < eps_0}
  let target : Set (M.SampleIndex N → M.S) :=
    {ω | ∀ s, V_ref ω s - M.empiricalGreedyValue hN ω s ≤
      2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
        (1 - M.γ) ^ 2}
  have h_subset : good ⊆ target := by
    intro ω hω
    dsimp [good, target] at hω ⊢
    exact M.minimax_from_empirical_fixed_points_good_event
      hN ω eps_0 heps_0 hω (pi_ref ω) (V_ref ω) (hV_ref ω)
  have h_pac := M.generative_model_pac_bernstein hN eps_0 heps_0
  have htarget_ne_top : (M.generativeModelMeasure N) target ≠ ∞ := by
    have htarget_lt_top : (M.generativeModelMeasure N) target < ∞ := by
      calc
        (M.generativeModelMeasure N) target ≤ (M.generativeModelMeasure N) Set.univ :=
          measure_mono (by intro ω _; simp)
        _ = 1 := by simp
        _ < ∞ := by simp
    exact ne_of_lt htarget_lt_top
  calc
    1 - ∑ p : M.S × M.A × M.S,
        2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
          (2 * ((N : ℝ) * (M.P p.1 p.2.1 p.2.2 - (M.P p.1 p.2.1 p.2.2) ^ 2)) +
            2 * ((N : ℝ) * eps_0) / 3))
      ≤ (M.generativeModelMeasure N).real good := by
        simpa [good] using h_pac
    _ ≤ (M.generativeModelMeasure N).real target :=
        measureReal_mono h_subset htarget_ne_top
    _ = (M.generativeModelMeasure N).real
          {ω | ∀ s, V_ref ω s - M.empiricalGreedyValue hN ω s ≤
            2 * M.γ * M.R_max * (↑(Fintype.card M.S) * eps_0) /
              (1 - M.γ) ^ 2} := by
        rfl

/-! ### Sample Complexity Inversion

The capstone theorem bounds the value gap as a function of per-entry error
tolerance `eps_0` and sample count `N`. This section inverts the relationship:
given desired value gap `ε` and confidence `1-δ`, we show there exists a
sufficient sample count `N₀`.

The proof uses the Hoeffding-based capstone for cleaner algebraic inversion.
The Bernstein-based capstone yields tighter constants. -/

/-- Each transition probability is bounded by 1, since probabilities are
    nonneg and sum to 1 over the next-state space. -/
lemma P_le_one (s : M.S) (a : M.A) (s' : M.S) : M.P s a s' ≤ 1 := by
  calc M.P s a s' ≤ ∑ s'' : M.S, M.P s a s'' :=
        Finset.single_le_sum (f := fun s'' => M.P s a s'')
          (fun s'' _ => M.P_nonneg s a s'') (Finset.mem_univ s')
    _ = 1 := M.P_sum_one s a

/-- The per-entry error tolerance chosen to make the deterministic
    value-gap bound `2γR_max|S|ε₀/(1-γ)²` equal the target `ε`.
    Defined as `ε(1-γ)²/(2γR_max|S|)`. Requires `γ > 0`. -/
noncomputable def pac_eps_0 (ε : ℝ) : ℝ :=
  ε * (1 - M.γ) ^ 2 / (2 * M.γ * M.R_max * ↑(Fintype.card M.S))

lemma pac_eps_0_pos {ε : ℝ} (hε : 0 < ε) (hγ : 0 < M.γ) :
    0 < M.pac_eps_0 ε := by
  unfold pac_eps_0
  apply div_pos
  · exact mul_pos hε (sq_pos_of_pos (sub_pos.mpr M.γ_lt_one))
  · exact mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hγ) M.R_max_pos)
      (Nat.cast_pos.mpr Fintype.card_pos)

/-- With the chosen `pac_eps_0`, the deterministic value-gap bound equals ε. -/
lemma pac_value_gap_eq {ε : ℝ} (hε : 0 < ε) (hγ : 0 < M.γ) :
    2 * M.γ * M.R_max * (↑(Fintype.card M.S) * M.pac_eps_0 ε) /
      (1 - M.γ) ^ 2 = ε := by
  unfold pac_eps_0
  have hγ_ne : M.γ ≠ 0 := ne_of_gt hγ
  have hR_ne : M.R_max ≠ 0 := ne_of_gt M.R_max_pos
  have hS_ne : (Fintype.card M.S : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  have h1γ_ne : (1 : ℝ) - M.γ ≠ 0 := ne_of_gt (sub_pos.mpr M.γ_lt_one)
  field_simp [hγ_ne, hR_ne, hS_ne, h1γ_ne]

/-- The Hoeffding failure term `K·2·exp(-2Nc²)` tends to zero as `N → ∞`.
    For any `c > 0` and `δ > 0`, there exists `N₀` such that for all `N ≥ N₀`
    the failure is at most `δ`.

    Proof uses `1 + x ≤ exp(x)`, so `exp(-x) ≤ 1/(1+x)`, giving a polynomial
    sufficient condition that avoids log/exp inversion. -/
lemma hoeffding_failure_eventually_small
    (c : ℝ) (hc : 0 < c) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ↑(Fintype.card M.S) * ↑(Fintype.card M.S) * ↑(Fintype.card M.A) *
        (2 * Real.exp (-2 * ↑N * c ^ 2)) ≤ δ := by
  -- K = |S|²|A| > 0
  set K : ℝ := ↑(Fintype.card M.S) * ↑(Fintype.card M.S) *
    ↑(Fintype.card M.A)
  have hK_pos : 0 < K := by positivity
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  -- We need N large enough that K * 2 * exp(-2Nc²) ≤ δ.
  -- Key bound: 1 + x ≤ exp(x) for all x, so exp(-x) ≤ 1/(1+x) for x > -1.
  -- With x = 2Nc²: exp(-2Nc²) ≤ 1/(1 + 2Nc²).
  -- So K * 2/(1 + 2Nc²) ≤ δ when 1 + 2Nc² ≥ 2K/δ, i.e., N ≥ K/(δc²).
  -- Choose N₀ = max 1 ⌈K/(δ·c²)⌉₊.
  refine ⟨max 1 ⌈K / (δ * c ^ 2)⌉₊, by omega, fun N hN => ?_⟩
  -- N ≥ ⌈K/(δc²)⌉₊ ≥ K/(δc²)
  have hdc_pos : 0 < δ * c ^ 2 := mul_pos hδ hc2
  have hNge : K / (δ * c ^ 2) ≤ ↑N := by
    have h1 : K / (δ * c ^ 2) ≤ ↑⌈K / (δ * c ^ 2)⌉₊ := Nat.le_ceil _
    have h2 : ⌈K / (δ * c ^ 2)⌉₊ ≤ max 1 ⌈K / (δ * c ^ 2)⌉₊ :=
      le_max_right _ _
    have h3 : max 1 ⌈K / (δ * c ^ 2)⌉₊ ≤ N := hN
    calc K / (δ * c ^ 2) ≤ ↑⌈K / (δ * c ^ 2)⌉₊ := h1
      _ ≤ ↑(max 1 ⌈K / (δ * c ^ 2)⌉₊) := Nat.cast_le.mpr h2
      _ ≤ ↑N := Nat.cast_le.mpr h3
  -- From hNge: K ≤ N·δ·c²
  have hKN : K ≤ ↑N * (δ * c ^ 2) := by
    rwa [div_le_iff₀ hdc_pos] at hNge
  -- exp(2Nc²) ≥ 1 + 2Nc² (from x+1 ≤ exp(x))
  have h_exp_ge : 2 * ↑N * c ^ 2 + 1 ≤ Real.exp (2 * ↑N * c ^ 2) :=
    Real.add_one_le_exp _
  -- Therefore 2K ≤ δ·exp(2Nc²)
  have h2K : 2 * K ≤ δ * Real.exp (2 * ↑N * c ^ 2) :=
    calc 2 * K ≤ 2 * (↑N * (δ * c ^ 2)) := by linarith
      _ = δ * (2 * ↑N * c ^ 2) := by ring
      _ ≤ δ * (2 * ↑N * c ^ 2 + 1) := by linarith
      _ ≤ δ * Real.exp (2 * ↑N * c ^ 2) :=
          mul_le_mul_of_nonneg_left h_exp_ge hδ.le
  -- K·2·exp(-2Nc²) · exp(2Nc²) = 2K  [since exp(-x)·exp(x) = 1]
  -- and 2K ≤ δ·exp(2Nc²), so dividing by exp(2Nc²) > 0 gives the result.
  have hexp_pos : 0 < Real.exp (2 * ↑N * c ^ 2) := Real.exp_pos _
  have h_prod : K * (2 * Real.exp (-2 * ↑N * c ^ 2)) *
      Real.exp (2 * ↑N * c ^ 2) = 2 * K := by
    have h1 : Real.exp (-2 * ↑N * c ^ 2) * Real.exp (2 * ↑N * c ^ 2) = 1 := by
      rw [← Real.exp_add]
      simp [Real.exp_zero]
    nlinarith [h1]
  -- K * 2 * exp(-2Nc²) ≤ δ
  have h_ineq : K * (2 * Real.exp (-2 * ↑N * c ^ 2)) *
      Real.exp (2 * ↑N * c ^ 2) ≤ δ * Real.exp (2 * ↑N * c ^ 2) := by
    rw [h_prod]; exact h2K
  exact le_of_mul_le_mul_right h_ineq hexp_pos

/-! ### Bernstein Log-Rate Inversion

The following upgrades the polynomial-in-1/δ Hoeffding inversion above to
a logarithmic `log(1/δ)` rate using the Bernstein capstone.

Key steps:
1. Bound each per-entry Bernstein exponent uniformly using `p(1-p) ≤ 1/4`.
2. Sum over `|S|²|A|` entries to get `K·2·exp(-N·c)` where `c = ε₀²/(1/2+2ε₀/3)`.
3. Invert via `Real.log`: N ≥ log(2K/δ)/c suffices. -/

/-- Bernstein coefficient: `c = ε₀²/(1/2 + 2ε₀/3)`, the exponent rate
    after bounding the per-entry variance `p(1-p)` by `1/4`. -/
noncomputable def bernsteinCoeff (eps_0 : ℝ) : ℝ :=
  eps_0 ^ 2 / (1 / 2 + 2 * eps_0 / 3)

lemma bernsteinCoeff_pos {eps_0 : ℝ} (heps : 0 < eps_0) :
    0 < bernsteinCoeff eps_0 := by
  apply div_pos (sq_pos_of_pos heps)
  linarith

/-- Each Bernstein per-entry failure term is bounded by the uniform
    exponential `2·exp(-N·c)` after replacing `p(1-p)` with `1/4`. -/
lemma bernstein_entry_uniform_bound
    {N : ℕ} (hN : 0 < N) (eps_0 : ℝ) (heps : 0 < eps_0)
    (s : M.S) (a : M.A) (s' : M.S) :
    2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
      (2 * ((N : ℝ) * (M.P s a s' - (M.P s a s') ^ 2)) +
        2 * ((N : ℝ) * eps_0) / 3)) ≤
    2 * Real.exp (-(↑N * bernsteinCoeff eps_0)) := by
  -- Strategy: show the exponent with actual variance ≤ exponent with 1/4,
  -- then exp(smaller) ≤ exp(larger) ≤ bound.
  -- We'll prove a*exp(x) ≤ a*exp(y) via a*exp(x)/a*exp(y) argument.
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hp_le : M.P s a s' - (M.P s a s') ^ 2 ≤ 1 / 4 := by
    nlinarith [M.P_nonneg s a s', M.P_le_one s a s',
               sq_nonneg (M.P s a s' - 1/2)]
  have h_denom_pos : 0 < 2 * ((N : ℝ) * (M.P s a s' -
      (M.P s a s') ^ 2)) + 2 * ((N : ℝ) * eps_0) / 3 := by
    have : 0 ≤ M.P s a s' - (M.P s a s') ^ 2 := by
      nlinarith [M.P_nonneg s a s', M.P_le_one s a s']
    nlinarith
  have h_unif_pos : (0 : ℝ) < 1 / 2 + 2 * eps_0 / 3 := by linarith
  -- denom_actual ≤ N*(1/2 + 2ε₀/3) = denom_uniform
  have h_denom_le : 2 * (↑N * (M.P s a s' - (M.P s a s') ^ 2)) +
      2 * (↑N * eps_0) / 3 ≤ ↑N * (1 / 2 + 2 * eps_0 / 3) := by
    nlinarith
  -- Key: -(N*ε₀)²/denom_actual ≤ -(N*ε₀)²/denom_uniform
  -- because denom_actual ≤ denom_uniform and the numerator is negative
  -- And -(N*ε₀)²/denom_uniform = -N*c
  -- So exp(-(N*ε₀)²/denom_actual) ≤ exp(-N*c)
  -- Multiply through by denom_actual*denom_uniform to avoid division:
  -- Need: exp(actual_exponent) ≤ exp(uniform_exponent)
  -- actual_exponent ≤ uniform_exponent because:
  --   actual: -(N*ε₀)² / D_actual,  uniform: -N*c = -(N*ε₀)² / D_uniform
  --   D_actual ≤ D_uniform, so actual ≤ uniform (both negative, larger denom → less negative)
  -- Use exp_div_exp or direct multiplication
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  -- Goal: -(↑N * eps_0) ^ 2 / denom_actual ≤ -(↑N * bernsteinCoeff eps_0)
  -- Rewrite -(↑N * c) as -(N*ε₀)² / (N*(1/2+2ε₀/3))
  have h_uniform_eq : -(↑N * bernsteinCoeff eps_0) =
      -(↑N * eps_0) ^ 2 / (↑N * (1 / 2 + 2 * eps_0 / 3)) := by
    unfold bernsteinCoeff; field_simp
  rw [h_uniform_eq]
  -- Now: -(a²)/D_act ≤ -(a²)/D_unif, where D_act ≤ D_unif
  -- Since a² > 0, -(a²) < 0, and D_act, D_unif > 0:
  -- (-a²)/D_act ≤ (-a²)/D_unif ↔ D_act ≤ D_unif (divide negative by larger → more negative)
  -- (-a²)/D_act ≤ (-a²)/D_unif when D_act ≤ D_unif and -a² ≤ 0
  -- Proof: multiply both sides by D_act * D_unif > 0
  have h_num_nonpos : -(↑N * eps_0) ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg (↑N * eps_0)]
  have h_unif_denom_pos : 0 < ↑N * (1 / 2 + 2 * eps_0 / 3) := by
    positivity
  rw [div_le_div_iff₀ h_denom_pos h_unif_denom_pos]
  exact mul_le_mul_of_nonpos_left h_denom_le h_num_nonpos

/-- The Bernstein failure sum is bounded by `K·2·exp(-N·c)`. -/
lemma bernstein_sum_le_uniform
    {N : ℕ} (hN : 0 < N) (eps_0 : ℝ) (heps : 0 < eps_0) :
    ∑ p : M.S × M.A × M.S,
      2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
        (2 * ((N : ℝ) * (M.P p.1 p.2.1 p.2.2 -
          (M.P p.1 p.2.1 p.2.2) ^ 2)) +
          2 * ((N : ℝ) * eps_0) / 3)) ≤
    ↑(Fintype.card (M.S × M.A × M.S)) *
      (2 * Real.exp (-(↑N * bernsteinCoeff eps_0))) := by
  calc ∑ p : M.S × M.A × M.S, _ ≤
      ∑ _ : M.S × M.A × M.S,
        2 * Real.exp (-(↑N * bernsteinCoeff eps_0)) := by
        apply Finset.sum_le_sum; intro ⟨s, a, s'⟩ _
        exact M.bernstein_entry_uniform_bound hN eps_0 heps s a s'
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Bernstein log-rate failure bound.**
    When `N ≥ log(2K/δ) / c` where `c = bernsteinCoeff ε₀`,
    the Bernstein failure sum is at most `δ`.

    This gives `N₀ = O(log(1/δ))`, improving on the polynomial rate
    from `hoeffding_failure_eventually_small`. -/
lemma bernstein_failure_le_delta
    {N : ℕ} (hN : 0 < N) (eps_0 : ℝ) (heps : 0 < eps_0)
    (δ : ℝ) (hδ : 0 < δ)
    (hNge : Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ) /
      bernsteinCoeff eps_0 ≤ ↑N) :
    ∑ p : M.S × M.A × M.S,
      2 * Real.exp (-((N : ℝ) * eps_0) ^ 2 /
        (2 * ((N : ℝ) * (M.P p.1 p.2.1 p.2.2 -
          (M.P p.1 p.2.1 p.2.2) ^ 2)) +
          2 * ((N : ℝ) * eps_0) / 3)) ≤ δ := by
  have hK_pos : (0 : ℝ) < Fintype.card (M.S × M.A × M.S) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hc_pos : 0 < bernsteinCoeff eps_0 := bernsteinCoeff_pos heps
  -- Step 1: bound the sum by K·2·exp(-Nc)
  have h_sum := M.bernstein_sum_le_uniform hN eps_0 heps
  -- Step 2: from hNge, N·c ≥ log(2K/δ)
  have h_Nc : Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ) ≤
      ↑N * bernsteinCoeff eps_0 := by
    rwa [div_le_iff₀ hc_pos] at hNge
  -- Step 3: exp(-Nc) ≤ exp(-log(2K/δ)) = δ/(2K)
  have h2K_pos : 0 < 2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ := by positivity
  have h_exp_le : Real.exp (-(↑N * bernsteinCoeff eps_0)) ≤
      δ / (2 * ↑(Fintype.card (M.S × M.A × M.S))) := by
    calc Real.exp (-(↑N * bernsteinCoeff eps_0))
        ≤ Real.exp (-(Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ))) :=
          Real.exp_le_exp_of_le (neg_le_neg h_Nc)
      _ = (Real.exp (Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ)))⁻¹ :=
          Real.exp_neg _
      _ = (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ)⁻¹ := by
          rw [Real.exp_log h2K_pos]
      _ = δ / (2 * ↑(Fintype.card (M.S × M.A × M.S))) := by rw [inv_div]
  -- Step 4: K·2·exp(-Nc) ≤ K·2·δ/(2K) = δ
  calc ∑ p : M.S × M.A × M.S, _
      ≤ ↑(Fintype.card (M.S × M.A × M.S)) *
        (2 * Real.exp (-(↑N * bernsteinCoeff eps_0))) := h_sum
    _ ≤ ↑(Fintype.card (M.S × M.A × M.S)) *
        (2 * (δ / (2 * ↑(Fintype.card (M.S × M.A × M.S))))) := by gcongr
    _ = δ := by field_simp

/-- **Minimax PAC with Bernstein concentration (composed).**

    End-to-end composition of:
    1. `generative_model_pac_bernstein` — transition concentration w.h.p.
    2. `minimax_from_empirical_fixed_points_good_event` — deterministic value gap

    When `N ≥ log(2|S×A×S|/δ) / bernsteinCoeff(ε_T)`, the empirical greedy
    policy satisfies:
      V_ref(s) - V̂(s) ≤ 2γ·R_max·|S|·ε_T / (1-γ)²
    with probability ≥ 1-δ.

    This theorem directly exposes the per-entry transition tolerance ε_T
    and the corresponding minimax rate, making the composition between
    concentration and deterministic reduction explicit. The `conditional`
    minimax_sample_complexity theorem is now discharged for all cases
    where Bernstein concentration provides the transition-error bound. -/
theorem minimax_pac_bernstein_composed
    {N : ℕ} (hN : 0 < N)
    (ε_T : ℝ) (hε_T : 0 < ε_T) (δ : ℝ) (hδ : 0 < δ)
    (hNge : Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ) /
      bernsteinCoeff ε_T ≤ ↑N)
    (π_ref : M.StochasticPolicy) (V_ref : M.StateValueFn)
    (hV : M.isValueOf V_ref π_ref) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤
        2 * M.γ * M.R_max * (↑(Fintype.card M.S) * ε_T) /
          (1 - M.γ) ^ 2} ≥ 1 - δ := by
  -- Compose: Bernstein capstone gives value gap w.h.p. via Bernstein failure
  have h_capstone :=
    M.minimax_value_gap_high_probability_from_empirical_fixed_points_bernstein
      hN ε_T hε_T
      (fun _ => π_ref) (fun _ => V_ref) (fun _ => hV)
  have h_fail := M.bernstein_failure_le_delta hN ε_T hε_T δ hδ hNge
  linarith

/-- **PAC sample complexity with Bernstein log-rate.**
    Given ε > 0, δ > 0, γ > 0, and any reference policy, when
    `N ≥ log(2|S|²|A|/δ) / bernsteinCoeff(pac_eps_0 ε)`,
    the empirical greedy policy is ε-optimal with probability ≥ 1-δ.

    The sample count scales as `O(log(1/δ))` — the near-minimax rate.
    This improves on `pac_rl_generative_model` which uses polynomial rate. -/
theorem pac_rl_generative_model_bernstein
    {N : ℕ} (hN : 0 < N)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hγ : 0 < M.γ)
    (hNge : Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ) /
      bernsteinCoeff (M.pac_eps_0 ε) ≤ ↑N)
    (π_ref : M.StochasticPolicy) (V_ref : M.StateValueFn)
    (hV : M.isValueOf V_ref π_ref) :
    (M.generativeModelMeasure N).real
      {ω | ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤ ε} ≥
      1 - δ := by
  have hc_pos := M.pac_eps_0_pos hε hγ
  -- Apply the Bernstein capstone
  have h_capstone :=
    M.minimax_value_gap_high_probability_from_empirical_fixed_points_bernstein
      hN (M.pac_eps_0 ε) hc_pos
      (fun _ => π_ref) (fun _ => V_ref) (fun _ => hV)
  -- Rewrite the value-gap bound to ε
  have h_sets_eq :
      {ω : M.SampleIndex N → M.S |
        ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤
          2 * M.γ * M.R_max * (↑(Fintype.card M.S) * M.pac_eps_0 ε) /
            (1 - M.γ) ^ 2} =
      {ω | ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤ ε} := by
    ext ω
    simp only [Set.mem_setOf_eq, M.pac_value_gap_eq hε hγ]
  rw [h_sets_eq] at h_capstone
  -- The Bernstein failure sum ≤ δ
  have h_fail := M.bernstein_failure_le_delta hN
    (M.pac_eps_0 ε) hc_pos δ hδ hNge
  linarith

/-- **Existential PAC sample complexity for the generative model.**
    Given any reference policy `π_ref` with value `V_ref` in the true MDP
    (e.g. the optimal policy), there exists a sample count `N₀` such that
    for `N ≥ N₀` i.i.d. samples per (s,a) pair from the generative model,
    the plug-in empirical greedy policy satisfies
    `V_ref(s) - V̂(s) ≤ ε` for all states with probability ≥ `1 - δ`.

    The sufficient `N₀` is polynomial in `1/δ` (from the `1+x ≤ exp(x)`
    bound in `hoeffding_failure_eventually_small`), which is weaker than
    the logarithmic `log(1/δ)` rate targeted by the sharper minimax result.
    The Bernstein-based capstone
    `minimax_value_gap_high_probability_from_empirical_fixed_points_bernstein`
    achieves a tighter per-entry bound; a closed-form inversion of that
    bound would recover the near-minimax rate.

    Requires `γ > 0`; the `γ = 0` case is trivial (value = immediate reward). -/
theorem pac_rl_generative_model
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hγ : 0 < M.γ)
    (π_ref : M.StochasticPolicy) (V_ref : M.StateValueFn)
    (hV : M.isValueOf V_ref π_ref) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      (M.generativeModelMeasure N).real
        {ω | ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤ ε} ≥
        1 - δ := by
  -- Choose eps_0 so that the deterministic value-gap bound equals ε
  have hc_pos := M.pac_eps_0_pos hε hγ
  -- Get N₀ from the Hoeffding failure bound
  obtain ⟨N₀, hN₀_pos, hN₀⟩ := M.hoeffding_failure_eventually_small
    (M.pac_eps_0 ε) hc_pos δ hδ
  refine ⟨N₀, hN₀_pos, fun N hN hNge => ?_⟩
  -- Apply the Hoeffding capstone with constant reference policy
  have h_capstone :=
    M.minimax_value_gap_high_probability_from_empirical_fixed_points
      hN (M.pac_eps_0 ε) hc_pos
      (fun _ => π_ref) (fun _ => V_ref) (fun _ => hV)
  -- Rewrite the value-gap bound to ε
  have h_sets_eq :
      {ω : M.SampleIndex N → M.S |
        ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤
          2 * M.γ * M.R_max * (↑(Fintype.card M.S) * M.pac_eps_0 ε) /
            (1 - M.γ) ^ 2} =
      {ω | ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤ ε} := by
    ext ω
    simp only [Set.mem_setOf_eq, M.pac_value_gap_eq hε hγ]
  rw [h_sets_eq] at h_capstone
  -- The Hoeffding failure ≤ δ
  have h_fail := hN₀ N hNge
  linarith

/-- **PAC theorem for generative-model RL (optimal-value form).**
    For any finite discounted MDP with `γ > 0`, there exists an optimal
    value function `V*` dominating all policies, and a sample count `N₀`,
    such that with `N ≥ N₀` i.i.d. samples per (s,a) pair from the
    generative model, the plug-in empirical greedy policy satisfies
    `V*(s) - V̂(s) ≤ ε` for all states with probability at least `1 - δ`.

    The sample complexity `N₀` is existential (polynomial in `1/δ`);
    see `pac_rl_generative_model` for rate discussion.
    Requires `γ > 0`; the `γ = 0` case is trivial. -/
theorem pac_rl_generative_model_optimal
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hγ : 0 < M.γ) :
    ∃ (V_star : M.StateValueFn),
      -- V_star dominates all policy values (it is the optimal value function)
      (∀ (π : M.StochasticPolicy) (V_pi : M.StateValueFn),
        M.isValueOf V_pi π → ∀ s, V_pi s ≤ V_star s) ∧
      -- Sample complexity: N ≥ N₀ suffices for PAC guarantee
      ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
        (M.generativeModelMeasure N).real
          {ω | ∀ s, V_star s - M.empiricalGreedyValue hN ω s ≤ ε} ≥
          1 - δ := by
  -- Construct the optimal Q-function via Banach fixed point
  obtain ⟨Q_star, hQ_star⟩ := M.exists_bellmanOptimalQ_fixedPoint
  -- Extract optimal policy and value from Q*
  have h_opt := M.optimal_policy_exists Q_star hQ_star
  set V_star : M.StateValueFn :=
    fun s => Finset.univ.sup' Finset.univ_nonempty (Q_star s)
  set π_star := M.greedyStochasticPolicy Q_star
  refine ⟨V_star, h_opt.2, ?_⟩
  exact M.pac_rl_generative_model ε δ hε hδ hγ π_star V_star h_opt.1

/-! ### Existential Bernstein PAC with Log-Rate

The following upgrades `pac_rl_generative_model` (polynomial rate) to use
Bernstein concentration, yielding an existential N₀ with `O(log(1/δ))` scaling.
This removes the free `N` hypothesis from `pac_rl_generative_model_bernstein`,
making the sample-complexity statement self-contained. -/

/-- **Existential PAC sample complexity with Bernstein log-rate.**

    Given any reference policy `π_ref` with value `V_ref` in the true MDP,
    there exists a sample count `N₀` such that for `N ≥ N₀` i.i.d. samples
    per (s,a) pair from the generative model, the plug-in empirical greedy
    policy satisfies `V_ref(s) - V̂(s) ≤ ε` for all states with
    probability ≥ `1 - δ`.

    Unlike `pac_rl_generative_model` which uses Hoeffding (polynomial in 1/δ),
    this version uses Bernstein concentration and achieves `N₀ = O(log(1/δ))`.
    The `hNge` hypothesis of `pac_rl_generative_model_bernstein` is
    discharged by choosing `N₀ = max 1 ⌈log(2K/δ)/c⌉₊` where
    `c = bernsteinCoeff(pac_eps_0 ε)`.

    Requires `γ > 0`; the `γ = 0` case is trivial (value = immediate reward). -/
theorem pac_rl_generative_model_bernstein_existential
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hγ : 0 < M.γ)
    (π_ref : M.StochasticPolicy) (V_ref : M.StateValueFn)
    (hV : M.isValueOf V_ref π_ref) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      (M.generativeModelMeasure N).real
        {ω | ∀ s, V_ref s - M.empiricalGreedyValue hN ω s ≤ ε} ≥
        1 - δ := by
  -- The Bernstein coefficient c > 0
  set c := bernsteinCoeff (M.pac_eps_0 ε) with hc_def
  have hc_pos : 0 < c := bernsteinCoeff_pos (M.pac_eps_0_pos hε hγ)
  -- The log term (may or may not be positive)
  set L := Real.log (2 * ↑(Fintype.card (M.S × M.A × M.S)) / δ) with hL_def
  -- Choose N₀ large enough that L/c ≤ N₀
  set N₀ := max 1 ⌈L / c⌉₊ with hN₀_def
  refine ⟨N₀, by omega, fun N hN hNge => ?_⟩
  -- Show the hNge hypothesis of pac_rl_generative_model_bernstein holds
  have hNge' : L / c ≤ ↑N := by
    calc L / c ≤ ↑⌈L / c⌉₊ := Nat.le_ceil _
      _ ≤ ↑N₀ := Nat.cast_le.mpr (le_max_right _ _)
      _ ≤ ↑N := Nat.cast_le.mpr hNge
  exact M.pac_rl_generative_model_bernstein hN ε δ hε hδ hγ hNge' π_ref V_ref hV

/-- **Existential PAC with Bernstein log-rate (optimal-value form).**

    For any finite discounted MDP with `γ > 0`, there exists an optimal
    value function `V*` dominating all policies, and a sample count `N₀`
    with `O(log(1/δ))` scaling, such that the empirical greedy policy
    is ε-optimal with probability ≥ 1 - δ for `N ≥ N₀`. -/
theorem pac_rl_generative_model_bernstein_optimal
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hγ : 0 < M.γ) :
    ∃ (V_star : M.StateValueFn),
      (∀ (π : M.StochasticPolicy) (V_pi : M.StateValueFn),
        M.isValueOf V_pi π → ∀ s, V_pi s ≤ V_star s) ∧
      ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
        (M.generativeModelMeasure N).real
          {ω | ∀ s, V_star s - M.empiricalGreedyValue hN ω s ≤ ε} ≥
          1 - δ := by
  obtain ⟨Q_star, hQ_star⟩ := M.exists_bellmanOptimalQ_fixedPoint
  have h_opt := M.optimal_policy_exists Q_star hQ_star
  set V_star : M.StateValueFn :=
    fun s => Finset.univ.sup' Finset.univ_nonempty (Q_star s)
  set π_star := M.greedyStochasticPolicy Q_star
  exact ⟨V_star, h_opt.2,
    M.pac_rl_generative_model_bernstein_existential ε δ hε hδ hγ
      π_star V_star h_opt.1⟩

end FiniteMDP

end
