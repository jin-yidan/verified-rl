# Theorem Catalog

This catalog covers the public `theorem` and `lemma` declarations imported by
the trusted benchmark root [`RLGeneralization.lean`](RLGeneralization.lean).

Purpose:

- give a human-language description of each trusted declaration,
- record whether it should be read as `exact`, `weaker`, or `conditional`,
- make the benchmark unit theorem-centered rather than file-centered.

Status vocabulary here:

- `exact`: faithful statement for its intended claim, or a straightforward infrastructure fact.
- `weaker`: a real theorem, but weaker than a headline target theorem or intentionally auxiliary.
- `conditional`: a kernel-checked theorem whose main analytical content still arrives through explicit hypotheses.

Conditional frontier results are tracked separately in
[`verification_manifest.json`](verification_manifest.json) and aggregated by
[`RLGeneralization/Draft.lean`](RLGeneralization/Draft.lean).

## RLGeneralization.MDP.Basic

- `R_max_pos` (`lemma`, exact): the global reward bound `R_max` is positive.
- `r_le_R_max` (`lemma`, exact): every reward is bounded above by `R_max`.
- `V_max_pos` (`lemma`, exact): the standard discounted value bound `V_max` is positive.
- `greedyAction_spec` (`theorem`, weaker): the chosen greedy action attains the maximal Q-value for a state.
- `greedyAction_eq_sup` (`theorem`, exact): the Q-value at the greedy action equals the finite supremum over actions.

## RLGeneralization.MDP.BellmanContraction

- `abs_weighted_sum_le_bound` (`lemma`, exact): bounded terms remain bounded after a stochastic weighted sum.
- `weighted_sum_le_sup` (`lemma`, exact): a weighted average is bounded by the pointwise supremum.
- `bellmanEvalOp_contraction` (`theorem`, exact): the Bellman evaluation operator is a `γ`-contraction.
- `abs_sup_sub_sup_le` (`theorem`, exact): finite suprema are Lipschitz under pointwise perturbation.
- `sup_sub_sup_le` (`lemma`, exact): one-sided finite-supremum perturbation bound.
- `bellmanOptOp_contraction` (`theorem`, exact): the Bellman optimality operator is a `γ`-contraction.
- `value_bounded_by_Vmax` (`theorem`, exact): Bellman-consistent values are bounded by the standard `V_max`.

## RLGeneralization.MDP.SimulationLemma

- `rewardError_le` (`lemma`, exact): reward mismatch is controlled by the global reward-error parameter.
- `transitionError_le` (`lemma`, exact): transition mismatch is controlled by the global transition-error parameter.
- `transition_value_error` (`lemma`, exact): one-step transition mismatch induces a bounded next-value error.
- `simulation_lemma` (`theorem`, weaker): Kearns-Singh style value-difference bound between a true and approximate model.

## RLGeneralization.MDP.ValueIteration

- `valueIterationQ_succ` (`lemma`, exact): unfolds one step of the value-iteration recursion.
- `value_iteration_geometric_error` (`theorem`, weaker): value iteration contracts geometrically toward `Q*`.
- `gamma_pow_le_exp_neg` (`theorem`, exact): standard bound comparing `γ^k` to an exponential.
- `value_iteration_threshold` (`theorem`, exact): explicit iteration count sufficient for an `ε`-accurate Q-value iterate.
- `q_error_amplification` (`theorem`, weaker): Q-error implies policy suboptimality, assuming a greedy selector.
- `value_iteration_policy_bound` (`theorem`, weaker): combines value-iteration error and Q-to-policy conversion into a policy-value bound.
- `value_iteration_with_greedy` (`theorem`, weaker): end-to-end value-iteration guarantee packaged with an external greedy policy selector.
- `value_iteration_epsilon_optimal` (`theorem`, weaker): for K ≥ log(C/ε)/(1-γ) iterations, a supplied V_greedy witness is 2ε/(1-γ)-optimal. Composes `value_iteration_threshold` with `q_error_amplification`. V_greedy is externally supplied.
- `value_iteration_epsilon_optimal_constructed` (`theorem`, exact): self-contained version that constructs V_greedy internally via Banach fixed point and `greedyStochasticPolicy`.

## RLGeneralization.MDP.PolicyIteration

- `valueFromQ_isValueOf` (`theorem`, exact): reconstructs the policy value from a Bellman-consistent action-value function.
- `bellmanEvalOpQ_monotone` (`theorem`, exact): the policy Bellman operator on Q-functions is monotone.
- `greedy_expectedAdvantage_nonneg` (`theorem`, exact): the greedy policy has nonnegative expected advantage relative to the baseline value induced by `Q`.
- `bellmanEvalOpQ_greedy_eq_bellmanOptOp` (`theorem`, exact): greedy policy evaluation on `Q` agrees with the Bellman optimality operator.
- `greedy_policy_value_improves` (`theorem`, exact): the greedy policy’s value dominates the old policy’s value.
- `policy_improvement_sandwich` (`theorem`, exact): a genuine policy-iteration step satisfies `TQ_k ≤ Q_{k+1} ≤ Q*`.
- `policy_iteration_convergence` (`theorem`, exact): evaluated greedy iterates converge geometrically to a Bellman-optimal fixed point.
- `bellmanOptOp_monotone` (`theorem`, weaker): the Bellman optimality operator is monotone.
- `sandwich_contraction` (`theorem`, weaker): a sandwich hypothesis implies geometric contraction.
- `sandwich_convergence` (`theorem`, weaker): sandwich iterates converge at a geometric rate.

## RLGeneralization.MDP.Resolvent

- `resolvent_bound` (`theorem`, exact): solutions of `V = v + γPV` satisfy the standard resolvent norm bound.
- `weighted_sum_le_max` (`lemma`, exact): a weighted sum of bounded terms is bounded by the maximum term.
- `resolvent_upper` (`theorem`, exact): one-sided resolvent comparison bound.
- `bellman_fixed_point_dominates` (`theorem`, weaker): any Bellman-optimal fixed point dominates every policy value.
- `crude_value_bound` (`theorem`, weaker): coarse value bound from Bellman/resolvent control.
- `greedyPolicy_expectedReward` (`lemma`, exact): expected reward under the greedy policy matches the greedy-action reward term.
- `greedyPolicy_expectedNextValue` (`lemma`, exact): expected next value under the greedy policy matches the greedy-action continuation term.
- `optimal_policy_exists` (`theorem`, exact): there exists an optimal policy achieving the Bellman-optimal value.
- `isActionValueOf_iff_fixedPoint` (`theorem`, exact): action-value functions for a policy are exactly fixed points of that policy’s Bellman operator.
- `bellmanEvalOpQ_contraction` (`theorem`, exact): the policy Bellman operator on Q-functions is a `γ`-contraction.
- `bellman_eval_unique_fixed_point` (`theorem`, exact): the policy Bellman operator has a unique fixed point.
- `bellman_eval_operator_form` (`theorem`, exact): explicit operator equation for policy action-values.
- `actionValue_bounded` (`theorem`, exact): policy action-values are uniformly bounded.

## RLGeneralization.MDP.BanachFixedPoint

- `supNormQ_eq_supPair` (`lemma`, exact): the project sup norm on Q-functions matches the flat sup over state-action pairs.
- `qSpace_dist_eq_supDistQ` (`lemma`, exact): the `PiLp ∞` metric agrees exactly with the project's `supDistQ` distance after transport.
- `bellmanEvalOpQSpace_contracting` (`lemma`, exact): the transported policy Bellman Q-operator is a contraction on a complete metric space.
- `actionValueFixedPoint_isActionValueOf` (`lemma`, exact): Banach's fixed point yields a Bellman-consistent action-value function for the policy.
- `exists_actionValue_fixedPoint` (`lemma`, exact): every policy admits an action-value fixed point.
- `tendsto_iterate_actionValueFixedPointQSpace` (`lemma`, exact): iterates of the transported Bellman operator converge to the fixed point.
- `apriori_dist_iterate_actionValueFixedPointQSpace_le` (`lemma`, exact): Banach's a priori geometric convergence bound for policy-evaluation iterates.
- `optimalQFixedPoint_isBellmanOptimalQ` (`lemma`, exact): Banach's fixed point yields a Bellman-optimal Q-function for the optimality operator.
- `exists_bellmanOptimalQ_fixedPoint` (`lemma`, exact): every discounted finite MDP admits a Bellman-optimal Q fixed point.
- `tendsto_iterate_optimalQFixedPointQSpace` (`lemma`, exact): iterates of the transported Bellman optimality operator converge to the optimal fixed point.

## RLGeneralization.MDP.PerformanceDifference

- `pdl_one_step` (`theorem`, weaker): one-step Bellman identity for the difference between two policy values.
- `pdl_bound` (`theorem`, weaker): resolvent-style bound on the difference between two policy values.

## RLGeneralization.MDP.OccupancyMeasure

- `transitionPow_zero` (`theorem`, exact): the zero-th transition power is the identity action on value functions.
- `transitionPow_sum_one` (`theorem`, exact): every transition power remains stochastic.
- `transitionPow_nonneg` (`theorem`, exact): every transition power remains nonnegative.
- `truncatedOccupancy_nonneg` (`theorem`, exact): truncated occupancy weights are nonnegative.
- `expectedUnderPow_zero` (`theorem`, exact): expectation under the zero-th transition power is the original value.
- `expectedUnderPow_succ` (`theorem`, exact): recursion for expectation under a higher transition power.
- `truncated_pdl` (`theorem`, weaker): truncated performance-difference identity with a remainder term.
- `truncated_pdl_remainder_bound` (`theorem`, exact): the truncated PDL remainder admits a geometric bound.
- `pdl_remainder_vanishes` (`theorem`, exact): the truncated PDL remainder converges to zero.
- `exact_pdl_limit` (`theorem`, exact): limit form of the performance-difference lemma via the truncated identity.
- `transitionPow_le_one` (`lemma`, exact): each transition-power entry is bounded by 1.
- `summable_geometric_transitionPow` (`lemma`, exact): the geometric-transition series is summable.
- `discountedVisitation` (`def`): infinite-horizon discounted state-visitation weight via tsum.
- `discountedVisitation_nonneg` (`lemma`, exact): discounted visitation is nonneg.
- `discountedVisitation_sum` (`theorem`, exact): discounted visitation sums to (1-γ)⁻¹ over states.
- `occupancyMeasure_sum_one` (`theorem`, exact): the normalized occupancy measure (1-γ)·discountedVisitation sums to 1.
- `stateOccupancy` (`def`): normalized discounted state-visitation distribution d^π(s₀,s) = (1-γ)·∑γ^t P^t(s₀,s).
- `stateActionOccupancy` (`def`): state-action occupancy d^π(s₀,s,a) = d^π(s₀,s)·π(a|s).
- `stateOccupancy_sum_one` (`theorem`, exact): normalized state occupancy sums to 1.
- `pdl_occupancy_form` (`theorem`, exact): PDL with unnormalized occupancy: V^π - V^{π'} = ∑_s d_unnorm(s) · E_π[A^{π'}(s)].
- `pdl_normalized` (`theorem`, exact): normalized PDL: V^π - V^{π'} = (1-γ)⁻¹ · ∑_s d^π(s) · E_π[A^{π'}(s)] where d^π is the normalized occupancy distribution (sums to 1).

## RLGeneralization.MDP.FiniteHorizon

- `backwardQ_zero` (`theorem`, exact): the zero-step backward Q-function is zero.
- `backwardQ_nonneg` (`theorem`, exact): backward Q-values are nonnegative.
- `backwardQ_le` (`theorem`, exact): backward Q-values are bounded by the remaining horizon length.
- `backwardQ_dominates_step` (`theorem`, exact): one-step backward-induction domination step.
- `backwardQ_dominates_policy` (`theorem`, exact): full finite-horizon domination of every policy by the backward-optimal Q-values.

## RLGeneralization.Generalization.SampleComplexity

- `empiricalTransition_nonneg` (`lemma`, exact): empirical transition probabilities are nonnegative.
- `empiricalTransition_sum_one` (`lemma`, exact): empirical transition probabilities sum to one.
- `model_based_comparison` (`theorem`, weaker): deterministic comparison bound between two policies under model error.
- `sample_complexity_from_transition_error` (`theorem`, weaker): deterministic sample-complexity core from a transition-error bound.
- `approx_value_bounded` (`lemma`, exact): approximate-model value functions stay uniformly bounded.
- `crude_value_bound_from_transition_error` (`theorem`, exact): single-policy value gap from transition error.
- `optimality_gap_from_transition_error` (`theorem`, exact): deterministic optimality-gap bound in the repository's naming scheme.

## RLGeneralization.Generalization.ComponentWise

- `value_gap_resolvent` (`theorem`, weaker): component-wise resolvent expression for a value gap.
- `value_gap_upper_bound` (`theorem`, weaker): component-wise upper bound on a value gap.
- `optimal_value_gap_upper_bound` (`theorem`, weaker): upper-direction form of the component-wise comparison lemma.
- `policy_value_gap_lower_bound` (`theorem`, weaker): lower-direction form of the component-wise comparison lemma.
- `optimal_value_comparison` (`theorem`, weaker): two-sided |V*_M - V*_M̂| ≤ ε_trans/(1-γ). This is a state-value corollary of the Q-function resolvent comparison. Combines upper/lower bounds with externally supplied optimality comparisons.

## RLGeneralization.LinearFeatures.LSVI

- `approx_dp_error` (`theorem`, exact): residual error at each stage accumulates linearly in horizon depth.
- `approx_dp_policy_gap` (`theorem`, weaker): approximate dynamic-programming residual yields a policy gap.
- `approx_dp_value_gap` (`theorem`, weaker): value-gap version of the approximate dynamic-programming guarantee.
- `greedyAction_is_sup` (`theorem`, exact): the chosen greedy action attains the finite supremum.
- `greedyAction_spec` (`theorem`, exact): explicit greedy-action optimality property for the LSVI setting.
- `policy_value_gap_linear` (`theorem`, weaker): linearized version of the greedy-policy value-gap estimate.
- `policy_value_gap` (`theorem`, exact): final greedy-policy value-gap bound in this line of formalization.

## RLGeneralization.LinearFeatures.RegressionBridge

- `lsvi_sample_complexity_rate` (`theorem`, conditional): LSVI policy gap ≤ 2H²√(Cσ²d/n), conditional on regression rate hypothesis.
- `lsvi_sample_complexity_inverse` (`theorem`, conditional): inverse form — η ≤ ε/(2H²) implies policy gap ≤ ε.
- `lsvi_sample_complexity` (`theorem`, conditional): full deterministic chain — given regression rate and sample size, policy gap ≤ ε.
- `lsvi_stage_slt_bound` (`theorem`, exact): direct application of SLT's `linear_minimax_rate` to an LSVI stage.

## RLGeneralization.Concentration.Hoeffding

- `transitionIndicator_nonneg` (`lemma`, exact): transition-indicator random variables are nonnegative.
- `transitionIndicator_le_one` (`lemma`, exact): transition-indicator random variables are bounded by one.
- `transitionIndicator_mem_Icc` (`lemma`, exact): transition-indicator random variables lie in `[0,1]`.
- `empirical_as_indicator_sum` (`theorem`, exact): empirical transition estimates are indicator averages.
- `l1_from_pointwise` (`theorem`, exact): pointwise transition error converts to an `L1` transition bound.
- `pac_from_concentration` (`theorem`, weaker): union-bound PAC event from pointwise concentration assumptions.

## RLGeneralization.Concentration.Bernstein

- `moment_bound_of_bounded` (`theorem`, exact): bounded centered variables satisfy the Bernstein moment condition.
- `factorial_ge_two_mul_three_pow` (`theorem`, exact): factorial lower bound used in the mgf proof.
- `bernstein_mgf_bound` (`theorem`, exact): Bernstein moment generating function bound.
- `bernstein_sum` (`theorem`, exact): Bernstein tail inequality for sums of independent variables.

## RLGeneralization.Concentration.GenerativeModelCore

- `samples_iIndepFun` (`theorem`, exact): coordinate projections in the generative-model product space are independent.
- `indicator_expectation` (`theorem`, exact): the expectation of a transition indicator equals the transition probability.
- `generative_model_pac` (`theorem`, exact): the empirical transition kernel satisfies the full PAC event under the product measure.

## RLGeneralization.Concentration.GenerativeModel

- `bernstein_sum_fintype` (`theorem`, exact): finite-index Bernstein tail bound for independent families indexed by a finite type.
- `coordinate_indicator_bernstein_upper` (`theorem`, exact): Bernstein tail bound specialized to the centered indicator coordinates for one fixed empirical transition entry, using the exact Bernoulli variance term.
- `empirical_transition_entry_bernstein_upper` (`theorem`, exact): reformulates the specialized Bernstein sum bound as an upper-tail inequality for the empirical transition entry itself.
- `empirical_transition_entry_bernstein_lower` (`theorem`, exact): matching lower-tail Bernstein inequality for one empirical transition entry.
- `empirical_transition_entry_bernstein_concentration` (`theorem`, exact): combines the upper and lower tails into a two-sided absolute-deviation Bernstein bound for one empirical transition entry.
- `generative_model_pac_bernstein` (`theorem`, exact): union-bounds the per-entry Bernstein inequalities over all `(s,a,s')` triples.
- `empiricalGreedyValue_isValueOf` (`theorem`, exact): the canonical true-model value of the empirical greedy policy is obtained by Banach policy evaluation.
- `minimax_from_empirical_fixed_points_good_event` (`theorem`, weaker): on the empirical-kernel good event, the minimax value-gap bound holds using canonical empirical evaluation and optimality fixed points.
- `minimax_value_gap_high_probability_from_empirical_fixed_points` (`theorem`, weaker): packages the PAC event with the canonical empirical fixed-point construction into a high-probability value-gap theorem.
- `minimax_value_gap_high_probability_from_empirical_fixed_points_bernstein` (`theorem`, weaker): Bernstein-based analogue of the same canonical fixed-point high-probability value-gap theorem.
- `P_le_one` (`lemma`, exact): each transition probability is bounded by 1.
- `pac_eps_0_pos` (`lemma`, exact): the error tolerance chosen for sample complexity inversion is positive.
- `pac_value_gap_eq` (`lemma`, exact): with the chosen error tolerance, the deterministic value-gap bound equals ε.
- `hoeffding_failure_eventually_small` (`lemma`, exact): for any c > 0 and δ > 0, there exists N₀ such that the Hoeffding failure term is at most δ for all N ≥ N₀.
- `pac_rl_generative_model` (`theorem`, weaker): PAC sample complexity for the generative model — there exists N₀ such that for N ≥ N₀, the empirical greedy policy is ε-optimal w.h.p.
- `pac_rl_generative_model_optimal` (`theorem`, weaker): presentation form using the optimal value function V* — ∃ V* dominating all policies, and ∃ N₀ for the PAC guarantee.
- `bernsteinCoeff` (`def`): rate constant ε₀²/(1/2 + 2ε₀/3) after bounding per-entry variance by 1/4.
- `bernstein_entry_uniform_bound` (`lemma`, exact): each Bernstein per-entry failure ≤ 2·exp(-N·bernsteinCoeff) via variance bound.
- `bernstein_sum_le_uniform` (`lemma`, exact): sum over |S|²|A| entries bounded by K·2·exp(-N·c).
- `bernstein_failure_le_delta` (`lemma`, exact): log-rate inversion: N ≥ log(2K/δ)/c implies failure ≤ δ.
- `pac_rl_generative_model_bernstein` (`theorem`, weaker): PAC with O(log(1/δ)) Bernstein rate. Uses uniform variance bound 1/4, not exact per-entry variance.
- `minimax_pac_bernstein_composed` (`theorem`, weaker): end-to-end composition of Bernstein concentration with minimax deterministic reduction, exposing per-entry transition tolerance ε_T directly.
- `pac_rl_generative_model_bernstein_existential` (`theorem`, weaker): existential N₀ wrapper for Bernstein PAC, removing the free sample-count hypothesis. N₀ = O(log(1/δ)).
- `pac_rl_generative_model_bernstein_optimal` (`theorem`, weaker): optimal-value form with existential N₀ and Bernstein log-rate.

## RLGeneralization.Generalization.MinimaxSampleComplexity

- `transition_variance_nonneg` (`lemma`, exact): transition variance is nonneg.
- `transition_variance_le_sq_norm` (`lemma`, exact): transition variance bounded by squared norm.
- `sqrt_variance_le_two_Vmax` (`lemma`, exact): square-root variance bound.
- `weighted_deviation_bound_genuine` (`theorem`, weaker): weighted-deviation resolvent bound with a looser constant.
- `variance_swap` (`theorem`, weaker): variance swap with explicit weaker comparison bound.
- `minimax_deterministic_core` (`theorem`, weaker): deterministic minimax comparison core.
- `minimax_deterministic_core_single_policy` (`theorem`, weaker): single-policy version of the deterministic core.
- `q_value_gap_from_v_gap` (`theorem`, weaker): Q-gap from V-gap with explicit hypothesis.
- `minimax_rate_scaling_V` (`theorem`, exact): existential scaling statement for the minimax rate.
- `minimax_rate_scaling_V_abs` (`theorem`, exact): symmetric version of the scaling statement.
- `minimax_sample_complexity_deterministic` (`theorem`, weaker): deterministic sample-complexity bound.
- `minimax_sample_complexity` (`theorem`, conditional): assumes the analytical composition/good-event layer.
- `minimax_rate_scaling` (`theorem`, weaker): existential rate scaling, not the full high-probability theorem.

## RLGeneralization.Bandits.UCB

- `gap_nonneg` (`theorem`, exact): suboptimality gaps are nonneg.
- `gap_eq_zero_iff_opt` (`theorem`, exact): zero gap characterizes optimal arms.
- `exists_optimal_arm` (`theorem`, exact): existence of an optimal arm.
- `optArm_gap` (`theorem`, exact): the designated optimal arm has zero gap.
- `pseudoRegret_eq_sum_gap` (`theorem`, exact): pseudo-regret decomposes as sum of gap-weighted pulls.
- `pseudoRegret_nonneg` (`theorem`, exact): pseudo-regret is nonneg.
- `confidenceWidth_nonneg` (`theorem`, exact): UCB confidence width is nonneg.
- `etc_oracle_regret_bound` (`theorem`, weaker): oracle explore-then-commit regret bound.
- `ucb_regret_from_pull_count_bounds` (`theorem`, conditional): deterministic regrouping from pull-count bounds.
- `oracle_gap_bound_of_etc_witness` (`theorem`, weaker): oracle gap bound from ETC witness.
- `oracle_worst_case_bound_via_etc` (`theorem`, weaker): worst-case bound via oracle ETC.
- `confidence_threshold` (`theorem`, exact): if n >= 8L/Delta^2, then sqrt(2L/n) <= Delta/2. Confidence width threshold for UCB pull-count analysis.
- `ucb_index_le_opt_mean` (`theorem`, exact): under concentration, a sufficiently-explored suboptimal arm's UCB index is at most mu*. If |mu_hat - mu| <= w and Delta >= 2w, then mu_hat + w <= mu*.
- `ucb_index_opt_ge_opt_mean` (`theorem`, exact): under concentration, the optimal arm's UCB index is at least mu*. If |mu_hat* - mu*| <= w, then mu* <= mu_hat* + w.
- `ucb_gap_dependent_regret` (`theorem`, conditional): UCB gap-dependent regret bound. Under the pull-count hypothesis (each suboptimal arm a has pullCount(a) <= 8L/Delta_a^2 + 1), R_T <= sum_{a:Delta>0} (8L/Delta_a + Delta_a). The sequential UCB selection argument is not formalized; the algebraic composition is fully proved.
- `ucbGoodEvent` (`def`): UCB good event — concentration holds for all arms with confidence width √(2L/n).
- `ucb_index_dominated_after_sufficient_pulls` (`theorem`, exact): under concentration with n >= 8L/Δ², arm a's UCB index ≤ μ*. Chains confidence_threshold with ucb_index_le_opt_mean.
- `ucb_gap_dependent_regret_from_good_event` (`theorem`, conditional): gap-dependent regret under good event. Forwards to ucb_gap_dependent_regret with pull-count hypothesis.
- `runningPullCount` (`def`): running pull count of arm a before round t — number of rounds s < t where I(s) = a.
- `pull_count_le_of_selection_domination` (`theorem`, exact): pure combinatorial counting lemma — if arm a cannot be selected once its running pull count reaches threshold, then pullCount ≤ threshold. Proved by induction on rounds.
- `ucb_index_strictly_dominated` (`theorem`, exact): strict version of UCB index domination. If 8L/Δ² < n strictly and |μ̂ - μ| ≤ √(2L/n), then μ̂ + √(2L/n) < μ*. Uses sqrt monotonicity for the strict bound.
- `ucb_gap_dependent_regret_full` (`theorem`, conditional): composed UCB gap-dependent regret bound. Under UCB selection rule (maximal index) and strict domination after threshold(a) pulls, R_T ≤ ∑ threshold(a)·Δ_a. Composes pull_count_le_of_selection_domination with fiberwise regret decomposition.
- `ucb_gap_dependent_regret_presentation` (`theorem`, conditional): clean presentation form with canonical threshold: R_T ≤ ∑(8L/Δ + 2Δ). Instantiates ucb_gap_dependent_regret_full and simplifies via ceiling arithmetic.

## RLGeneralization.Bandits.BanditConcentration

- `banditArmProb_val_le_one` (`lemma`, exact): the arm probability parameter is at most 1.
- `banditArmProb_le_one` (`lemma`, exact): NNReal version of the arm probability bound.
- `banditSamples_iIndepFun` (`theorem`, exact): coordinate projections from the bandit product sample space are independent.
- `rewardOf_nonneg` (`lemma`, exact): Bernoulli reward indicator is nonneg.
- `rewardOf_le_one` (`lemma`, exact): Bernoulli reward indicator is at most 1.
- `rewardOf_mem_Icc` (`lemma`, exact): Bernoulli reward indicator lies in [0,1].
- `armSamples_iIndepFun` (`theorem`, exact): samples for a fixed arm form an independent family.
- `coordinate_reward_expectation` (`theorem`, exact): the expectation of rewardOf at a fixed coordinate equals the arm probability.
- `arm_mean_concentration` (`theorem`, exact): Hoeffding concentration for a single arm's empirical mean: P(|mu_hat - p| >= eps) <= 2 exp(-2N eps^2).
- `all_arms_concentration` (`theorem`, exact): uniform concentration over all arms via union bound: P(exists a, |mu_hat_a - p_a| >= eps) <= 2K exp(-2N eps^2).

## RLGeneralization.BilinearRank.Auxiliary

- `inner_product_le_of_norm_bound` (`theorem`, exact): finite-dimensional Cauchy-Schwarz under unit-norm bounds.
- `abs_inner_product_le_of_norm_bound` (`theorem`, exact): absolute-value version of the same finite-dimensional bound.
- `bellman_error_le_of_rank` (`theorem`, exact): bilinear Bellman-rank structure bounds the total Bellman error by one.
- `bellman_error_le_one` (`theorem`, exact): one-sided Bellman-error version of the same bound.
- `episode_bellman_error_le_H` (`theorem`, exact): summing the per-step Bellman-error bound gives an `H`-step bound.

## RLGeneralization.Exploration.UCBVI

- `cumulativeRegret_nonneg` (`theorem`, exact): cumulative regret is nonnegative.
- `per_step_value_gap_nonneg` (`theorem`, exact): per-step value gaps are nonnegative.
- `throughout` (`lemma`, exact): local helper lemma used in the regret induction.
- `policyValueFn_zero` (`theorem`, exact): zero reward/value baseline identity for policy values.
- `regret_decomposition_step` (`theorem`, weaker): one-step regret decomposition underlying the UCBVI proof.
- `advantage_nonneg` (`theorem`, exact): policy advantage term is nonnegative under the stated conditions.
- `regret_nonneg_inductive` (`theorem`, exact): inductive nonnegativity of regret components.
- `regret_from_uniform_advantage_bound` (`theorem`, weaker): uniform advantage control implies an episode regret bound.
- `episode_regret_bound` (`theorem`, weaker): per-episode regret bound from a uniform bonus/advantage hypothesis.
- `cumulative_regret_le_total_bonuses` (`theorem`, weaker): cumulative regret is controlled by summed bonuses.
- `ucbvi_regret_from_bonus_hypotheses` (`theorem`, conditional): cumulative regret bound obtained by combining a per-episode bonus hypothesis with a total-bonus hypothesis.

## RLGeneralization.Exploration.BatchUCBVI

- `sum_sqrt_le_sqrt_card_mul_sum` (`theorem`, exact): Cauchy-Schwarz for square root sums: sum sqrt(a_i) <= sqrt(|s| * sum a_i). Derived from the discrete Cauchy-Schwarz inequality.
- `sum_inv_sqrt_le` (`theorem`, exact): harmonic-square-root bound: sum_{n=1}^{N} 1/sqrt(n) <= 2 sqrt(N). Proved via telescoping with the conjugate identity.
- `pigeonhole_bonus_bound` (`theorem`, exact): total bonus bound via pigeonhole + Cauchy-Schwarz: sum_i sum_{n=1}^{N(i)} 1/sqrt(n) <= 2 sqrt(|iota| * K) where K >= sum N(i). Chains sum_inv_sqrt_le with sum_sqrt_le_sqrt_card_mul_sum.

## RLGeneralization.PolicyOptimization.PolicyGradient

- `softmaxProb_nonneg` (`theorem`, exact): softmax probabilities are nonnegative.
- `softmaxProb_sum_one` (`theorem`, exact): softmax probabilities sum to one.
- `softmax_denom_pos` (`theorem`, exact): the softmax normalizing denominator is strictly positive.
- `softmaxProb_pos` (`theorem`, exact): softmax probabilities are strictly positive.
- `expected_advantage_zero` (`theorem`, exact): expected advantage under the current policy is zero.
- `softmax_expected_advantage_zero` (`theorem`, exact): softmax-specialized version of expected advantage zero.
- `baseline_subtraction` (`theorem`, exact): subtracting a baseline leaves the score-weighted expectation unchanged.
- `score_baseline_invariance` (`theorem`, weaker): baseline invariance for the policy-gradient estimator.
- `policy_gradient_advantage_form` (`theorem`, weaker): policy-gradient expression can be written with advantages instead of Q-values.
- `log_derivative_trick` (`theorem`, exact): algebraic log-derivative identity used in policy-gradient derivations.
- `value_eq_expected_action_value` (`theorem`, exact): policy value equals the policy-weighted expected action-value.
- `bellman_advantage_zero` (`theorem`, exact): Bellman-consistent advantages have zero policy expectation.

## RLGeneralization.PolicyOptimization.CPI

- `expectedAdvantage_self_zero` (`theorem`, exact): a policy has zero expected advantage under its own Bellman-consistent action-value function.
- `mixturePolicy_expectedAdvantage` (`theorem`, exact): the mixture-policy expected advantage scales linearly with the mixing weight.
- `cpi_resolvent_identity` (`theorem`, exact): the CPI mixture value gap satisfies the exact resolvent identity.
- `cpi_improvement_bound` (`theorem`, exact): the CPI mixture value gap obeys the resolvent sup-norm bound.
- `cpi_monotonic_improvement` (`theorem`, exact): the CPI mixture improves pointwise under nonnegative expected advantage.

## RLGeneralization.OfflineRL.FQI

- `pointwise_le_supDistQ` (`lemma`, exact): pointwise Q-error is bounded by the sup norm.
- `geom_sum_le_inv` (`lemma`, exact): standard geometric-series bound.
- `fqi_one_step` (`lemma`, exact): one-step fitted Q-iteration error recursion.
- `fqi_error_propagation` (`theorem`, exact): standard contraction-style error propagation for fitted Q-iteration under the stated per-step regression-error hypothesis.

## RLGeneralization.LinearMDP.Basic

- `optQ_linear` (`theorem`, exact): in a linear MDP, finite-horizon optimal Q-functions are linear in the feature map.

## RLGeneralization.PolicyOptimization.Optimality

- `gradient_domination_nonneg` (`theorem`, exact): the gradient-domination coefficient is nonnegative.

## RLGeneralization.ImitationLearning.Basic

- `behavior_cloning_bound_from_pdl` (`theorem`, wrapper): behavior-cloning error bound via algebraic rewrite of an assumed PDL bound to `H² ε` form.

## RLGeneralization.LinearMDP.EllipticalPotential

- `log_one_add_ge_div` (`lemma`, exact): log(1+x) ≥ x/(1+x) for x ≥ 0.
- `half_le_log_one_add` (`lemma`, exact): ½·x ≤ log(1+x) for x in [0,1].
- `log_two_ge_half` (`lemma`, exact): log 2 ≥ ½.
- `log_sum_eq_log_prod` (`lemma`, exact): telescoping identity for log sums.
- `min_le_two_mul_log_one_add` (`theorem`, exact): min(1, x) ≤ 2 log(1+x).
- `sum_sqrt_le_sqrt_mul_bound` (`theorem`, exact): Cauchy-Schwarz bound for sqrt sums.
- `elliptical_potential_conditional` (`theorem`, conditional): analytic core of the elliptical-potential lemma from a supplied log-sum bound.
- `gramMatrixM` (`def`): Gram matrix as a Mathlib `Matrix` type.
- `gramMatrix_symm` (`theorem`, exact): Gram matrix is symmetric.
- `outerProduct_symm` (`theorem`, exact): outer product is symmetric.
- `outerProductM_posSemidef` (`theorem`, exact): outer product is positive semidefinite (v^T(φφ^T)v = (φ·v)² ≥ 0).
- `elliptical_potential_from_det_bound` (`theorem`, conditional): elliptical potential with separated hypotheses — splits the opaque log-sum bound into (1) telescoping product = det and (2) det ≤ ((d+T)/d)^d.
- `gramMatrixM_trace_eq` (`theorem`, exact): trace of Gram matrix = d + ∑ squared norms.
- `gramMatrixM_trace_le_at_T` (`theorem`, exact): trace ≤ d + T when feature norms ≤ 1.
- `prod_le_arith_mean_pow` (`theorem`, exact): AM-GM: ∏ aᵢ ≤ ((∑ aᵢ)/d)^d for nonneg reals.
- `det_le_trace_div_pow_of_posSemidef` (`theorem`, exact): det(A) ≤ (trace(A)/d)^d for PSD matrices via spectral theorem + AM-GM.
- `featureMatrix` (`def`): feature matrix Φ with rows φ₁,...,φ_T.
- `gramMatrixM_eq_one_add_transpose_mul` (`theorem`, exact): Gram matrix decomposition Λ = I + ΦᵀΦ.
- `gramMatrixM_posSemidef` (`theorem`, exact): Gram matrix is PSD, via PosSemidef.diagonal + posSemidef_conjTranspose_mul_self + PosSemidef.add.
- `elliptical_potential_from_gram` (`theorem`, exact): full elliptical potential with only norm bound hypothesis. AM-GM det bound and PSD fully discharged; telescoping supplied by gramMatrixM_det_telescoping.
- `det_gramMatrixM_eq_prod_one_add_eigenvalues` (`theorem`, exact): det(I + ΦᵀΦ) = ∏(1 + eigenvalue of ΦΦᵀ) via Weinstein-Aronszajn identity and spectral decomposition.
- `gramMatrixM_det_telescoping` (`theorem`, exact): ∃ x_t ≥ 0, ∏(1+x_t) = det(Λ_{T+1}). Eigenvalue-based telescoping product.
- `elliptical_potential_unconditional` (`theorem`, exact): fully self-contained elliptical potential — ∃ x_t ≥ 0, ∑ min(1, x_t) ≤ 2d·log(1+T/d). No matrix-algebra hypotheses.

## RLGeneralization.LinearMDP.Regret

- `ucbvi_lin_regret_nonneg` (`theorem`, exact): linear cumulative regret is nonnegative.
- `ucbvi_lin_regret_from_bonus_hypotheses` (`theorem`, wrapper): UCBVI-Lin regret bound from supplied per-episode and total-bonus hypotheses.

## RLGeneralization.LQR.Basic

- `stageCost_nonneg` (`theorem`, exact): LQR stage cost is nonnegative from PSD cost matrices.

## Summary: What We Prove vs. What We Assume

The following table lists the headline results and their proof status.

| Result | Target Tag | Status | What Is Proved | What Remains as Hypothesis |
|--------|------------|--------|----------------|---------------------------|
| Value iteration convergence | Value iteration | `exact` | Constructs greedy policy via Banach fixed point; proves 2ε/(1-γ)-optimality after K iterations | Bellman-optimal Q* assumed to exist (standard) |
| Policy iteration convergence | Policy iteration | `exact` | Geometric convergence of the evaluated greedy sequence via sandwich inequality | Bellman-optimal Q* assumed; exact policy evaluation |
| Performance-difference lemma (PDL) | Normalized PDL | `exact` | Full infinite-horizon occupancy-measure PDL via truncation + limit; normalized occupancy sums to 1 | None beyond Bellman consistency |
| Simulation lemma | Simulation comparison | `weaker` | Kearns-Singh value-difference bound from reward/transition errors | Weaker constant than the stronger resolvent-based form |
| Minimax sample complexity | Minimax PAC core | `weaker` | Deterministic core with 1/(1-γ)² rate; end-to-end high-probability composition | Uses crude rate instead of sharp variance-sensitive bound |
| PAC generative model (Bernstein) | Bernstein PAC | `weaker` | O(log(1/δ)) sample complexity with Bernstein concentration; constructs empirical fixed points via Banach | Uses uniform variance p(1-p) ≤ 1/4 (exact per-entry variance preserved in intermediate theorems) |
| Hoeffding concentration (bandits) | Bandit Hoeffding | `exact` | Measure-theoretic Hoeffding in the bandit product space; union bound over K arms | None |
| UCB gap-dependent regret | UCB regret | `conditional` | Counting argument + algebraic composition: R_T ≤ ∑(8L/Δ + 2Δ) under UCB selection rule | UCB selection rule and concentration event taken as hypotheses |
| Elliptical potential lemma | Elliptical potential | `exact` | Fully self-contained via spectral theorem + AM-GM + PSD; no matrix-algebra hypotheses | None beyond feature norm bound |
| UCBVI bonus bound | UCBVI bonus | `exact` | Pigeonhole + Cauchy-Schwarz for visit-count bonus sums | None |
| UCBVI-Lin regret | UCBVI-Lin regret | `wrapper` | Final transitivity step from per-episode and total-bonus hypotheses | Optimism proof; per-episode bonus decomposition |
| CPI improvement | CPI improvement | `exact` | Resolvent-based mixture-policy improvement and monotonicity | None |
| Behavior cloning | Behavior cloning | `wrapper` | Algebraic rewrite to H²ε form | State-distribution mismatch argument |
| FQI error propagation | FQI propagation | `exact` | Contraction-style error propagation under per-step regression error | None |

### Design Decisions

**Bernstein uniform variance:** The PAC sample complexity (`pac_rl_generative_model_bernstein`) uses
the uniform bound p(1-p) ≤ 1/4 rather than the exact per-entry Bernoulli variance. This yields
a clean closed-form sample complexity N = O(log(K/δ)/c) with a single rate constant. The exact
per-entry variance is preserved in the intermediate theorem `generative_model_pac_bernstein`, which
retains the full `p(1-p)` term in the exponent — the uniform bound is only applied in the final
inversion step for a presentable sample complexity formula.

**UCB 2Δ constant:** The presentation form gives R_T ≤ ∑(8L/Δ + 2Δ) instead of a leaner asymptotic
∑(8L/Δ + Δ). The extra Δ comes from the integer ceiling in the counting argument: the canonical
threshold ⌈8L/Δ²⌉₊ + 1 ensures strict inequality for tie-breaking, and the ceiling adds at most
one extra unit. This is standard in formalized UCB proofs.

**UCBVI-Lin gap:** The elliptical potential lemma is fully proved (`elliptical_potential_unconditional`),
but connecting it to the UCBVI-Lin regret module requires a per-episode bonus decomposition that
factors the global potential bound into episode-level bonus sums. This structural bridge is the
remaining gap, not the potential lemma itself.

### Capstone Theorems (Recommended for Presentation)

The following are the strongest end-to-end results:

1. **`elliptical_potential_unconditional`** — Self-contained elliptical-potential theorem via spectral theory.
2. **`pdl_normalized`** — Normalized Kakade-Langford PDL with complete limit proof.
3. **`pac_rl_generative_model_bernstein`** — End-to-end PAC with O(log(1/δ)) Bernstein rate.
4. **`value_iteration_epsilon_optimal_constructed`** — Self-contained ε-optimal value iteration.
5. **`policy_iteration_convergence`** — Geometric convergence of policy iteration.
6. **`arm_mean_concentration` + `all_arms_concentration`** — Measure-theoretic Hoeffding in the bandit product space.
7. **`ucb_gap_dependent_regret_presentation`** — Composed UCB regret bound with pull-count counting lemma.

### Note on GenerativeModel Capstone Chain

`RLGeneralization.Concentration.GenerativeModel` contains ~12 progressive refinements of the minimax
value-gap theorem, each removing one hypothesis. The final capstones are:
- `pac_rl_generative_model_bernstein` — PAC with Bernstein log-rate
- `minimax_pac_bernstein_composed` — End-to-end Bernstein + minimax composition
- `pac_rl_generative_model_bernstein_existential` — Existential N₀ wrapper

The intermediate theorems (`minimax_from_generative_model`, `minimax_value_gap_high_probability`, etc.)
are stepping stones that document the progressive discharge of hypotheses. They are correct but
superseded by the capstones above.

## Coverage Note

This catalog is theorem-centered, but the source code remains organized by
topic/module. That is intentional:

- modules are the right unit for reuse and extension,
- theorems are the right unit for trust, auditing, and benchmark labeling.
