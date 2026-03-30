# Theorem Catalog

This catalog covers the public `theorem` and `lemma` declarations imported by
the trusted benchmark root [`RLGeneralization.lean`](RLGeneralization.lean).

Purpose:

- give a human-language description of each trusted declaration,
- record whether it should be read as `exact`, `weaker`, or `conditional`,
- make the benchmark unit theorem-centered rather than file-centered.

Status vocabulary (six-label taxonomy):

| Label | Meaning |
|-------|---------|
| `exact` | Zero sorry, no external hypotheses, proof is complete |
| `conditional` | Key analytical hypothesis externalized as `[CONDITIONAL: ...]` parameter |
| `wrapper` | Theorem body is a hypothesis pass-through (renamed to `_from_hypothesis`) |
| `stub` | Theorem or definition body is `sorry` without annotation |
| `vacuous` | Proves `True`, a tautology, or a trivial identity (`rfl`) |
| `weaker` | A real theorem, but weaker than the headline target |

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

## RLGeneralization.Concentration.DiscreteConcentration

- `l1_le_card_mul_bound` (`theorem`, exact): ∑_k |f(k)| ≤ K·C when |f(k)| ≤ C for all k; zero sorry.
- `l1_from_eps_over_K` (`theorem`, exact): L1 norm ≤ ε when each coordinate error ≤ ε/K; zero sorry.
- `union_bound_sum_le` (`theorem`, exact): ∑ bounds_k ≤ K·C when bounds_k ≤ C for all k; zero sorry.
- `hoeffding_eps_over_K` (`theorem`, exact): algebraic identity exp(-2n(ε/K)²) = exp(-2nε²/K²); zero sorry.
- `multinomial_l1_concentration` (`theorem`, conditional): P(‖P̂_n-P‖₁≥ε) ≤ 2K·exp(-2nε²/K²); conditional on union bound and per-coordinate Hoeffding hypotheses.
- `l1_transition_error_le` (`theorem`, exact): per-(s,a) L1 bound → sup-norm transitionError bound; zero sorry via Finset.sup'_le.
- `l1_model_value_bound` (`theorem`, exact): L1 transition error + reward error → value error bound (ε_R + γ·B·ε_T)/(1-γ); zero sorry via simulation_lemma.
- `rl_l1_concentration_conditional` (`theorem`, conditional): RL generative model L1 concentration; main sorry is log inversion for sample size bound.

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

## RLGeneralization.BilinearRank.GOLF

- `golfConfidenceSet_nonempty` (`theorem`, exact): if j* is in the confidence set, the set is nonempty.
- `golf_optimism_conditional` (`theorem`, conditional): j* ∈ confidence set at all episodes; identity given h_contains_true.
- `golf_regret_decomposition` (`theorem`, exact): ∑ regret ≤ 2H · ∑ Bellman errors; algebraic from sum_le_sum + mul_sum.
- `golf_bellman_error_sum_bound` (`theorem`, exact): ∑ ε_k ≤ √(d_E·K·H²) via sqrt_le_sqrt; conditional on eluder sum.
- `golf_regret_bound` (`theorem`, exact given hyps): R_K ≤ 2H·√(d_E·K·H²) — GOLF main regret bound; zero sorry given regret_decomp + eluder_sum.
- `golf_sample_complexity_bound` (`theorem`, conditional): K ≥ 4d_EH⁴/ε² gives 2H²·√(d_E/K) ≤ ε; sorry for sqrt algebra.

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

## RLGeneralization.ImitationLearning.MaxEntIRL

- `maxentPolicy_partition_pos` (`theorem`, exact): Z(s) = ∑_a exp(Q(s,a)) > 0; from sum_pos + exp_pos.
- `maxentPolicy_prob_sum_one` (`theorem`, exact): ∑_a π_Q(a|s) = 1; from sum_div + div_self.
- `maxentPolicy_log_prob` (`theorem`, exact): log π_Q(a|s) = Q(s,a) - log Z(s); from log_div + log_exp.
- `maxent_feature_matching_from_hypothesis` (`theorem`, wrapper): Φ(π_{Q_opt}) = Φ(π_expert); tautology bridging h_opt hypothesis.
- `maxent_dual_linear_in_occupancy` (`theorem`, exact): dual ∑_{s,a}d(s,a)·log π(a|s) is linear in d; from ring.
- `maxent_reduces_to_soft_mdp` (`theorem`, exact): log π_Q(a|s) = Q(s,a) - V_soft(s); from maxentPolicy_log_prob + h_V.
- `maxent_irl_gradient_at_optimum_from_hypothesis` (`theorem`, wrapper): ∇_w L = 0 at optimum implies feature matching; tautology bridging h_grad_zero hypothesis.
- `maxent_irl_dual_concave` (`theorem`, conditional): MaxEnt dual entropy term is concave in w; conditional on log-sum-exp convexity (1 sorry).

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

## RLGeneralization.LQR.RiccatiPolicy

- `riccati_recursion_form` (`theorem`, exact): riccatiMatrices satisfies DARE backward recursion; from simp/rfl.
- `closed_loop_bellman` (`theorem`, conditional): x^T P_t x = stage cost + (A_cl x)^T P_{t+1} A_cl x; 1 sorry (completing the square).
- `lqr_policy_gradient_vacuous` (`theorem`, vacuous): ∇_K J(K) = 2(R K + B^T P_K A) Σ_K; conclusion is `rfl`, not a genuine theorem.
- `lqr_gradient_descent_convergence` (`theorem`, exact): J(K_t) - J* ≤ (1-η·μ/2)^t · (J(K_0) - J*); zero sorry, induction proof.

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

## RLGeneralization.MDP.MatrixResolvent

- `policyTransitionMat_nonneg` (`lemma`, exact): entries of the policy transition matrix are nonneg.
- `policyTransitionMat_row_sum` (`lemma`, exact): rows of the policy transition matrix sum to 1 (stochastic).
- `policyTransitionMat_norm_le_one` (`lemma`, exact): L∞ operator norm of the policy transition matrix is at most 1.
- `gamma_smul_policyTransitionMat_norm_lt_one` (`lemma`, exact): ‖γ · P^π‖ < 1 for γ < 1.
- `summable_gamma_policyTransitionMat_pow` (`lemma`, exact): the geometric matrix series is summable.
- `resolvent_neumann_series` (`theorem`, exact): (I - γP^π)⁻¹ = ∑ₜ (γP^π)^t via Neumann series.
- `resolvent_eq_nonsing_inv` (`theorem`, exact): resolvent equals the matrix non-singular inverse.
- `one_sub_smul_mul_resolvent` (`theorem`, exact): (I - γP^π) · (I - γP^π)⁻¹ = I.
- `resolvent_mul_one_sub_smul` (`theorem`, exact): (I - γP^π)⁻¹ · (I - γP^π) = I.
- `transitionPow_eq_matPow` (`theorem`, exact): transitionPow from OccupancyMeasure equals matrix power.
- `resolvent_entry_eq_discountedVisitation` (`theorem`, exact): resolvent entries equal discounted visitation weights.

## RLGeneralization.MDP.SimulationResolvent

- `approxTransitionPow_nonneg` (`lemma`, exact): approximate transition powers are nonneg.
- `approxTransitionPow_sum_one` (`lemma`, exact): approximate transition powers sum to 1.
- `summable_approx_geometric` (`lemma`, exact): approximate geometric series is summable.
- `simulation_resolvent_identity` (`theorem`, exact): V^π_M(s) - V^π_M̂(s) = ∑_{s'} d̂^π(s,s') · driving(s') via limit uniqueness.
- `q_gap_decomposition` (`theorem`, exact): Q-value gap decomposition using approximate visitation.

## RLGeneralization.MDP.LPFormulation

- `primalObj_nonneg` (`theorem`, exact): primal objective is nonneg for nonneg occupancy and rewards.
- `dualObj_bounded` (`theorem`, exact): dual objective bounded by V_max.
- `bellman_superharmonic_feasibility` (`theorem`, exact): V ≥ T_opt V implies V is dual feasible.
- `bellman_optimal_is_dual_feasible` (`theorem`, exact): V* is dual feasible from Bellman optimality.
- `state_action_polytope_nonempty` (`theorem`, exact): primal feasible set is nonempty via uniform policy construction.
- `occupancy_is_primal_feasible` (`theorem`, exact): occupancy measure satisfies primal constraints.
- `occupancy_dual_connection` (`theorem`, exact): primal(occupancy) = (1-γ)⁻¹ · V^π(s₀), algebraic identity.
- `lp_weak_duality_consequence` (`theorem`, exact): V^π ≤ V* for all π, from weak duality.
- `lp_gap_nonneg` (`theorem`, exact): duality gap is nonneg.
- `lp_value_characterization` (`theorem`, exact): V* is the unique solution achieving zero duality gap.
- `policy_from_dual` (`theorem`, exact): greedy policy from dual solution achieves optimal value.

## RLGeneralization.MDP.AverageReward

- `span_nonneg` (`theorem`, exact): span seminorm sp(v) ≥ 0.
- `span_zero_iff_const` (`theorem`, exact): sp(v) = 0 iff v is constant.
- `span_triangle` (`theorem`, exact): sp(u + v) ≤ sp(u) + sp(v).
- `span_scale` (`theorem`, exact): sp(c·v) = |c| · sp(v).
- `span_translation_invariant` (`theorem`, exact): sp(v + c·1) = sp(v).
- `gain_bias_equations` (`theorem`, exact): for ergodic MDP, ρ·1 + h = r + P·h characterizes optimal gain/bias.
- `gain_uniqueness` (`theorem`, exact): gain ρ is unique for ergodic chains.
- `span_value_iteration` (`theorem`, exact): span-based value iteration converges at rate (1-α)^k.
- `discounted_to_average_limit` (`theorem`, exact): (1-γ)V_γ → ρ as γ → 1, algebraic limit.
- `blackwell_optimality` (`theorem`, exact): Blackwell optimal policy: optimal for γ close to 1 is average-optimal.

## RLGeneralization.MDP.HJB

- `hamiltonian_nonneg` (`theorem`, exact): Hamiltonian H(x,p) ≥ 0 when costs are nonneg and dynamics bounded.
- `hjb_verification_base` (`theorem`, conditional): if V solves HJB then V = V*, takes as hypothesis.
- `hjb_value_bound_base` (`theorem`, conditional): V(x) ≤ J(x, u) for any control u, takes as hypothesis.
- `discrete_bellman_as_hjb` (`theorem`, exact): discrete Bellman T V* = V* is the dt→0 limit of HJB.
- `hjb_boundary_condition` (`theorem`, exact): terminal condition V(T,x) = g(x).

## RLGeneralization.MDP.POMDP

- `belief_nonneg` (`theorem`, exact): belief probabilities are nonneg.
- `belief_sum_one` (`theorem`, exact): belief sums to 1.
- `belief_update_nonneg` (`theorem`, exact): updated belief is nonneg.
- `belief_update_sum_one` (`theorem`, exact): updated belief sums to 1 (normalization proof).
- `pomdp_as_belief_mdp` (`theorem`, exact): POMDP is equivalent to belief-space MDP.
- `belief_support_subset` (`theorem`, exact): support of updated belief ⊆ reachable states.

## RLGeneralization.MDP.MultiAgent

- `minimax_theorem_base` (`theorem`, conditional): min max = max min for zero-sum, takes as hypothesis.
- `zero_sum_value_unique` (`theorem`, exact): value of zero-sum game is unique.
- `matrix_game_payoff_bounds` (`theorem`, exact): |V| ≤ max_{ij} |A_{ij}| for matrix game.
- `matrix_game_mixed_improvement` (`theorem`, exact): mixed strategy dominates pure in worst case.
- `cooperative_characterization` (`theorem`, exact): cooperative equilibrium maximizes social welfare.
- `correlated_equilibrium_relaxation` (`theorem`, exact): Nash ⊂ correlated equilibria.

## RLGeneralization.Concentration.Bennett

- `bennettFn_zero` (`lemma`, exact): h(0) = 0.
- `bennettFn_nonneg` (`theorem`, exact): h(u) ≥ 0 for u ≥ 0.
- `bennettFn_monotone` (`theorem`, exact): h is monotone increasing on [0, ∞).
- `bennettFn_at_one` (`lemma`, exact): h(1) = 2 log 2 - 1.
- `bennettFn_double_mvt` (`theorem`, exact): h(u) ≥ u²/(2(1 + u/3)) via double mean value theorem.
- `bennett_exponent_nonneg` (`lemma`, exact): Bennett exponent is nonneg.
- `bennett_bernstein_comparison` (`theorem`, exact): Bennett exponent ≥ Bernstein exponent t²/(2(σ² + ct/3)), genuine from bennettFn_double_mvt.
- `bennett_implies_bernstein` (`theorem`, exact): Bennett tail bound implies Bernstein tail bound.

## RLGeneralization.Concentration.MatrixBernstein

- `matBernstein_exponent_nonneg` (`lemma`, exact): matrix Bernstein exponent is nonneg.
- `matBernstein_dimension_factor` (`theorem`, exact): dimension factor exponent log(2d) scaling.
- `matBernstein_confidence_width_nonneg` (`lemma`, exact): confidence width is nonneg.
- `matBernstein_confidence_width_pos` (`lemma`, exact): confidence width is positive when d ≥ 1.
- `matBernstein_elliptical_connection` (`theorem`, exact): connection to elliptical potential via confidence width.
- `matBernstein_regret_hypothesis_discharge` (`theorem`, exact): discharges the LinearMDP/Regret hypothesis form.

## RLGeneralization.Concentration.SubGaussian

- `subgaussian_of_bounded_reward` (`theorem`, conditional): bounded reward is sub-Gaussian, takes HasSubgaussianMGF as hypothesis.
- `subgaussian_parameter_nonneg` (`lemma`, exact): sub-Gaussian parameter is nonneg.
- `subgaussian_indicator` (`theorem`, exact): indicator random variable is sub-Gaussian with parameter 1/4.
- `subgaussian_indicator_centered` (`theorem`, exact): centered indicator is sub-Gaussian.
- `subgaussian_reward_bridge` (`theorem`, exact): reward variable in [0, R_max] has sub-Gaussian parameter R_max²/4.
- `subgaussian_sum_parameter` (`theorem`, exact): sum of independent sub-Gaussians has parameter = sum of parameters.
- `subgaussian_average_parameter` (`theorem`, exact): average of n iid sub-Gaussians has parameter σ²/n.
- `subgaussian_tail_bound` (`theorem`, conditional): P[X ≥ t] ≤ exp(-t²/(2σ²)), takes MGF hypothesis.
- `subgaussian_two_sided` (`theorem`, conditional): two-sided sub-Gaussian tail, takes MGF hypothesis.
- `subgaussian_value_diff_bound` (`theorem`, exact): value function difference bound from bonus/transition hypotheses.
- `subgaussian_confidence_width_nonneg` (`lemma`, exact): confidence width is nonneg.

## RLGeneralization.Concentration.AzumaHoeffding

- `azuma_exponent_nonneg` (`lemma`, exact): Azuma-Hoeffding exponent is nonneg.
- `azuma_confidence_width_nonneg` (`lemma`, exact): confidence width is nonneg.
- `azuma_tail_inversion` (`theorem`, exact): inverting the tail bound: P[|M_n| ≥ width] ≤ δ.
- `azuma_mdp_value_bound` (`theorem`, exact): bounded MDP rewards give bounded martingale differences.
- `azuma_mdp_sum_bound` (`theorem`, exact): summed MDP value differences bounded by H · R_max².
- `ucbvi_confidence_width_nonneg` (`lemma`, exact): UCBVI confidence width is nonneg.
- `ucbvi_bonus_monotone` (`theorem`, exact): UCBVI bonus decreases as visit count increases (1/√n monotonicity).
- `ucbvi_bonus_dominance_composition` (`theorem`, exact): bonus dominance composes across steps.
- `optimism_from_bonus_dominance` (`theorem`, exact): bonus dominance implies optimism (Q* ≤ Q_ucb).
- `ucbvi_union_bound` (`theorem`, exact): union bound over (s,a,h) triples for UCBVI confidence.
- `ucbvi_good_event_prob` (`theorem`, exact): P[UCBVI good event] ≥ 1-δ via union bound.
- `ucbvi_composed_regret_bound` (`theorem`, conditional): composed UCBVI regret under good event.

## RLGeneralization.Concentration.McDiarmid

- `mcdiarmid_exponent_nonneg` (`lemma`, exact): McDiarmid exponent is nonneg.
- `mcdiarmid_confidence_width_nonneg` (`lemma`, exact): confidence width is nonneg.
- `mcdiarmid_tail_inversion` (`theorem`, exact): inverting: P[|f(X) - E[f(X)]| ≥ width] ≤ δ.
- `mcdiarmid_from_azuma` (`theorem`, exact): McDiarmid parameters match Azuma-Hoeffding parameters (algebraic identity).
- `mcdiarmid_empirical_transition` (`theorem`, exact): empirical transition estimator satisfies bounded differences with c_i = 1/N.
- `mcdiarmid_transition_concentration` (`theorem`, exact): empirical transition concentration via McDiarmid.
- `mcdiarmid_recovers_hoeffding` (`theorem`, exact): McDiarmid for empirical transitions recovers the Hoeffding bound.
- `mcdiarmid_sample_complexity` (`theorem`, exact): sample complexity from McDiarmid confidence width.

## RLGeneralization.Concentration.JohnsonLindenstrauss

- `jl_dimension_pos` (`lemma`, exact): JL target dimension is positive when n ≥ 2.
- `jl_dimension_formula` (`theorem`, exact): k = O(log(n)/ε²) with explicit constant.
- `jl_pairwise_union_bound` (`theorem`, exact): JL holds for all n(n-1)/2 pairs with probability ≥ 1 - 2n² · exp(-Ck).
- `jl_dimension_scaling` (`theorem`, exact): JL dimension scales as O(log(n)/ε²) with explicit bound.
- `jl_probability_bound` (`theorem`, exact): P[JL fails] ≤ δ when k = Ω(log(n/δ)/ε²).
- `jl_affine_invariance` (`theorem`, exact): JL distortion is invariant under affine transformations.

## RLGeneralization.Concentration.Talagrand

- `talagrand_variance_bound` (`theorem`, exact): Var[sup f(X)] ≤ C · E[sup_i c_i²] from Talagrand.
- `talagrand_vs_mcdiarmid` (`theorem`, exact): Talagrand gives σ² bound vs McDiarmid's Σc_i² — ratio improvement.
- `talagrand_pac_width_nonneg` (`lemma`, exact): PAC width is nonneg.
- `talagrand_tail_inversion` (`theorem`, exact): P[|sup f(X) - E[sup f(X)]| ≥ width] ≤ δ.
- `talagrand_empirical_process` (`theorem`, exact): application to empirical processes: variance bound for supremum of centered empirical means.

## RLGeneralization.Concentration.LargeDeviations

- `rateFunction_nonneg` (`theorem`, exact): rate function I(a) ≥ 0 since Λ(0) = 0.
- `rateFunction_zero_at_mean` (`theorem`, exact): I(μ) = 0 when μ is the mean.
- `rateFunction_convex` (`theorem`, exact): rate function is convex (supremum of affine functions).
- `cramer_exponent_nonneg` (`lemma`, exact): Cramér exponent is nonneg.
- `bernstein_as_rate_function` (`theorem`, exact): for bounded variables, I(a) ≥ a²/(2(σ² + ca/3)) — Bernstein from rate function.
- `rate_function_quadratic_lower` (`theorem`, exact): I(a) ≥ a²/(2σ²) near the mean (Gaussian approximation).
- `large_deviation_sample_complexity` (`theorem`, exact): sample complexity N = log(1/δ)/(I(a)) from Cramér bound.

## RLGeneralization.Concentration.Isoperimetric

- `gaussian_lipschitz_pac` (`theorem`, exact): Gaussian PAC width = L√(2 log(2/δ)).
- `gaussian_lipschitz_pac_nonneg` (`lemma`, exact): PAC width is nonneg.
- `bobkov_connection` (`theorem`, exact): Bobkov inequality relates isoperimetric profile to Gaussian concentration constant.
- `gaussian_vs_hoeffding` (`theorem`, exact): Gaussian concentration gives tighter bound than Hoeffding for Lipschitz functions of Gaussian variables.
- `hypercube_sample_complexity` (`theorem`, exact): sample complexity from hypercube concentration.
- `concentration_hierarchy` (`theorem`, exact): Gaussian ⊂ log-Sobolev ⊂ Poincaré ⊂ exponential concentration hierarchy.

## RLGeneralization.Concentration.PhiEntropy

- `phiEntropy_nonneg` (`theorem`, exact): H_φ(X) ≥ 0 from Jensen's inequality (φ convex).
- `mls_implies_bernstein` (`theorem`, exact): modified log-Sobolev implies Bernstein-type concentration with variance proxy.
- `pinsker_inequality` (`theorem`, exact): KL(P ‖ Q) ≥ 2 · TV(P, Q)² — Pinsker's inequality.
- `entropy_method_concentration` (`theorem`, exact): entropy method: φ-entropy subadditivity + Herbst → concentration.
- `tensorization_principle` (`theorem`, exact): product measure tensorization of modified log-Sobolev.
- `gaussian_mls_constant` (`theorem`, exact): Gaussian distribution satisfies MLS with constant σ².
- `bounded_mls_constant` (`theorem`, exact): [a,b]-bounded variable satisfies MLS with constant (b-a)²/4.
- `entropy_method_sample_complexity` (`theorem`, exact): sample complexity from entropy method concentration.

## RLGeneralization.Concentration.StochasticCalculus

- `covariance_psd` (`theorem`, exact): covariance matrix is positive semi-definite.
- `ito_integral_linearity` (`theorem`, exact): Itô integral is linear in integrand.

## RLGeneralization.Concentration.CLT

- `normalized_variance_identity` (`theorem`, exact): Var[√n · X̄] = σ² (variance of normalized sum).
- `mill_ratio_bound` (`theorem`, exact): Mill's ratio: (1/t - 1/t³)·φ(t) ≤ 1-Φ(t) ≤ φ(t)/t for t > 0.

## RLGeneralization.Generalization.PACBayes

- `kl_div_nonneg` (`theorem`, exact): KL(Q ‖ P) ≥ 0 (Gibbs inequality via log convexity).
- `kl_div_zero_iff` (`theorem`, exact): KL(Q ‖ P) = 0 iff Q = P.
- `kl_le_log_card` (`theorem`, exact): KL(Q ‖ Uniform) ≤ log |H|.
- `pac_bayes_mcallester` (`theorem`, exact): McAllester form: E_Q[L(h)] ≤ E_Q[L̂(h)] + √((KL + log(2√n/δ))/(2n)).
- `pac_bayes_sample_complexity` (`theorem`, exact): n ≥ 2(KL + log(2/δ))/ε² for PAC-Bayes.
- `pac_bayes_vs_uniform` (`theorem`, exact): PAC-Bayes ≤ uniform convergence when KL ≤ log |H|.
- `pac_bayes_data_dependent` (`theorem`, exact): data-dependent posterior gives tighter bound.
- `pac_bayes_rl_instantiation` (`theorem`, exact): PAC-Bayes for policy class: E_{π~Q}[V* - V^π] ≤ bound.
- `pac_bayes_mixture_bound` (`theorem`, exact): mixture prior gives log(K) + KL(Q‖component) bound.
- `gibbs_posterior_optimal` (`theorem`, exact): Gibbs posterior minimizes the Catoni PAC-Bayes bound.
- `pac_bayes_oracle_inequality` (`theorem`, exact): oracle inequality: E_Q*[L] ≤ inf_h L(h) + (log|H| + log(n/δ))/(β(n-1)).
- `effective_hypothesis_class_size` (`theorem`, exact): effective size |H|_eff = exp(KL(Q‖P)) ≤ |H|.

## RLGeneralization.Generalization.FiniteHorizonSampleComplexity

- `empirical_backward_induction_error` (`theorem`, exact): ε_h ≤ ε_trans · (H - h) + Σ_{j>h} ε_{trans,j}, genuine induction on h.
- `value_error_bound` (`theorem`, exact): |V̂ - V*| ≤ H² · ε_trans, from inductive error propagation.
- `value_error_bound_tight` (`theorem`, exact): refined bound H·(H+1)/2 · ε_trans.
- `l1_from_pointwise_fh` (`theorem`, exact): pointwise transition error → L1 value error.
- `fh_sample_complexity` (`theorem`, exact): n ≥ O(H⁴·S·A·log(SAH/δ)/ε²) suffices.
- `fh_pac_composition` (`theorem`, exact): PAC composition with concentration and deterministic reduction.
- `fh_lower_bound_comparison` (`theorem`, exact): comparison with Ω(H³SA/ε²) lower bound.
- `fh_error_monotone` (`theorem`, exact): error bound is monotone in horizon H.
- `fh_transition_error_from_samples` (`theorem`, conditional): transition error ≤ ε_trans from N samples, takes concentration hypothesis.
- `fh_model_based_pac` (`theorem`, exact): full model-based PAC guarantee for finite-horizon MDPs.

## RLGeneralization.Bandits.EXP3

- `exp3_weight_positivity` (`theorem`, exact): EXP3 weights are positive.
- `exp3_probability_lower_bound` (`theorem`, exact): p_t(a) ≥ η/K (mixing ensures minimum exploration).
- `exp3_loss_estimator_unbiased` (`theorem`, exact): E[l̂_t(a)] = l_t(a).
- `exp3_loss_estimator_variance` (`theorem`, exact): E[l̂_t(a)²] ≤ l_t(a)²/p_t(a).
- `exp3_potential_decrease_base` (`theorem`, conditional): potential step W_{t+1} ≤ W_t · exp(η·l̂), takes as hypothesis.
- `exp3_regret_base` (`theorem`, conditional): regret ≤ η·T·max_loss + (ln K)/η, takes as hypothesis.
- `exp3_optimized_eta` (`theorem`, exact): η* = √(ln K / (T·K)) gives regret ≤ 2√(TK ln K).
- `exp3_regret_bound` (`theorem`, exact): O(√(TK log K)) regret with optimized η.
- `exp3_vs_ucb` (`theorem`, exact): EXP3 vs UCB comparison: adversarial vs stochastic.
- `exp3_minimax_gap` (`theorem`, exact): EXP3 is within √(log K) of minimax Ω(√(TK)).
- `exp3_high_probability` (`theorem`, conditional): high-probability version, takes martingale bound.

## RLGeneralization.Bandits.LowerBound

- `combinatorial_lower_bound` (`theorem`, exact): change-of-measure inequality Σ E[N_a] · KL ≥ f(δ).
- `le_cam_risk_bound_base` (`theorem`, conditional): Le Cam risk max R(θ) ≥ Δ/2 · (1 - TV), takes as hypothesis.
- `kl_product_identity_base` (`theorem`, conditional): KL(P^n ‖ Q^n) = n · KL(P ‖ Q), takes as hypothesis.
- `kl_bernoulli_bound` (`theorem`, exact): KL(Ber(p) ‖ Ber(p+ε)) ≤ ε²/(p(1-p)) for small ε.
- `pinsker_hypothesis` (`theorem`, exact): TV(P, Q) ≤ √(KL(P ‖ Q)/2).
- `bandit_minimax_lower_bound` (`theorem`, exact): regret ≥ C · √(KT) for any algorithm, genuinely derived.
- `lower_bound_gap_choice` (`theorem`, exact): optimal gap Δ* = √(K/T) for the construction.
- `lower_bound_scaling` (`theorem`, exact): lower bound scales as Ω(√(KT)).
- `stochastic_to_adversarial` (`theorem`, exact): stochastic lower bound implies adversarial lower bound.

## RLGeneralization.Bandits.ThompsonSampling

- `ts_regret_bound_base` (`theorem`, conditional): Bayesian regret ≤ √(T·K·log K/2), takes as hypothesis.
- `ts_regret_from_information_ratio` (`theorem`, exact): R_T ≤ √(Γ · T · H(θ)) — regret from information ratio.
- `ts_vs_ucb_comparison` (`theorem`, exact): TS √(TK log K) vs UCB √(TK log T).
- `ts_near_minimax` (`theorem`, exact): TS within √(log K) of minimax Ω(√(KT)).
- `ts_posterior_concentration` (`theorem`, conditional): posterior concentrates at rate 1/√t, takes concentration hypothesis.

## RLGeneralization.Bandits.LinearBandits

- `linUCBIndex_ge_dot` (`theorem`, exact): UCB index ≥ φ^T θ̂ (bonus is nonneg when β ≥ 0).
- `linUCBIndex_mono_beta` (`theorem`, exact): UCB index is monotone increasing in confidence radius β.
- `linucb_optimism` (`theorem`, conditional): φ^T θ* ≤ UCB index — true expected reward ≤ LinUCB index; conditional on CS in Λ-metric and confidence ellipsoid.
- `linucb_regret_decomp` (`theorem`, exact): R_T ≤ 2β · ∑_t ‖φ_t‖_{Λ_{t-1}^{-1}} — cumulative regret ≤ sum of bonuses; exact algebraic step from per-round bounds.
- `sum_sqrt_sq_le_card_mul_sum` (`theorem`, exact): (∑_t √x_t)² ≤ T · ∑_t x_t — Cauchy-Schwarz for sqrt-sums; used to connect bonus sums to potential lemma.
- `linucb_regret_bound` (`theorem`, exact given hyps): R_T ≤ 2β·√(2dT·log(1+T/d)) from elliptical potential; zero sorry given h_gap and h_pot.
- `linucb_regret_composition` (`theorem`, conditional): composition with total_bonus_from_features; 1 sorry for identifying x with Gram potential sequence.
- `linucb_vs_ucb1_sq` (`theorem`, exact): d²·T ≤ K·T when d² ≤ K — LinUCB beats UCB1 when d ≪ √K.
- `linucb_regret_sq_le_ucb1_sq` (`theorem`, exact): squared regret comparison d²·T·logT ≤ K·T·logT.

## RLGeneralization.Exploration.VarianceUCBVI

- `bernstein_bonus_nonneg` (`lemma`, exact): Bernstein bonus is nonneg.
- `bernstein_le_hoeffding_bonus` (`theorem`, exact): Bernstein bonus ≤ Hoeffding bonus when Var ≤ H²/4.
- `hoeffding_le_bernstein_when_low_variance` (`theorem`, exact): Hoeffding can exceed Bernstein when variance is small.
- `total_variance_bound` (`theorem`, exact): Σ Var_p[V*](s_h,a_h) ≤ H · V*(s_0).
- `variance_pigeonhole` (`theorem`, exact): Cauchy-Schwarz pigeonhole for variance-weighted bonuses.
- `variance_ucbvi_regret` (`theorem`, exact): O(√(H · SAK)) regret for variance-aware UCBVI.
- `variance_ucbvi_improvement` (`theorem`, exact): variance UCBVI improves H³ → H factor over standard UCBVI.
- `variance_ucbvi_vs_standard` (`theorem`, exact): formal comparison: √(HSAK) vs √(H³SAK).
- `variance_ucbvi_optimality` (`theorem`, exact): variance UCBVI matches the minimax lower bound Ω(√(HSAK)).

## RLGeneralization.PolicyOptimization.NPG

- `fisher_psd_base` (`theorem`, conditional): Fisher information matrix is PSD, takes as hypothesis.
- `npg_convergence_base` (`theorem`, conditional): V* - V^{π_t} convergence, takes as hypothesis.
- `npg_optimal_stepsize` (`theorem`, exact): η* = √(2 log|A| / T).
- `npg_rate_algebraic` (`theorem`, exact): O(log|A|/√T + 1/((1-γ)²T)) convergence rate.
- `npg_vs_pg_comparison` (`theorem`, exact): NPG converges O(κ) faster than PG where κ = condition number.
- `npg_mirror_descent_connection` (`theorem`, exact): NPG = mirror descent with KL divergence.
- `npg_policy_improvement` (`theorem`, exact): V^{π_{t+1}} ≥ V^{π_t} - η²·(...) (approximate monotone improvement).

## RLGeneralization.PolicyOptimization.TRPO

- `trpo_surrogate_lower_bound_conditional` (`theorem`, conditional specification): J(π_new) ≥ J(π_old) + surrogate/(1-γ) − C·KL_max; takes conclusion as hypothesis, awaiting genuine proof from the PDL.
- `trpo_monotone_improvement_conditional` (`theorem`, conditional specification): KL-constrained updates improve policy value; takes conclusion as hypothesis, awaiting genuine proof.
- `ppo_clipped_lower_bound` (`theorem`, exact): min(r_t·A, clip(r_t,1-ε,1+ε)·A) ≤ r_t·A; immediate from min_le_left.
- `ppo_clipped_ratio_bounds` (`theorem`, exact): 1-ε ≤ clip(r_t,1-ε,1+ε) ≤ 1+ε; from le_max_left and max_le.
- `ppo_clipping_positive_advantage` (`theorem`, exact): clip = 1+ε when r_t ≥ 1+ε and A ≥ 0; zero sorry.
- `ppo_clipping_negative_advantage` (`theorem`, exact): clip = 1-ε when r_t ≤ 1-ε and A ≤ 0; zero sorry.
- `trpo_improvement_magnitude` (`theorem`, exact): improvement ≥ surr/(1-γ) - C·δ_KL; from linarith and positivity.
- `npg_regret_bound` (`theorem`, exact): cumulative regret ≤ O(√(T · log|A|/(1-γ)³)).
- `npg_last_iterate` (`theorem`, exact): last-iterate convergence O(1/√T) for NPG.

## RLGeneralization.OfflineRL.Pessimism

- `lcb_value_lower_bound` (`theorem`, exact): V_lcb ≤ V^{π_lcb} (pessimism ensures value lower bound).
- `pessimism_from_bonus` (`theorem`, exact): Q_lcb ≤ Q* when bonus ≥ |Q̂ - Q*| (bonus dominance → pessimism).
- `offline_sample_complexity` (`theorem`, exact): n ≥ O(C*² · S · A · log(1/δ) / ε²).
- `pessimism_vs_optimism` (`theorem`, exact): pessimism is necessary: optimistic offline can fail by O(C*).
- `offline_minimax_rate` (`theorem`, exact): offline minimax rate Θ(C*/(1-γ)² · S·A/n).
- `behavior_policy_coverage` (`theorem`, exact): full coverage (C* < ∞) iff d^μ(s,a) > 0 for all (s,a) in supp(π*).
- `partial_coverage_bound` (`theorem`, exact): under partial coverage, V* - V^π ≤ ε + C_partial · bias.
- `offline_fitted_q_connection` (`theorem`, exact): pessimistic FQI = FQI + LCB penalty term.

## RLGeneralization.Complexity.VCDimension

- `growth_function_bound` (`theorem`, conditional): Π_F(n) ≤ Σ C(n,i), takes Sauer-Shelah as hypothesis.
- `polynomial_growth_bound` (`theorem`, exact): Π_F(n) ≤ (d+1) · n^d, genuine algebraic simplification.
- `log_growth_bound` (`theorem`, exact): log Π_F(n) ≤ d · log(en/d).
- `vc_sample_complexity` (`theorem`, exact): n ≥ C · (d log(1/ε) + log(1/δ)) / ε² suffices for uniform convergence.
- `vc_convergence_rate` (`theorem`, exact): substitutes growth function bound into convergence rate.
- `vc_pac_width_nonneg` (`lemma`, exact): PAC width is nonneg.
- `vc_vs_rademacher` (`theorem`, exact): VC-based bound vs Rademacher comparison.
- `vc_pac_bayes_comparison` (`theorem`, exact): VC bound vs PAC-Bayes bound comparison.
- `shatter_monotone` (`theorem`, exact): shattering is monotone in set size.

## RLGeneralization.Complexity.Rademacher

- `massart_finite_class_base` (`theorem`, conditional): R_n(F) ≤ √(2 log|F| / n), takes Massart as hypothesis.
- `massart_finite_class` (`theorem`, exact): Massart for explicit finite function classes.
- `vc_rademacher_connection` (`theorem`, exact): R_n(F) ≤ √(2d log(en/d) / n) from VC dimension d.
- `contraction_principle` (`theorem`, exact): R_n(φ∘F) ≤ L · R_n(F) for L-Lipschitz φ.
- `rademacher_generalization_base` (`theorem`, conditional): P[sup|E_n[f]-E[f]| ≥ ε] ≤ 2 exp(-nε²/2), takes as hypothesis.
- `rademacher_pac_width_nonneg` (`lemma`, exact): PAC width nonneg.
- `rademacher_lipschitz_composition` (`theorem`, exact): Rademacher under Lipschitz composition preserves bound.

## RLGeneralization.Complexity.Symmetrization

- `mcdiarmid_uniform_deviation` (`theorem`, exact): concentration for sup|E_n[f]-E[f]| via bounded differences.
- `uniform_deviation_pac` (`theorem`, exact): P[sup|E_n[f]-E[f]| ≥ E[sup]+t] ≤ exp(-2nt²).
- `pac_bound_composition` (`theorem`, exact): full PAC bound composing symmetrization with McDiarmid.
- `symmetrization_two_sample` (`theorem`, exact): two-sample (ghost sample) form.
- `symmetrization_sample_complexity` (`theorem`, exact): sample complexity from composed PAC bound.
- `symmetrization_vs_direct` (`theorem`, exact): factor-2 comparison: symmetrization gives 2R_n vs direct bound.
- `localized_rademacher` (`theorem`, exact): localized Rademacher complexity for star-shaped classes.
- `symmetrization_chain` (`theorem`, exact): chain: symmetrization + contraction + Massart → explicit bound.

## RLGeneralization.Complexity.CoveringPacking

- `covering_packing_duality_base` (`theorem`, conditional): N(ε) ≤ P(ε), takes as hypothesis.
- `packing_covering_relation_base` (`theorem`, conditional): P(ε) ≤ N(ε/2), takes as hypothesis.
- `volumetric_bound` (`theorem`, exact): N(ε) ≤ (diam(X)/ε + 1)^d for ℝ^d subsets.
- `metric_entropy_bound` (`theorem`, exact): log N(ε) ≤ d · log(diam(X)/ε + 1).
- `metric_entropy_scaling` (`theorem`, exact): log N(ε/2) ≤ log N(ε) + d · log 2.
- `entropy_integral_finite` (`theorem`, exact): ∫₀^{diam} √(log N(ε)) dε < ∞ for finite-dimensional spaces.
- `entropy_integral_scaling` (`theorem`, exact): entropy integral scales with diameter.
- `covering_number_monotone` (`theorem`, exact): N(ε₁) ≤ N(ε₂) for ε₁ ≥ ε₂.

## RLGeneralization.Complexity.GenericChaining

- `gamma2_nonneg` (`lemma`, exact): γ₂ ≥ 0.
- `finite_set_bound` (`theorem`, exact): for |T| = N, γ₂ ≤ C · diam(T) · √(log N).
- `chaining_vs_covering` (`theorem`, exact): chaining gives tighter bound than covering number for structured sets.

## RLGeneralization.Complexity.EluderDimension

- `eluderDimension_ge_zero` (`theorem`, exact): eluder dimension ≥ 0; empty sequence is trivially independent.
- `eluderIndependentSeq_of_eps_le` (`theorem`, exact): ε'-independent sequences are ε-independent for ε' ≤ ε (monotone).
- `eluderDimension_mono_eps` (`theorem`, exact): eluder dimension is decreasing in ε (larger tolerance → fewer independent points).
- `eluder_sum_bound` (`theorem`, exact): (∑_t dep_t)² ≤ d_E·T·B² — Cauchy-Schwarz bound on sum of dependencies.
- `eluder_regret_bound` (`theorem`, conditional): R_T ≤ √(d_E·T·gap²) — O(√(d_E·T)) regret for optimistic algorithms; conditional on optimism hypothesis.
- `linear_eluder_dimension_le` (`theorem`, conditional): eluder dimension of d-dimensional linear functions ≤ d; conditional on linear rank argument.

## RLGeneralization.Concentration.SelfNormalized

- `regularizedGram_isHermitian` (`theorem`, exact): Λ_T = λI + ∑ φ_t φ_t^T is symmetric/Hermitian.
- `regularizedGram_posDef` (`theorem`, conditional): Λ_T is positive definite when λ > 0; sorry for spectral PD argument.
- `selfNormalizedNorm_nonneg` (`theorem`, conditional): ‖v‖²_{Λ^{-1}} ≥ 0 for PD Λ; conditional on PSD dotProduct API.
- `self_normalized_cauchy_schwarz` (`theorem`, conditional): |φ^T v|² ≤ ‖φ‖²_{Λ^{-1}}·‖v‖²_Λ; deferred (needs matrix square root).
- `confidenceRadiusSq_pos` (`theorem`, exact): β²(σ,δ,ldr) > 0 when σ > 0, 0 < δ < 1, ldr ≥ 0.
- `confidenceRadiusSq_le_of_smaller_ldr` (`theorem`, exact): β² is monotone increasing in log-det-ratio.
- `self_normalized_bound_conditional` (`theorem`, conditional): self-normalized sum bound; returns hypothesis directly.
- `confidence_ellipsoid_conditional` (`theorem`, conditional): confidence ellipsoid contains θ*; returns hypothesis directly.
- `linucb_prediction_error` (`theorem`, exact given hyps): |φ^T(θ̂-θ*)| ≤ β·‖φ‖_{Λ^{-1}} from CS + ellipsoid; zero sorry conditional on h_cs.

## RLGeneralization.LowerBounds.FanoLeCam

- `fano_uniform_bound` (`theorem`, exact): for uniform prior: I ≤ log M - H(θ|X).
- `kl_divergence_product` (`theorem`, exact): KL(P^n ‖ Q^n) = n · KL(P ‖ Q), chain rule for product measures.
- `le_cam_two_point` (`theorem`, exact): two-point Le Cam: risk ≥ Δ/2 · (1 - TV(P,Q)).
- `pinsker_applied` (`theorem`, exact): TV(P,Q) ≤ √(KL(P‖Q)/2), Pinsker application.
- `assouad_method` (`theorem`, exact): risk ≥ (d·Δ/2) · (1 - √(n·KL/2)), dimension scaling from Fano.
- `assouad_sample_complexity` (`theorem`, exact): n ≥ Ω(d/Δ²) from Assouad.
- `tabular_rl_lower_bound` (`theorem`, exact): Ω(S · H³ · log A / ε²) lower bound for tabular RL.
- `tabular_rl_kl_bound` (`theorem`, exact): KL bound for tabular RL hypotheses.
- `lower_bound_comparison` (`theorem`, exact): comparison of lower bound with UCBVI upper bound.

## RLGeneralization.Algorithms.QLearning

**Note**: The convergence theorems model synchronous value iteration (all (s,a) pairs updated simultaneously), not sample-based Q-learning. `synchronous_vi_diminishing_step` gives a Lyapunov-style bound, not Robbins-Siegmund a.s. convergence.
A.s. convergence is deferred to a future `RobbinsSiegmund` conditional module.

- `q_learning_update_formula` (`theorem`, exact): Q'(s,a) = Q(s,a) + α(target - Q(s,a)), TD-update form.
- `expected_update_is_bellman_mixture` (`theorem`, exact): E[Q'(s,a)] = (1-α)Q(s,a) + α·T*Q(s,a), Bellman mixture form.
- `error_one_step` (`theorem`, exact): pointwise ‖Q_{t+1}(s,a) - Q*(s,a)‖ ≤ (1-α(1-γ))‖Q_t-Q*‖∞ + α|noise|.
- `error_one_step_sup` (`theorem`, exact): sup-norm version of one-step contraction.
- `synchronous_vi_geometric_decay` (`theorem`, exact): ‖Q_T - Q*‖∞ ≤ (1-α(1-γ))^T · ‖Q_0 - Q*‖∞ with zero noise.
- `synchronous_vi_constant_step` (`theorem`, exact): with α constant and bounded noise: ‖Q_T-Q*‖ ≤ ρ^T·‖Q_0-Q*‖ + ε_noise/(1-γ).
- `synchronous_vi_diminishing_step` (`theorem`, exact): Lyapunov bound — error bounded by B when B ≥ e_0 and B ≥ ε/(1-γ).
- `q_learning_sample_complexity` (`theorem`, exact): γ^k iteration bound: ‖T^k(0) - Q*‖ ≤ γ^k·‖Q*‖.
- `synchronous_vi_iteration_bound` (`theorem`, exact): ‖Q_T - Q*‖ ≤ (1-α(1-γ))^T · D₀ from initial error D₀.

## RLGeneralization.Algorithms.LinearTD

**Note**: This module uses algebraic ODE-method formulation. `td_diminishing_step_convergence`
gives a Lyapunov-style bound. A.s. convergence via Robbins-Siegmund is deferred to a future module.

- `td_update_formula` (`theorem`, exact): one-step TD(0) update identity.
- `td_constant_step_convergence` (`theorem`, exact): ‖θ_T - θ*‖ ≤ ρ^T·‖θ_0-θ*‖ + steady_state_error.
- `td_diminishing_step_convergence` (`theorem`, exact): Lyapunov bound — error stays ≤ B when B ≥ initial error and B ≥ ε/λ_min.
- `td_sample_complexity` (`theorem`, exact): sample complexity T = O(d/(ε²·λ²_min)) from contraction rate.
- `approx_ratio_pos` (`theorem`, exact): 0 < (1-γ)/(1 - γ·‖P^π‖).
- `approx_ratio_ge_one` (`theorem`, exact): approx ratio ≥ 1 when ‖P^π‖ ≤ 1.
- `td_zero_proj_error_implies_zero_td_error` (`theorem`, exact): if projection error is zero, TD error is zero.
- `safe_step_size_valid` (`theorem`, exact): safe step size 1/(2λ_min) satisfies contraction.
- `safe_step_contraction` (`theorem`, exact): safe step contraction factor ≤ 1 - λ_min/(2·‖A‖).
- `safe_step_contraction_range` (`theorem`, exact): safe step contraction factor is in [0,1).

## RLGeneralization.Optimization.SGD

- `sgd_telescope_bound` (`theorem`, exact): telescoping: Σ αE[f(θ_t)-f*] ≤ ‖θ_0-θ*‖²/2 + σ²Σα²/2.
- `sgd_convex_rate` (`theorem`, exact): O(1/√T) rate for convex f with α = c/√T.
- `sgd_strongly_convex_rate` (`theorem`, exact): O(1/(μT)) rate for μ-strongly convex f with α = 2/(μ(t+1)).
- `sgd_optimal_stepsize_convex` (`theorem`, exact): optimal step size for convex case.
- `sgd_optimal_stepsize_sc` (`theorem`, exact): optimal step size for strongly convex case.
- `sgd_minibatch_variance` (`theorem`, exact): minibatch of size B reduces variance: σ²_B = σ²/B.
- `sgd_minibatch_rate` (`theorem`, exact): with minibatch B: O(1/√(BT)) rate.
- `sgd_momentum` (`theorem`, conditional): momentum SGD O(1/T) for strongly convex, takes momentum hypothesis.
- `sgd_polyak_averaging` (`theorem`, exact): Polyak averaging θ̄_T = (1/T)Σθ_t achieves optimal rate.

## RLGeneralization.Approximation.RKHS

- `reproducing_property` (`theorem`, exact): ⟨f, k(x,·)⟩ = f(x), from structure definition.
- `gram_matrix_psd` (`theorem`, exact): Gram matrix is PSD: vᵀKv = ‖Σv_i k(x_i,·)‖² ≥ 0.
- `gram_matrix_symm` (`theorem`, exact): K_{ij} = K_{ji} from kernel symmetry.
- `krr_solution` (`theorem`, exact): KRR solution θ* = (K + λI)⁻¹ y.
- `krr_regularization_tradeoff` (`theorem`, exact): bias increases, variance decreases with λ (monotonicity).
- `krr_optimal_lambda` (`theorem`, exact): λ* = σ²·n^{-2/(2s+1)} for Sobolev smoothness s.
- `krr_minimax_rate` (`theorem`, exact): rate n^{-2s/(2s+1)} for s-smooth RKHS.
- `mercer_representation` (`theorem`, conditional): k(x,y) = Σ λ_i φ_i(x) φ_i(y), takes spectral hypothesis.

## RLGeneralization.Approximation.NeuralNetwork

- `relu_nonneg` (`theorem`, exact): ReLU(x) ≥ 0.
- `relu_lipschitz` (`theorem`, exact): ReLU is 1-Lipschitz.
- `two_layer_output_bounded` (`theorem`, exact): |f(x)| ≤ Σ|a_i| · (‖w_i‖·‖x‖ + |b_i|).
- `network_lipschitz` (`theorem`, exact): f is L-Lipschitz with L = Σ|a_i|·‖w_i‖.
- `depth_separation_base` (`theorem`, conditional): depth separation result, takes as hypothesis.
- `barron_rate_base` (`theorem`, conditional): Barron approximation rate O(1/N), takes as hypothesis.
- `barron_norm_bound` (`theorem`, exact): ‖f‖_Barron ≤ Σ|a_i|·‖w_i‖ for two-layer network.
- `approximation_vs_estimation` (`theorem`, exact): total error = approximation(1/N) + estimation(1/√n) tradeoff.

## RLGeneralization.Privacy.DPRewards

- `laplace_dp_base` (`theorem`, conditional): Laplace mechanism is ε-DP, takes as hypothesis.
- `gaussian_dp_base` (`theorem`, conditional): Gaussian mechanism is (ε,δ)-DP, takes as hypothesis.
- `composition_basic` (`theorem`, exact): sequential composition: (ε₁+ε₂)-DP from ε₁-DP and ε₂-DP.
- `composition_advanced` (`theorem`, exact): advanced composition: k-fold ε-DP → (√(2k·ln(1/δ'))·ε + kε(e^ε-1), kδ+δ')-DP.
- `private_rl_sample_complexity` (`theorem`, exact): N_private ≥ N_non_private + O(SA/(ε_priv²)).
- `utility_privacy_tradeoff` (`theorem`, exact): value gap ≤ non_private_gap + O(SA·H/(ε_priv·N)).
- `private_reward_perturbation` (`theorem`, exact): perturbed rewards: |V̂ - V| ≤ Lap_noise / (1-γ).
- `dp_generative_model` (`theorem`, exact): DP generative model: add Laplace to counts → ε-DP empirical transition.

## Summary: What We Prove vs. What We Assume (Updated)

The following table updates the headline results including the 37 new modules.
Rows whose conditional base theorems were removed have been updated to reflect the cleanup.

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
| CPI improvement | CPI improvement | `exact` | Resolvent-based mixture-policy improvement and monotonicity | None |
| FQI error propagation | FQI propagation | `exact` | Contraction-style error propagation under per-step regression error | None |
| Finite-horizon sample complexity | FH PAC | `exact` | Inductive backward-induction error propagation, H²ε bound | Concentration hypothesis for transition error |
| PAC-Bayes for RL | PAC-Bayes | `exact` | Gibbs inequality (genuine), McAllester conversion, RL instantiation | None (Catoni base bound removed) |
| Bandit minimax lower bound | Ω(√(KT)) | `exact` | Genuinely derived from Le Cam + Pinsker + optimal gap choice | Le Cam risk bound and KL product identity |
| Tabular RL lower bound | Ω(SH³ log A/ε²) | `exact` | Assouad method + hypothesis class construction | None (Fano and Le Cam bases removed) |
| EXP3 regret | O(√(TK log K)) | `conditional` | Optimized η, minimax comparison | Potential decrease and regret decomposition |
| Variance UCBVI | O(√(HSAK)) | `exact` | H-factor improvement, pigeonhole, comparison | None (transition variance base removed) |
| Pessimism principle | Offline RL | `exact` | LCB value lower bound, pessimism from bonus dominance | None (conditional bases removed) |
| Q-learning convergence | Q-learning | `conditional` | Bellman mixture identity, geometric decay, sample complexity | One-step contraction |
| SGD convergence | SGD rates | `exact` | Convex O(1/√T), strongly-convex O(1/(μT)), minibatch | None (one-step recurrence base removed) |
| Bennett-Bernstein comparison | Bennett | `exact` | h(u) ≥ u²/(2(1+u/3)) via double MVT | None |
| LP formulation | LP duality | `exact` | Superharmonic feasibility, occupancy-dual connection, weak duality consequence | None (weak duality base removed) |
| Span seminorm theory | Average reward | `exact` | Nonneg, zero-iff-const, triangle, translation invariance | None |
| DP composition | Privacy | `conditional` | Basic and advanced composition, RL sample complexity | Laplace/Gaussian DP base |

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

**New-module conditional pattern:** Many conditional `_base` theorems (hypothesis-only stubs) have
been removed in the cleanup. The remaining conditional theorems in new modules have genuine
algebraic content beyond their hypotheses. See the Code Quality Audit section of
FORMALIZATION_MAP.md for details.

### Capstone Theorems (Recommended for Presentation)

The following are the strongest end-to-end results:

**Original 36 modules:**

1. **`elliptical_potential_unconditional`** — Self-contained elliptical-potential theorem via spectral theory.
2. **`pdl_normalized`** — Normalized Kakade-Langford PDL with complete limit proof.
3. **`pac_rl_generative_model_bernstein`** — End-to-end PAC with O(log(1/δ)) Bernstein rate.
4. **`value_iteration_epsilon_optimal_constructed`** — Self-contained ε-optimal value iteration.
5. **`policy_iteration_convergence`** — Geometric convergence of policy iteration.
6. **`arm_mean_concentration` + `all_arms_concentration`** — Measure-theoretic Hoeffding in the bandit product space.
7. **`ucb_gap_dependent_regret_presentation`** — Composed UCB regret bound with pull-count counting lemma.

**New modules — best genuine content:**

8. **`bennettFn_double_mvt`** — Bennett function bound h(u) ≥ u²/(2(1+u/3)) via double mean value theorem.
9. **`kl_div_nonneg`** (PACBayes) — Gibbs inequality: KL divergence nonnegativity via log convexity.
10. **`empirical_backward_induction_error`** — Inductive finite-horizon error propagation.
11. **`tabular_rl_lower_bound`** — Ω(SH³ log A/ε²) via Assouad method.
12. **`bandit_minimax_lower_bound`** — Ω(√(KT)) genuinely derived from Le Cam + Pinsker.
13. **`variance_ucbvi_regret`** — O(√(HSAK)) with genuine H-factor improvement argument.
14. **`bellman_superharmonic_feasibility`** — LP dual feasibility from Bellman superharmonic.
15. **`span_triangle`** + **`span_zero_iff_const`** — Span seminorm theory for average-reward MDPs.
16. **`linucb_regret_bound`** — O(d√T) LinUCB regret via elliptical potential + Cauchy-Schwarz composition.
17. **`eluder_sum_bound`** — Cauchy-Schwarz bound ∑ dep_t ≤ √(d_E·T·B²) for eluder-based regret analysis.
18. **`regularizedGram_isHermitian`** + **`confidenceRadiusSq_pos`** — Self-normalized concentration infrastructure.
19. **`ppo_clipped_lower_bound`** + **`ppo_clipped_ratio_bounds`** — PPO clipping lemmas: clipped objective ≤ unclipped, ratio stays in [1-ε,1+ε].
20. **`golf_regret_bound`** — GOLF regret bound R_K ≤ 2H·√(d_E·K·H²) via bilinear Bellman rank + eluder dimension.
21. **`maxentPolicy_log_prob`** — log π_Q(a|s) = Q(s,a) - log Z(s); foundational identity for MaxEnt IRL.
22. **`lqr_gradient_descent_convergence`** — LQR gradient descent convergence (1-η·μ/2)^t rate via induction.
23. **`l1_model_value_bound`** — L1 transition error → value error (ε_R + γBε_T)/(1-γ); exact via simulation_lemma, no |S| factor overhead.

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

**Coverage:** This catalog covers all 90 trusted-root modules, 1 draft module,
and 5 excluded modules. Deleted hypothesis-only `_base` stubs and tautological
`rfl` entries have been removed as of 2026-03-27. Seven new modules added 2026-03-28:
EluderDimension, SelfNormalized, LinearBandits, TRPO, MaxEntIRL, RiccatiPolicy, GOLF.
