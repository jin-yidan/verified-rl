# Formalization Map

**Last updated**: 2026-03-19
**Trusted build**: `lake build --wfail`  
**Draft build**: `lake build RLGeneralization.Draft`

This repository now separates a trusted benchmark root from a draft frontier
aggregate.

## Trusted Root

[`RLGeneralization.lean`](RLGeneralization.lean)
is the benchmark target. It is the only root that should be treated as clean
training/evaluation data for proof-auditing agents.

Imported modules in the trusted root:

- `RLGeneralization.MDP.Basic`
- `RLGeneralization.MDP.BellmanContraction`
- `RLGeneralization.MDP.SimulationLemma`
- `RLGeneralization.MDP.ValueIteration`
- `RLGeneralization.MDP.PolicyIteration`
- `RLGeneralization.MDP.Resolvent`
- `RLGeneralization.MDP.BanachFixedPoint`
- `RLGeneralization.MDP.PerformanceDifference`
- `RLGeneralization.MDP.OccupancyMeasure`
- `RLGeneralization.MDP.MatrixResolvent`
- `RLGeneralization.MDP.SimulationResolvent`
- `RLGeneralization.MDP.FiniteHorizon`
- `RLGeneralization.Generalization.SampleComplexity`
- `RLGeneralization.Generalization.ComponentWise`
- `RLGeneralization.LinearFeatures.LSVI`
- `RLGeneralization.LinearFeatures.RegressionBridge`
- `RLGeneralization.Concentration.Hoeffding`
- `RLGeneralization.Concentration.Bernstein`
- `RLGeneralization.Concentration.GenerativeModelCore`
- `RLGeneralization.Concentration.GenerativeModel`
- `RLGeneralization.Generalization.MinimaxSampleComplexity`
- `RLGeneralization.Bandits.UCB`
- `RLGeneralization.Bandits.BanditConcentration`
- `RLGeneralization.BilinearRank.Auxiliary`
- `RLGeneralization.Exploration.UCBVI`
- `RLGeneralization.Exploration.BatchUCBVI`
- `RLGeneralization.PolicyOptimization.PolicyGradient`
- `RLGeneralization.PolicyOptimization.CPI`
- `RLGeneralization.PolicyOptimization.Optimality`
- `RLGeneralization.OfflineRL.FQI`
- `RLGeneralization.ImitationLearning.Basic`
- `RLGeneralization.LinearMDP.Basic`
- `RLGeneralization.LinearMDP.EllipticalPotential`
- `RLGeneralization.LinearMDP.Regret`
- `RLGeneralization.LQR.Basic`
- `RLGeneralization.Test.SimpleMDP`

## Draft Frontier

[`RLGeneralization/Draft.lean`](RLGeneralization/Draft.lean)
collects modules that compile but are excluded from the benchmark root because
their main theorems are conditional, hypothesis-forwarding, or otherwise not
yet benchmark-grade as end-to-end formalized results.

Draft aggregate modules:

- `RLGeneralization.BilinearRank.Basic`
- `RLGeneralization.PolicyOptimization.NPG`

Substantive theorems now promoted into the trusted root:

- `FiniteMDP.policy_improvement_sandwich`
- `FiniteMDP.policy_iteration_convergence`
- `FiniteMDP.exists_actionValue_fixedPoint`
- `FiniteMDP.exists_bellmanOptimalQ_fixedPoint`
- `FiniteMDP.samples_iIndepFun`
- `FiniteMDP.indicator_expectation`
- `FiniteMDP.generative_model_pac`
- `FiniteHorizonMDP.bellman_error_le_of_rank`
- `FiniteMDP.cpi_improvement_bound`
- `FiniteMDP.cpi_monotonic_improvement`
- `FiniteMDP.weighted_deviation_bound_genuine`
- `FiniteMDP.variance_swap`
- `FiniteMDP.minimax_deterministic_core`
- `FiniteMDP.coordinate_indicator_bernstein_upper`
- `FiniteMDP.empirical_transition_entry_bernstein_upper`
- `FiniteMDP.empirical_transition_entry_bernstein_concentration`
- `FiniteMDP.generative_model_pac_bernstein`
- `BanditInstance.etc_oracle_regret_bound`
- `FiniteMDP.minimax_value_gap_high_probability_from_empirical_eval_and_bellman_fixed_point`
- `FiniteMDP.minimax_value_gap_high_probability_from_empirical_fixed_points`
- `FiniteMDP.minimax_value_gap_high_probability_from_empirical_fixed_points_bernstein`
- `FiniteMDP.pac_rl_generative_model`
- `FiniteMDP.pac_rl_generative_model_optimal`
- `FiniteMDP.value_iteration_epsilon_optimal`
- `FiniteMDP.optimal_value_comparison`
- `FiniteMDP.discountedVisitation_sum`
- `FiniteMDP.pdl_occupancy_form`
- `FiniteMDP.pac_rl_generative_model_bernstein`
- `FiniteMDP.value_iteration_epsilon_optimal_constructed`
- `FiniteMDP.pdl_normalized`
- `FiniteMDP.stateOccupancy_sum_one`
- `lsvi_sample_complexity`
- `lsvi_sample_complexity_rate`
- `lsvi_stage_slt_bound`
- `Bandits.confidence_threshold`
- `Bandits.ucb_index_le_opt_mean`
- `Bandits.ucb_index_opt_ge_opt_mean`
- `Bandits.ucb_gap_dependent_regret`
- `sum_sqrt_le_sqrt_card_mul_sum`
- `FiniteHorizonMDP.pigeonhole_bonus_bound`
- `FiniteMDP.gradient_domination_nonneg`
- `LQRInstance.stageCost_nonneg`

## Status Classes

- `exact`: faithful match or very close to the intended theorem.
- `weaker`: a real theorem, but weaker than the intended target statement.
- `conditional`: the proof is kernel-checked, but key analytical content is supplied as a hypothesis or structure field.
- `wrapper`: the declaration mostly forwards or repackages an assumed inequality and should not be read as substantive derivation.
- `stub`: the statement is still a scaffold and should not be counted as an end-to-end formalization.
- `vacuous`: the conclusion is too weak to count as substantive theory formalization.

## Practical Reading

Use the trusted root when you need:

- reusable RL infrastructure,
- honest benchmark data,
- modules that are not labeled `wrapper`,
- examples of theorem decomposition without placeholders.

Use the draft root when you need:

- open proof obligations,
- examples of “what remains to be shown,”
- supervision for a proof-auditing agent that must distinguish derived theorems from wrappers.

## Machine-Readable Source

The machine-readable version of this map is
[`verification_manifest.json`](verification_manifest.json).
It records the trusted-root module list and statuses, the draft-root module
list, and theorem-level status for the major frontier results.
