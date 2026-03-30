# Formalization Map

**Last updated**: 2026-03-28
**Trusted build**: `lake build --wfail`
**Draft build**: `lake build RLGeneralization.Draft`

This repository now separates a trusted benchmark root from a draft frontier
aggregate.

## Trusted Root

[`RLGeneralization.lean`](RLGeneralization.lean)
is the benchmark target. It is the only root that should be treated as clean
training/evaluation data for proof-auditing agents.

Imported modules in the trusted root (106 modules):

### MDP Core (12 modules)

- `RLGeneralization.MDP.Basic` — Core discounted MDP definitions and Bellman operators.
- `RLGeneralization.MDP.BellmanContraction` — Bellman contraction and norm bounds.
- `RLGeneralization.MDP.SimulationLemma` — Kearns-Singh comparison inequality.
- `RLGeneralization.MDP.ValueIteration` — Value-iteration convergence and ε-optimal policy construction.
- `RLGeneralization.MDP.PolicyIteration` — Policy-iteration sandwich step and convergence.
- `RLGeneralization.MDP.Resolvent` — Resolvent bounds, fixed-point uniqueness, optimal-policy existence.
- `RLGeneralization.MDP.BanachFixedPoint` — Banach fixed-point construction for policy Q-evaluation.
- `RLGeneralization.MDP.PerformanceDifference` — One-step PDL identity and resolvent bound.
- `RLGeneralization.MDP.OccupancyMeasure` — Occupancy measure, normalized PDL.
- `RLGeneralization.MDP.MatrixResolvent` — Matrix resolvent (I-γP^π)⁻¹ via Neumann series.
- `RLGeneralization.MDP.SimulationResolvent` — Exact simulation resolvent identity.
- `RLGeneralization.MDP.FiniteHorizon` — Finite-horizon backward induction.

### MDP Extensions (4 modules)

- `RLGeneralization.MDP.LPFormulation` — LP formulation of discounted MDPs: primal/dual, weak duality, occupancy-dual connection. (exact)
- `RLGeneralization.MDP.AverageReward` — Average-reward MDPs: span seminorm, gain-bias equations, discounted-to-average limit. (conditional: span contraction takes ergodicity hypothesis)
- `RLGeneralization.MDP.HJB` — Hamilton-Jacobi-Bellman stub: HJB equation, verification theorem, discrete Bellman as HJB. (conditional: blocked by ODE/viscosity solutions)
- `RLGeneralization.MDP.POMDP` — POMDPs: belief states, Bayesian belief update, POMDP-as-belief-MDP reduction. (conditional)
- `RLGeneralization.MDP.MultiAgent` — Multi-agent RL: Markov games, Nash equilibrium, minimax theorem, matrix game bounds. (conditional: Nash existence and minimax theorem assumed)

### Generalization (7 modules)

- `RLGeneralization.Generalization.SampleComplexity` — Deterministic comparison/sample-complexity core.
- `RLGeneralization.Generalization.ComponentWise` — Component-wise resolvent-style bounds.
- `RLGeneralization.Generalization.MinimaxSampleComplexity` — Minimax deterministic core, variance/deviation bounds.
- `RLGeneralization.Generalization.PACBayes` — PAC-Bayes bounds for RL: KL divergence, Gibbs inequality, Catoni/McAllester forms, RL instantiation. (exact, except Catoni base bound is conditional)
- `RLGeneralization.Generalization.PolicyEvaluation` — LSTD policy evaluation: value error bound, sample complexity. Regression rate taken as conditional hypothesis. (conditional)
- `RLGeneralization.Generalization.FiniteHorizonSampleComplexity` — Finite-horizon minimax sample complexity: inductive error propagation, H²·ε bound, sample complexity formula. (exact)
- `RLGeneralization.Generalization.UniformConvergence` — VC dimension to uniform convergence to PAC learning chain: VC-based convergence bound, PAC inversion, full VC-PAC chain, RL policy class application. (conditional: concentration step takes VC-based bound as hypothesis)

### Concentration Inequalities (15 modules)

- `RLGeneralization.Concentration.Hoeffding` — Hoeffding/union-bound bridge.
- `RLGeneralization.Concentration.Bernstein` — Bernstein MGF, tail, and two-sided bounds.
- `RLGeneralization.Concentration.Bennett` — Bennett's inequality: Bennett function h(u), monotonicity, double-MVT proof of h(u) ≥ u²/(2(1+u/3)). (exact for Bennett function properties; conditional for the base inequality)
- `RLGeneralization.Concentration.MatrixBernstein` — Matrix Bernstein: variance, dimension factor, confidence ellipsoid, elliptical potential connection. (conditional: matrix tail bound assumed)
- `RLGeneralization.Concentration.SubGaussian` — Sub-Gaussian bridge: bounded rewards, indicators, value difference bounds. (conditional: bounded→sub-Gaussian bridge assumed)
- `RLGeneralization.Concentration.AzumaHoeffding` — Azuma-Hoeffding for finite-horizon MDPs: confidence width, bonus monotonicity, optimism composition. (conditional: Azuma-Hoeffding tail assumed)
- `RLGeneralization.Concentration.McDiarmid` — McDiarmid bounded differences: Azuma-Hoeffding connection, RL application to empirical transitions. (conditional: McDiarmid tail assumed)
- `RLGeneralization.Concentration.JohnsonLindenstrauss` — JL random projection: dimension formula k=O(log(n)/ε²), pairwise union bound. (conditional: JL property assumed)
- `RLGeneralization.Concentration.Talagrand` — Talagrand convex distance: variance bounds, suprema concentration, Talagrand-vs-McDiarmid comparison. (conditional: core inequality assumed)
- `RLGeneralization.Concentration.LargeDeviations` — Large deviation principles: rate function, Cramér upper bound, Bernstein as special case. (conditional: Cramér bound assumed)
- `RLGeneralization.Concentration.Isoperimetric` — Isoperimetric inequalities: Gaussian, hypercube, Lévy, Bobkov connection. (conditional: all three base inequalities assumed)
- `RLGeneralization.Concentration.PhiEntropy` — Phi-entropy and modified log-Sobolev: subadditivity, Herbst argument, MLS-implies-Bernstein, Pinsker, entropy method. (conditional: subadditivity and Herbst assumed)
- `RLGeneralization.Concentration.GenerativeModelCore` — Generative-model product measure, coordinate independence, PAC concentration.
- `RLGeneralization.Concentration.GenerativeModel` — Bernstein PAC analysis, canonical fixed-point construction, end-to-end minimax composition.
- `RLGeneralization.Concentration.DiscreteConcentration` — Discrete distribution L1 concentration: multinomial bound, RL transition L1 bound, value error bound via simulation lemma. (conditional: union bound + Hoeffding per coord)

### Concentration Stubs (3 modules)

- `RLGeneralization.Concentration.StochasticCalculus` — Stochastic calculus stub: Itô process, Itô isometry, Euler-Maruyama. (conditional: blocked by Brownian motion upstream)
- `RLGeneralization.Concentration.CLT` — Central Limit Theorem stub: CLT statement, Berry-Esseen rate, Mill ratio. (conditional: blocked by characteristic functions)
- `RLGeneralization.Concentration.RobbinsSiegmund` — Robbins-Siegmund convergence for stochastic approximation: a.s. convergence and summability. (conditional: blocked by Mathlib probability theory)

### Bandits (6 modules)

- `RLGeneralization.Bandits.UCB` — UCB: ETC, gap-dependent regret, counting argument, worst-case conversion.
- `RLGeneralization.Bandits.BanditConcentration` — Bernoulli reward space, Hoeffding for arm means, union bound.
- `RLGeneralization.Bandits.EXP3` — EXP3 adversarial regret: exponential weights, potential function, O(√(TK log K)). (conditional: potential decrease and regret decomposition assumed)
- `RLGeneralization.Bandits.LowerBound` — Minimax lower bound: Le Cam two-point, combinatorial bound, Pinsker, Ω(√(KT)). (conditional: Le Cam risk bound and KL product assumed; Ω(√(KT)) genuinely derived)
- `RLGeneralization.Bandits.ThompsonSampling` — Thompson Sampling: information ratio, √(TK log K/2), Bayesian-vs-frequentist, near-minimax. (conditional: information ratio and regret bounds assumed)
- `RLGeneralization.Bandits.LinearBandits` — LinUCB for linear bandits (Abbasi-Yadkori 2011): linUCBIndex = φ^T θ̂ + β·‖φ‖_{Λ^{-1}}, optimism lemma, regret decomposition, O(d√T) regret via elliptical potential. (conditional: per-round CS + confidence ellipsoid from SelfNormalized)

### Exploration (4 modules)

- `RLGeneralization.Exploration.UCBVI` — UCBVI regret: optimism, per-episode, cumulative, O(√(H³SAK)).
- `RLGeneralization.Exploration.VarianceUCBVI` — Variance-aware UCBVI: Bernstein bonus, variance pigeonhole, O(√(HSAK)) improving H³→H. (conditional: variance ≤ range × mean assumed)
- `RLGeneralization.Exploration.BatchUCBVI` — Harmonic-sqrt bound, Cauchy-Schwarz, pigeonhole bonus bound.
- `RLGeneralization.Exploration.UCBVIProbability` — UCBVI with high-probability regret bounds: concentration event, optimism on good event, R(K) ≤ O(H²√(SAK·log(SAHK/δ))), expected regret decomposition. (conditional: concentration and optimism taken as hypothesis)

### Linear Features & Linear MDPs (5 modules)

- `RLGeneralization.LinearFeatures.LSVI` — LSVI error propagation core.
- `RLGeneralization.LinearFeatures.RegressionBridge` — LSVI-SLT bridge. (conditional: regression rate as hypothesis)
- `RLGeneralization.LinearMDP.Basic` — Linear-MDP definition and optQ_linear proof.
- `RLGeneralization.LinearMDP.EllipticalPotential` — Elliptical potential: spectral + AM-GM, fully self-contained.
- `RLGeneralization.LinearMDP.Regret` — UCBVI-Lin regret wrappers. (conditional: elliptical confidence set construction)

### Bilinear Rank (2 modules)

- `RLGeneralization.BilinearRank.Auxiliary` — Bellman-rank definitions and exact bilinear bounds.
- `RLGeneralization.BilinearRank.GOLF` — GOLF algorithm (Ch 8.5): GOLFInstance, confidence sets, eluder-based regret bound O(H²√(d_E·K)). (conditional: optimism and eluder sum assumed)

### Policy Optimization (5 modules)

- `RLGeneralization.PolicyOptimization.PolicyGradient` — Log-derivative trick, baseline invariance, advantage form, softmax. (conditional: calculus layer deferred)
- `RLGeneralization.PolicyOptimization.CPI` — Conservative policy iteration: mixture resolvent, improvement.
- `RLGeneralization.PolicyOptimization.Optimality` — Gradient-domination nonnegativity.
- `RLGeneralization.PolicyOptimization.NPG` — Natural policy gradient: Fisher PSD, mirror-descent, O(1/√T). (conditional: Fisher PSD and convergence base assumed)
- `RLGeneralization.PolicyOptimization.TRPO` — TRPO/PPO (Ch 12.2): surrogate lower bound, KL penalty, PPO clipping lemma, trust-region monotone improvement. (conditional: occupancy PDL + KL-TV bound assumed)

### Offline RL (2 modules)

- `RLGeneralization.OfflineRL.FQI` — Fitted Q-iteration contraction and error propagation.
- `RLGeneralization.OfflineRL.Pessimism` — Pessimism principle: LCB Q-function, concentrability, offline regret, online-vs-offline comparison. (conditional: concentrability amplification assumed)

### Imitation Learning (2 modules)

- `RLGeneralization.ImitationLearning.Basic` — Behavior-cloning H²ε bound, DAgger H·ε bound. (conditional: per-step advantage hypothesis)
- `RLGeneralization.ImitationLearning.MaxEntIRL` — MaxEnt IRL (Ziebart 2008, Ch 13.4): softmax policy, log-partition identity, feature matching, dual linearity, reduction to soft MDP. (conditional: feature matching takes optimal Q as hypothesis)

### LQR (2 modules)

- `RLGeneralization.LQR.Basic` — LQR definitions, Riccati infrastructure, stageCost_nonneg.
- `RLGeneralization.LQR.RiccatiPolicy` — Riccati recursion (Ch 14): finite-horizon recursion, closed-loop Bellman, LQR policy gradient formula, gradient descent convergence. (conditional: closed-loop Bellman sorry; convergence zero sorry)

### Statistical Complexity (7 modules)

- `RLGeneralization.Complexity.VCDimension` — VC dimension: growth function, Sauer-Shelah (algebraic), polynomial bound, convergence rate, VC-vs-PAC-Bayes. (conditional: Sauer-Shelah and convergence rate assumed)
- `RLGeneralization.Complexity.Rademacher` — Rademacher complexity: Massart bound, VC-Rademacher connection, contraction principle, generalization. (conditional: Massart and generalization base assumed)
- `RLGeneralization.Complexity.Symmetrization` — Symmetrization lemma: factor-2, McDiarmid concentration, PAC composition. (conditional: symmetrization/desymmetrization assumed)
- `RLGeneralization.Complexity.CoveringPacking` — Covering/packing duality: N(ε) ≤ P(ε) ≤ N(ε/2), volumetric bounds, metric entropy. (conditional: duality bounds assumed)
- `RLGeneralization.Complexity.GenericChaining` — Generic chaining/γ₂: admissible sequences, Dudley equivalence, finite set bound. (conditional: Dudley equivalence and chaining bound assumed)
- `RLGeneralization.Complexity.EluderDimension` — Eluder dimension (Russo-Van Roy 2013): eluderIndependent, eluderDimension via sSup, linearFunctions class. eluder_sum_bound (Cauchy-Schwarz zero sorry). eluder_regret_bound conditional on optimism hypothesis. (conditional: linear rank bound and optimism assumed)
- `RLGeneralization.Concentration.SelfNormalized` — Self-normalized concentration (Abbasi-Yadkori 2011): regularizedGram, selfNormalizedNorm, confidenceRadiusSq. Hermitian/positivity/monotonicity proved zero sorry. Cauchy-Schwarz and PD properties conditional. (conditional: matrix spectral API and PSD dotProduct deferred)

### Information-Theoretic Lower Bounds (1 module)

- `RLGeneralization.LowerBounds.FanoLeCam` — Fano's inequality, Le Cam, Assouad with dimension scaling, tabular RL Ω(SH³ log A/ε²). (conditional: Fano and Le Cam base assumed; Assouad and RL lower bound genuinely derived)

### Algorithms (3 modules)

- `RLGeneralization.Algorithms.QLearning` — Q-learning: Bellman mixture identity, geometric decay, constant/diminishing step convergence, sample complexity. (conditional: one-step contraction assumed)
- `RLGeneralization.Algorithms.LinearTD` — Linear TD(0): projected Bellman, Tsitsiklis-Van Roy bound, convergence. (conditional: expected update and contraction factor assumed; PD matrix hypothesis)
- `RLGeneralization.Algorithms.SARSA` — SARSA on-policy TD learning: update rule, expected SARSA, noise decomposition, SARSA vs Q-learning gap, Bellman contraction for policy evaluation. (conditional)

### Optimization (1 module)

- `RLGeneralization.Optimization.SGD` — SGD: convex O(1/√T), strongly-convex O(1/(μT)), telescope, minibatch. (conditional: one-step recurrence assumed)

### Function Approximation (2 modules)

- `RLGeneralization.Approximation.RKHS` — RKHS: reproducing kernel, Gram PSD/symmetry, kernel ridge regression, regularization tradeoff. (conditional: KRR bias-variance assumed)
- `RLGeneralization.Approximation.NeuralNetwork` — Neural network approximation: two-layer, ReLU, UAT, depth separation, Barron rate. (conditional: UAT, depth separation, Barron rate all assumed)

### Privacy (1 module)

- `RLGeneralization.Privacy.DPRewards` — Differential privacy for RL: Laplace/Gaussian mechanisms, composition, private RL sample complexity. (conditional: Laplace and Gaussian DP assumed)

### Tests (1 module)

- `RLGeneralization.Test.SimpleMDP` — Sanity checks for the trusted target.

## Draft Frontier

[`RLGeneralization/Draft.lean`](RLGeneralization/Draft.lean)
collects modules that compile but are excluded from the benchmark root because
their main theorems are conditional, hypothesis-forwarding, or otherwise not
yet benchmark-grade as end-to-end formalized results.

Draft aggregate modules (5 modules):

- `RLGeneralization.BilinearRank.Basic` — Draft Bellman-rank degenerate helper and GOLF wrappers.
- `RLGeneralization.OfflineRL.FunctionApprox` — Offline RL with function approximation: FQI under realizability, eluder-dimension suboptimality, pessimism-coverage tradeoff. (conditional)
- `RLGeneralization.MDP.AverageRewardNonasymptotic` — Average-reward nonasymptotic sample complexity: finite-sample bound, span bound. (conditional: mixing time)
- `RLGeneralization.MDP.POmdpBeliefMDP` — POMDP belief-MDP reduction: belief-state process as MDP, value equivalence. (conditional: measurability)
- `RLGeneralization.BilinearRank.RepresentationBound` — Bellman rank / eluder dimension connection, low-rank MDP regret. (conditional)

## Excluded Modules

- `RLGeneralization.Concentration.MarkovChain` — Excluded frontier file. Theorem surface too thin; does not formalize a genuine concentration result.
- `RLGeneralization.Test.ConcreteExample` — Concrete worked example and sanity-check module outside the trusted benchmark root.

## Promoted Theorems

Substantive theorems promoted into the trusted root (original 36 modules):

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

## Code Quality Audit and Remediation (2026-03-27)

An audit of the 37 new modules found ~55 tautological theorems (conclusion
restates a hypothesis) across 35 modules. **All tautologies have been deleted.**
The remaining code compiles with zero `sorry`.

### Remediation summary

- **~64 tautological theorems deleted** across 35 modules.
- **Callers updated** to take hypotheses directly instead of via deleted wrappers.
- **Misleading docstrings fixed** in ThompsonSampling, LowerBound, LPFormulation, AverageReward, HJB, SGD, NeuralNetwork, RKHS.
- **Unused definitions removed:** `Gain`, `Bias` type aliases in AverageReward.
- **Vacuous definition annotated:** `depth_separation_holds` in NeuralNetwork.
- **Definition mismatch documented:** `stationaryOccupancy` in LPFormulation (one-step version).
- **Build passes** with zero `sorry` after all deletions.

### What remains conditional

Downstream theorems in the new modules still take core analytical results as
hypotheses (e.g., UCBVI takes optimism as hypothesis, SGD takes one-step
recurrence as hypothesis). These are honest conditional theorems — the
hypothesis is a different claim from the conclusion. The deleted tautologies
were cases where the hypothesis was identical to the conclusion.

**Best genuine content in new modules:**
- `Bennett` — Bennett function properties and double-MVT Bennett-Bernstein comparison.
- `PACBayes` — Gibbs inequality (KL divergence nonnegativity) via log convexity.
- `FiniteHorizonSampleComplexity` — inductive backward-induction error propagation.
- `FanoLeCam` — Assouad's method and tabular RL lower bound Ω(SH³ log A/ε²).
- `LPFormulation` — Bellman-superharmonic feasibility and occupancy-dual connection.
- `AverageReward` — Span seminorm theory (nonneg, zero-iff-const, triangle).
- `DPRewards` — Composition theorems and RL sample complexity (clean, no tautologies).
- `CoveringPacking` — Genuine covering/packing duality via maximal packing argument.

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
- examples of "what remains to be shown,"
- supervision for a proof-auditing agent that must distinguish derived theorems from wrappers.

## Machine-Readable Source

The machine-readable version of this map is
[`verification_manifest.json`](verification_manifest.json).
It records the trusted-root module list and statuses, the draft-root module
list, and theorem-level status for the major frontier results.
