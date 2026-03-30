# Status Summary

This file is machine-derived from `verification_manifest.json`.

## Trusted Root

- Modules: 111
- Exact: 74
- Weaker: 0
- Conditional: 37
- Build command: `lake build`

### Exact Modules

- `RLGeneralization.MDP.Basic` — Core discounted MDP definitions and Bellman operators.
- `RLGeneralization.MDP.BellmanContraction` — Bellman contraction and norm bounds.
- `RLGeneralization.MDP.SimulationLemma` — Kearns-Singh comparison inequality. The exact resolvent identity is in SimulationResolvent; this inequality is a genuine corollary sufficient for all downstream uses.
- `RLGeneralization.MDP.ValueIteration` — Value-iteration convergence, threshold, and a self-contained ε-optimal policy construction via Banach fixed point.
- `RLGeneralization.MDP.PolicyIteration` — Full policy-iteration sandwich step and convergence theorem.
- `RLGeneralization.MDP.Resolvent` — Resolvent bounds, fixed-point uniqueness, and optimal-policy existence theorems.
- `RLGeneralization.MDP.BanachFixedPoint` — Banach fixed-point construction of policy-evaluation and optimality Q fixed points in a complete sup-norm space.
- `RLGeneralization.MDP.PerformanceDifference` — One-step PDL identity and resolvent bound. The occupancy-measure form lives in OccupancyMeasure.
- `RLGeneralization.MDP.OccupancyMeasure` — Infinite-horizon occupancy measure via tsum, normalized state-visitation distribution, and the normalized Kakade-Langford performance-difference identity.
- `RLGeneralization.MDP.MatrixResolvent` — Matrix resolvent (I-γP^π)⁻¹ via Neumann series. Policy transition matrix, L∞ norm bound, and resolvent identity.
- `RLGeneralization.MDP.SimulationResolvent` — Exact simulation resolvent identity: V_M - V_Mhat = sum d_hat * driving. Uses limit uniqueness with approximate transition powers.
- `RLGeneralization.MDP.FiniteHorizon` — Finite-horizon backward-induction core.
- `RLGeneralization.MDP.LPFormulation` — LP formulation of discounted MDPs. Primal/dual LP, Bellman superharmonic feasibility, state-action polytope, weak duality, occupancy-dual connection. Zero sorry.
- `RLGeneralization.Generalization.SampleComplexity` — Deterministic comparison/sample-complexity core. All theorems fully proved including model_based_comparison, optimality_gap_from_transition_error. Zero sorry.
- `RLGeneralization.Generalization.ComponentWise` — Component-wise resolvent-style bounds with approxMDP_value_exists proving Bellman fixed-point existence via Banach. All theorems fully proved. Zero sorry.
- `RLGeneralization.LinearFeatures.LSVI` — Approximate dynamic-programming error-propagation core. Inductive error bound, greedy gap, policy value gap 2H²η. All theorems fully proved. Zero sorry.
- `RLGeneralization.Generalization.TransferRL` — Transfer RL / sim-to-real. TransferGap structure, source-target value gap from model error (simulation lemma wrapper), sample reuse decomposition, triangle bound, warm-start improvement, domain randomization, progressive transfer. Zero sorry.
- `RLGeneralization.Concentration.Hoeffding` — Hoeffding/union-bound bridge used by the verified target.
- `RLGeneralization.Concentration.Bernstein` — Bernstein MGF, one-sided tail bound, two-sided Bernstein (Boucheron Cor 2.11), and Chebyshev-Cantelli one-sided bound (Boucheron Ex 2.3).
- `RLGeneralization.Concentration.BennettMGF` — Full Bennett's inequality: Bennett MGF bound, Chernoff optimization, P[S>=t]<=exp(-V/b^2*h(bt/V)), Bennett>=Bernstein corollary. Zero sorry.
- `RLGeneralization.Concentration.MatrixBernstein` — Matrix Bernstein inequality algebraic core. Matrix variance, dimension-factor exponent, confidence width, confidence ellipsoid, connection to elliptical potential, discharge of LinearMDP/Regret hypothesis form. Zero sorry.
- `RLGeneralization.Concentration.SelfNormalized` — Self-normalized concentration (Abbasi-Yadkori et al. 2011) for LinUCB/LSVI-UCB. regularizedGram_isHermitian, regularizedGram_posDef, selfNormalizedNorm_nonneg, confidenceRadiusSq_pos, confidenceRadiusSq_le_of_smaller_ldr, self_normalized_bound_conditional, confidence_ellipsoid_conditional (all zero sorry). self_normalized_cauchy_schwarz (proved via discriminant argument). linucb_prediction_error (zero sorry, conditional on h_cs).
- `RLGeneralization.Concentration.SubGaussian` — Sub-Gaussian bridge definitions connecting Mathlib's HasSubgaussianMGF/HasCondSubgaussianMGF to RL setting. Bounded rewards and indicators are sub-Gaussian; value function difference bounds for Azuma-Hoeffding.
- `RLGeneralization.Concentration.JohnsonLindenstrauss` — Johnson-Lindenstrauss random projection lemma. JL dimension formula k=O(log(n)/eps^2), sub-Gaussian connection, pairwise union bound, dimension scaling properties. Zero sorry.
- `RLGeneralization.Concentration.Talagrand` — Talagrand convex distance inequality algebraic core. Variance bounds, suprema concentration, Talagrand-vs-McDiarmid comparison, PAC width. Zero sorry.
- `RLGeneralization.Concentration.LargeDeviations` — Large deviation principles. Rate function, Cramer upper bound, rate function properties, Bernstein as special case. Zero sorry.
- `RLGeneralization.Concentration.Isoperimetric` — Isoperimetric inequalities. Gaussian concentration, hypercube, Levy, Bobkov connection. Zero sorry.
- `RLGeneralization.Concentration.PhiEntropy` — Phi-entropy and modified log-Sobolev. Subadditivity, Herbst argument, MLS-implies-Bernstein, Pinsker, entropy method. Zero sorry.
- `RLGeneralization.Concentration.GenerativeModelCore` — Trusted generative-model product measure, coordinate independence, and PAC concentration.
- `RLGeneralization.Concentration.GenerativeModel` — Bernstein PAC analysis with log-rate sample complexity (pac_rl_generative_model_bernstein), canonical fixed-point construction, end-to-end minimax value-gap theorem, and Bernstein composition (minimax_pac_bernstein_composed). Uses uniform variance bound p(1-p) ≤ 1/4 for clean sample-complexity formula; exact per-entry variance is preserved in the intermediate theorem generative_model_pac_bernstein.
- `RLGeneralization.Concentration.DiscreteConcentration` — Discrete distribution L1 concentration (Appendix A.4). All theorems fully proved: l1_le_card_mul_bound, l1_from_eps_over_K, union_bound_sum_le, hoeffding_eps_over_K, multinomial_l1_concentration, l1_transition_error_le, l1_model_value_bound, rl_l1_concentration_conditional (log inversion closed).
- `RLGeneralization.Generalization.MinimaxSampleComplexity` — Minimax deterministic core, variance/deviation bounds, rate scaling. Now includes minimax_deterministic_core_pointwise, minimax_rate_scaling_existence, and minimax_bernstein_improvement. All theorems fully proved. Zero sorry.
- `RLGeneralization.Generalization.PACBayes` — PAC-Bayes bounds for RL. KL divergence for finite distributions with Gibbs inequality (kl_div_nonneg), KL ≤ log|H| for uniform prior, algebraic PAC-Bayes bound (Catoni and McAllester forms), sample complexity, PAC-Bayes vs uniform convergence comparison, and RL instantiation. First formal PAC-Bayes for RL in any proof assistant. Zero sorry.
- `RLGeneralization.Generalization.FiniteHorizonSampleComplexity` — Finite-horizon minimax sample complexity. Empirical backward induction, per-step error propagation (inductive), value error ≤ H² · ε_transition, L1-from-pointwise, and sample complexity formula. Zero sorry.
- `RLGeneralization.Bandits.UCB` — Bandit definitions, oracle ETC regret, UCB algebraic core, confidence threshold, index domination lemmas, gap-dependent regret bound, composed presentation form with pull-count counting argument, worst-case conversion from gap-dependent to O(K√(CT)), complete min-of-both-forms regret bound, and minimax comparison showing UCB within √(KL) of optimal. Zero sorry.
- `RLGeneralization.Bandits.BanditConcentration` — Bernoulli reward probability space, Hoeffding concentration for arm means, union bound over all arms, and ucb_high_probability_good_event proving P(good event) >= 1-delta. Zero sorry.
- `RLGeneralization.Bandits.EXP3` — EXP3 adversarial bandit regret bound. Exponential weights with importance-weighted losses, potential-function argument, regret decomposition, and optimized O(sqrt(T log K)) bound. Zero sorry.
- `RLGeneralization.Bandits.LowerBound` — Minimax lower bound for bandits via Le Cam two-point method. TwoPointTest structure, combinatorial lower bound, Le Cam risk bound, KL product identity, Pinsker hypothesis, Omega(sqrt(KT)) lower bound. Zero sorry.
- `RLGeneralization.Bandits.ThompsonSampling` — Thompson Sampling Bayesian regret. Information ratio framework, TS regret bound sqrt(T*logK/2), TS-vs-UCB comparison, Bayesian-vs-frequentist, near-minimax optimality. Zero sorry.
- `RLGeneralization.BilinearRank.Auxiliary` — Trusted Bellman-rank definitions and exact bilinear Bellman-error bounds.
- `RLGeneralization.Exploration.UCBVI` — Complete algebraic core of UCBVI regret. Includes optimism_from_bonus_dominates_error (bonus dominance → Q* ≤ Q_ucb), ucbvi_full_regret_composition (chains optimism → per-episode → cumulative → final bound), and ucbvi_regret_self_contained (end-to-end R_K ≤ O(√(H³SAK)) from primitive hypotheses). Zero sorry.
- `RLGeneralization.Exploration.VarianceUCBVI` — Variance-aware (Bernstein-style) UCBVI. Transition variance, Bernstein bonus, variance ≤ range × mean inequality, Bernstein ≤ Hoeffding comparison, total variance bound, variance pigeonhole via Cauchy-Schwarz, O(√(HSAK)) regret improving over O(√(H³SAK)). Zero sorry.
- `RLGeneralization.Exploration.BatchUCBVI` — Harmonic-sqrt bound, Cauchy-Schwarz for visit counts, pigeonhole bonus bound. Zero sorry.
- `RLGeneralization.Exploration.RewardFree` — Reward-free exploration (Jin et al. 2020). Dataset structure, planning bound, per-step aggregation, sample decomposition, coverage monotonicity, exploration tradeoff, uniform reward-class bound. Zero sorry.
- `RLGeneralization.PolicyOptimization.CPI` — Resolvent-based conservative policy-iteration improvement theorems.
- `RLGeneralization.PolicyOptimization.Optimality` — Gradient-domination structure and nonnegativity theorem.
- `RLGeneralization.PolicyOptimization.ActorCritic` — Actor-critic methods. Advantage decomposition, baseline invariance, critic bias bound, two-timescale gap, variance reduction (advantage vs Q second moment), improvement direction, accuracy-suffices theorem. Zero sorry.
- `RLGeneralization.OfflineRL.FQI` — Fitted Q-iteration contraction and error-propagation theorem.
- `RLGeneralization.OfflineRL.Pessimism` — Offline RL pessimism principle. LCB Q-function, pessimism from bonus, concentrability amplification, offline regret bound, online-vs-offline comparison, sample complexity. Zero sorry.
- `RLGeneralization.LinearMDP.Basic` — Linear-MDP definition and the optQ_linear proof.
- `RLGeneralization.LinearMDP.EllipticalPotential` — Elliptical-potential analytic core. Matrix-algebra hypotheses fully discharged via spectral theory + AM-GM. elliptical_potential_unconditional provides the fully self-contained version.
- `RLGeneralization.LQR.Basic` — LQR definitions, Riccati infrastructure, and stageCost_nonneg theorem.
- `RLGeneralization.LQR.RiccatiPolicy` — Riccati recursion and LQR policy gradient (Ch 14). riccatiMatrices/riccatiGain/closedLoopDynamics (noncomputable defs). riccati_recursion_form (zero sorry). closed_loop_bellman (proved: Bellman decomposition for closed-loop LQR). lqr_cost_decomposition (proved: cost = trace(Q Sigma) + trace(K^T R K Sigma)). lqr_gradient_descent_convergence (zero sorry).
- `RLGeneralization.Complexity.VCDimension` — VC dimension theory. Growth function bound (Sauer-Shelah algebraic), polynomial bound (d+1)*n^d, log bounds, VC convergence rate, VC-vs-PAC-Bayes comparison. Zero sorry.
- `RLGeneralization.Complexity.Rademacher` — Rademacher complexity. Massart finite-class bound sqrt(2*log|F|/n), VC-Rademacher connection, contraction principle, generalization bound, PAC width, sample complexity. Zero sorry.
- `RLGeneralization.Complexity.Symmetrization` — Symmetrization lemma. Factor-2 symmetrization/desymmetrization, McDiarmid concentration for uniform deviation, PAC bound composition, sample complexity. Zero sorry.
- `RLGeneralization.Complexity.CoveringPacking` — Covering/packing duality. N(eps) <= P(eps) <= N(eps/2), volumetric bounds for Euclidean balls, metric entropy bounds, entropy integral scaling. Zero sorry.
- `RLGeneralization.Complexity.GenericChaining` — Generic chaining / gamma_2. Admissible sequences, gamma_2-Dudley equivalence, finite set bound, complexity hierarchy. Zero sorry.
- `RLGeneralization.LowerBounds.FanoLeCam` — Information-theoretic lower bounds. Fano inequality (error >= 1-(I+log2)/logM), Le Cam generalized, Assouad method with dimension scaling, tabular RL lower bound Omega(SH^3 logA/eps^2). Zero sorry.
- `RLGeneralization.LowerBounds.MinimaxMatching` — Minimax matching between UCBVI upper and Fano lower bounds. regret_to_pac_sample_complexity (sqrt monotonicity chain), lower_bound_le_upper_bound (Real.log_le_self), minimax_gap_is_log_A (field_simp), regret_implies_pac. All proofs complete; bridges Omega(sqrt(H^3*S*A*K)) lower to O(sqrt(H^3*S*A*K)) upper. Zero sorry.
- `RLGeneralization.Algorithms.QLearning` — Q-learning convergence. Update rule, Robbins-Siegmund step sizes, Bellman mixture identity, one-step error contraction, geometric decay, constant/diminishing step convergence, sample complexity. Zero sorry.
- `RLGeneralization.Algorithms.ModelBased` — Model-based RL. Model-based sample bound via simulation lemma, Dyna K-step contraction (induction on Bellman backup), end-to-end model+planning decomposition, model-based vs model-free rate comparison, sample size algebra. Zero sorry.
- `RLGeneralization.Algorithms.MCTS` — MCTS / UCT. Tree node structure, UCT score (value estimate + exploration bonus), value boundedness, bonus monotonicity, depth-limited horizon bound via geometric series, pigeonhole visit bound. Zero sorry.
- `RLGeneralization.Privacy.DPRewards` — Differential privacy for RL. Epsilon-DP, Laplace/Gaussian mechanisms, composition, private RL sample complexity, utility-privacy tradeoff. Zero sorry.
- `RLGeneralization.Optimization.SGD` — SGD convergence. Convex O(1/sqrt(T)) and strongly-convex O(1/(mu*T)) rates, one-step recurrence, telescope bound, minibatch variance reduction. Zero sorry.
- `RLGeneralization.MDP.Options` — Options framework for hierarchical RL (Sutton, Precup, Singh 1999). Option structure (initiation set, intra-option policy, termination probability), primitive options, option value Bellman equation, full-termination reduction, primitive-option Bellman reduction, option expressiveness, reward and next-value bounds. Zero sorry.
- `RLGeneralization.MDP.ConstrainedMDP` — Constrained MDPs (Altman 1999). CostFunction, CMDP structure, feasibility, Lagrangian, weak duality, Lagrangian decomposition, relaxation bound, cost tradeoff (budget monotonicity), budget monotonicity of Lagrangian, expected cost bounds, zero-multiplier identity. Zero sorry.
- `RLGeneralization.MDP.RewardShaping` — Reward shaping (Ng, Hazan, Russell 1999). Potential-based shaping r' = r + γΦ(s') - Φ(s), shaped Bellman shift (V_shaped = V - Φ), optimal policy invariance under potential-based shaping, advantage invariance, reward bounds. Zero sorry.
- `RLGeneralization.Concentration.RobbinsSiegmund` — Robbins-Siegmund convergence theorem for stochastic approximation. Defines RobbinsSiegmundHypothesis structure with deterministic recursion encoding. X_bounded_by_initial and partial_sum_pos_decrements_bounded are fully proved. The a.s. convergence and summability conclusions take their limits as hypotheses (wrapper form for the deterministic encoding).
- `RLGeneralization.Concentration.MDPFiltration` — MDP trajectory filtration: conditional expectations as finite sums, martingale differences with zero conditional mean, bounded differences, variance bounds. Finitary tower of expectations for finite-horizon MDPs. UCBVI confidence width definition. All proved, zero sorry.
- `RLGeneralization.Executable.CertifiedVI` — Certified value iteration: concrete MDP lifting, VI step-zero correctness.
- `RLGeneralization.Executable.LPCertificate` — LP duality certificates: duality gap bound, primal/dual bridges, occupancy nonnegativity.
- `RLGeneralization.Executable.TabularPlanner` — Tabular planner: epsilon-optimality from iteration count, per-iteration and total work bounds.
- `RLGeneralization.Test.SimpleMDP` — Sanity checks/examples for the trusted target.

### Weaker Modules


### Conditional Modules

- `RLGeneralization.MDP.AverageReward` — Average-reward MDPs. Span seminorm (nonneg, zero-iff-const, triangle), gain-bias equations, Bellman span contraction under ergodicity hypothesis, discounted-to-average limit. Zero sorry.
- `RLGeneralization.Concentration.Bennett` — Bennett function properties fully proved (double MVT, monotonicity, Bennett >= Bernstein comparison). Bernstein tail bound re-exported. Full Bennett tail P[S>=t]<=exp(-v*h(t/v)) requires Bennett-specific MGF proof.
- `RLGeneralization.Concentration.AzumaHoeffding` — Azuma-Hoeffding algebraic bridge. Confidence width derivation, tail probability inversion, UCBVI composition. Filtration construction and conditional sub-Gaussianity for MDP trajectories deferred.
- `RLGeneralization.Concentration.MDPConcentration` — One-step conditional sub-Gaussianity for MDP transitions via Hoeffding's lemma. Multi-step trajectory composition deferred.
- `RLGeneralization.Concentration.McDiarmid` — McDiarmid algebraic framework. BoundedDifferences structure, exponent algebra, Efron-Stein bridge, condDev bound. Full tail bound P[f(X)-E[f]>=eps]<=exp(-2eps^2/Sigma c_i^2) requires Doob martingale decomposition.
- `RLGeneralization.Concentration.McDiarmidFull` — McDiarmid variance bound Var(f)<=sum c_i^2 via Efron-Stein. Chebyshev tail bound (polynomial). Full exponential bound deferred.
- `RLGeneralization.Generalization.PolicyEvaluation` — LSTD value error bound, sample complexity. Regression rate taken as conditional hypothesis.
- `RLGeneralization.Generalization.DudleyRL` — Dudley entropy integral for RL function class generalization. Defines ValueFunctionClass, ParametricCoveringAssumption, LinearValueClass, DudleyRLHypothesis. Algebraic generalization bound inversions (rl_generalization_from_covering, linear_rl_generalization). Dudley bound packaged as opaque hypothesis; direct SLT.Dudley call deferred to Phase 5.
- `RLGeneralization.Generalization.UniformConvergence` — VC dimension to uniform convergence to PAC learning chain. VC-based uniform convergence bound, uniform convergence to PAC, full VC-PAC chain, RL application via policy class uniform convergence. Zero sorry.
- `RLGeneralization.Generalization.SLTBridge` — SLT library bridge to RL sample complexity. RL function classes (value, Q, Bellman error), covering numbers, uniform convergence from covering dimension, Bellman error concentration, Rademacher-to-sample complexity, Dudley entropy integral bridge. All conditional on SLT analytical hypotheses.
- `RLGeneralization.Bandits.LinearBandits` — LinUCB for linear bandits (Abbasi-Yadkori 2011). linUCBIndex = φ^T θ̂ + β·‖φ‖_{Λ^{-1}}. linUCBIndex_ge_dot, linUCBIndex_mono_beta, sum_sqrt_sq_le_card_mul_sum, linucb_regret_bound (all zero sorry given hypotheses). linucb_optimism (conditional: CS + confidence ellipsoid from SelfNormalized). linucb_regret_composition (1 sorry connecting x to Gram potential). linucb_vs_ucb1_sq, linucb_regret_sq_le_ucb1_sq (zero sorry).
- `RLGeneralization.Bandits.EXP3Bandit` — EXP3 bandit version with importance-weighted estimators. IW loss unbiasedness, variance bound, per-round K-bound, O(sqrt(KT log K)) optimized regret. Potential telescoping is conditional.
- `RLGeneralization.Bandits.UCBRegret` — UCB probabilistic regret bound. High-probability gap-dependent R_T <= sum(8L/Delta+2Delta), expected regret decomposition, worst-case E[R_T] <= O(K*sqrt(T*logT)), minimax gap analysis. Good event probability is conditional.
- `RLGeneralization.LinearFeatures.RegressionBridge` — LSVI-SLT bridge: type adapters, per-stage regression model, and deterministic sample-complexity chain. Key theorems take the regression rate as a hypothesis; lsvi_stage_slt_bound re-exports SLT's linear_minimax_rate.
- `RLGeneralization.BilinearRank.GOLF` — GOLF algorithm (Ch 8.5, Jin et al. NeurIPS 2021). GOLFInstance structure, golfConfidenceSet definition. golf_optimism_conditional (trivial: identity). golf_regret_decomposition (zero sorry: sum_le_sum + mul_sum). golf_bellman_error_sum_bound (zero sorry: sqrt_le_sqrt). golf_regret_bound (zero sorry: Cauchy-Schwarz composition). golf_sample_complexity_bound (zero sorry: sqrt algebra via div_le_div_iff₀ + nlinarith). Zero sorry.
- `RLGeneralization.Exploration.UCBVISimulation` — UCBVI-Simulation bridge: connects simulation lemma error propagation to UCBVI regret decomposition. value_error_from_transition, simulation_regret_composition (Finset.sum_le_sum), bonus_dominates_model_error. Full simulation-UCBVI end-to-end theorem with AzumaHoeffding concentration deferred to Phase 1.
- `RLGeneralization.Exploration.UCBVIProbability` — UCBVI with high-probability regret bounds. Concentration event, optimism on good event, high-probability regret R(K) ≤ O(H²√(SAK·log(SAHK/δ))), expected regret via good/bad event decomposition. Zero sorry.
- `RLGeneralization.PolicyOptimization.PolicyGradient` — Algebraic policy gradient core. Log-derivative trick, baseline invariance, advantage form, PDL composition, softmax parameterization. All algebraic proofs complete. Calculus layer (actual derivatives) deferred to Mathlib. Zero sorry.
- `RLGeneralization.PolicyOptimization.NPG` — Natural policy gradient: Fisher PSD, mirror-descent convergence analysis. Algebraic O(1/sqrt(T)) rate with optimal step size. Convergence theorems take KL/advantage hypotheses externally.
- `RLGeneralization.PolicyOptimization.TRPO` — TRPO/PPO policy optimization (Ch 12.2). trpo_surrogate_lower_bound_conditional (conditional specification: occupancy PDL + KL-TV bound), trpo_monotone_improvement_conditional (conditional specification). ppo_clipped_lower_bound (zero sorry: min_le_left), ppo_clipped_ratio_bounds (zero sorry). ppo_clipping_positive_advantage/ppo_clipping_negative_advantage (zero sorry algebraic). trpo_improvement_magnitude (zero sorry: linarith chain).
- `RLGeneralization.ImitationLearning.Basic` — Behavior-cloning H²ε bound, new DAgger-style H·ε bound (dagger_bound), one-step PDL identity, inductive value gap. DAgger bound uses constant per-step advantage hypothesis.
- `RLGeneralization.ImitationLearning.MaxEntIRL` — MaxEnt IRL (Ziebart 2008, Ch 13.4). maxentPolicy_partition_pos, maxentPolicy_prob_sum_one, maxentPolicy_log_prob, maxent_dual_linear_in_occupancy, and maxent_irl_dual_concave are zero sorry. maxent_feature_matching_from_hypothesis and maxent_irl_gradient_at_optimum_from_hypothesis are conditional on the MaxEnt optimality condition; maxent_reduces_to_soft_mdp is conditional on the soft-optimality bridge.
- `RLGeneralization.LinearMDP.Regret` — UCBVI-Lin regret wrappers. h_per_ep now dischargeable from isOptimistic via UCBVI.regret_from_optimism_gap. Remaining hypothesis: elliptical confidence set construction (matrix concentration).
- `RLGeneralization.LinearMDP.RegretFull` — Self-contained UCBVI-Lin regret theorem. ucbvi_lin_regret_self_contained composes elliptical potential with UCBVI-Lin via ucbvi_lin_regret_from_bonus_hypotheses. ucbvi_lin_vs_tabular_sq compares d^2*H^2 vs H^3*S*A (nlinarith). Remaining hypothesis: per-episode optimism from confidence set construction (matrix concentration).
- `RLGeneralization.LinearMDP.EllipticalBridge` — Bridge from elliptical potential to LinUCB regret. Instantiates elliptical_potential_unconditional for linucb_regret_composition. End-to-end LinUCB O(d*sqrt(T)) regret conditional on per-round optimism (Cauchy-Schwarz + confidence ellipsoid).
- `RLGeneralization.Complexity.EluderDimension` — Eluder dimension (Russo-Van Roy 2013) for function-approximation RL complexity. eluderIndependent/eluderDependent definitions, eluderDimension via sSup, linearFunctions class. eluderDimension_mono_eps (1 sorry: constructive witness argument). eluder_sum_bound (1 sorry: structural hypotheses connecting abstract dependence to eluder dimension). eluder_regret_bound conditional on optimism hypothesis. linear_eluder_dimension_le (1 sorry: linear rank bound).
- `RLGeneralization.Algorithms.LinearTD` — Linear TD(0) convergence. Feature map, projected Bellman equation, expected linear update, contraction factor, constant/diminishing step convergence, Tsitsiklis-Van Roy approximation bound, sample complexity. Positive-definite A matrix taken as hypothesis. Zero sorry.
- `RLGeneralization.Algorithms.GenerativeQLearning` — Generative model to value iteration sample complexity composition. vi_error_composition_conditional (linarith), generative_vi_budget_conditional (from hypothesis), two_phase_sample_complexity_formula (nlinarith). Algebraic skeleton; genuine end-to-end composition with pac_rl_generative_model_bernstein and value_iteration_threshold deferred to Phase 1.
- `RLGeneralization.Algorithms.SARSA` — SARSA on-policy TD learning. SARSA update rule, expected SARSA, noise decomposition with conditional-expectation-zero and bounded noise, SARSA vs Q-learning gap, Bellman contraction for the policy evaluation operator. Zero sorry.
- `RLGeneralization.Approximation.RKHS` — RKHS definitions. Reproducing kernel structure, Gram matrix, kernel ridge regression, regularization bias-variance, common kernels. Zero sorry.
- `RLGeneralization.Approximation.NeuralNetwork` — Neural network approximation. Two-layer networks, ReLU activation, UAT statement, depth separation, Barron rate. Zero sorry.
- `RLGeneralization.MDP.HJB` — Hamilton-Jacobi-Bellman stub. HJB equation, Hamiltonian, verification theorem algebraic core, discrete Bellman as HJB. Blocked by ODE/viscosity solutions. Zero sorry.
- `RLGeneralization.MDP.POMDP` — POMDP stub. POMDP structure, belief states, Bayesian belief update with normalization proof, POMDP-as-belief-MDP reduction. Zero sorry.
- `RLGeneralization.MDP.MultiAgent` — Multi-agent RL stub. Markov games, Nash equilibrium, two-player zero-sum, matrix game payoff bounds, cooperative characterization. Zero sorry.
- `RLGeneralization.Concentration.StochasticCalculus` — Stochastic calculus stub. Ito process definition, Ito isometry statement, Euler-Maruyama discretization, covariance matrix. Blocked by Brownian motion upstream (Degenne et al.). Zero sorry.
- `RLGeneralization.Concentration.CLT` — Central Limit Theorem stub. CLT statement structure, normalized variance identity, Berry-Esseen rate, Mill ratio. Characteristic-function infrastructure exists in Mathlib, but the Levy-continuity and Fourier-smoothing proof stack needed for CLT and Berry-Esseen is not yet assembled here. Zero sorry.
- `RLGeneralization.Concentration.TrajectoryMeasure` — Trajectory probability measure via PMF construction. Proves sum-to-one, expectation-as-sum, martingale zero mean, variance bound. Azuma-Hoeffding tail and UCBVI high-probability are conditional on Mathlib filtration connection.

## Draft Root

- Modules: 5
- Build command: `lake build RLGeneralization.Draft`

- `RLGeneralization.BilinearRank.Basic` — Draft Bellman-rank degenerate helper and GOLF wrappers.
- `RLGeneralization.OfflineRL.FunctionApprox` — Offline RL with function approximation. FQI contraction under realizability, eluder-dimension suboptimality, pessimism-coverage tradeoff. All conditional.
- `RLGeneralization.MDP.AverageRewardNonasymptotic` — Average-reward nonasymptotic sample complexity. Finite-sample bound and span bound conditional on mixing time.
- `RLGeneralization.MDP.POmdpBeliefMDP` — POMDP belief-MDP reduction. Belief-state process as MDP and value equivalence. Conditional on measurability.
- `RLGeneralization.BilinearRank.RepresentationBound` — Bellman rank and eluder dimension connection. Low-rank MDP regret bounds. Conditional.

## Excluded Modules

- Modules: 2

- `RLGeneralization.Concentration.MarkovChain` — Excluded frontier file. Current theorem surface is too thin for trusted use and does not yet formalize a genuine concentration result.
- `RLGeneralization.Test.ConcreteExample` — Concrete worked example and sanity-check module outside the trusted benchmark root.
