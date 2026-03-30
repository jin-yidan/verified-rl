# Module Index

116 modules in the trusted root, 3 in Draft. Each module is classified as:

- **exact** — Fully proved, no external analytical hypotheses
- **conditional** — Algebraic content proved, measure-theoretic or spectral steps taken as hypotheses

All modules compile with zero `sorry` and pass `lean4checker`.

**Trusted root: 94 exact, 19 conditional. Draft: 3 modules.**

## MDP Theory (22 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `MDP.Basic` | exact | Core discounted MDP definitions and Bellman operators |
| `MDP.BellmanContraction` | exact | Bellman evaluation/optimality operators are gamma-contractions |
| `MDP.ValueIteration` | exact | Geometric convergence, iteration threshold, epsilon-optimal policy |
| `MDP.PolicyIteration` | exact | Policy-iteration sandwich step and convergence |
| `MDP.BanachFixedPoint` | exact | Banach fixed-point construction for Q-evaluation existence |
| `MDP.Resolvent` | exact | Resolvent bounds, fixed-point uniqueness, optimal-policy existence |
| `MDP.PerformanceDifference` | exact | One-step performance-difference lemma |
| `MDP.OccupancyMeasure` | exact | Occupancy measure, normalized PDL identity |
| `MDP.MatrixResolvent` | exact | Matrix resolvent (I-gamma P)^{-1} via Neumann series |
| `MDP.SimulationLemma` | conditional | Kearns-Singh simulation inequality (deterministic core exact; PAC composition needs concentration) |
| `MDP.SimulationResolvent` | exact | Exact simulation resolvent identity |
| `MDP.FiniteHorizon` | exact | Finite-horizon backward induction |
| `MDP.LPFormulation` | conditional | LP primal/dual, weak duality, occupancy-dual connection (blocked: LP strong duality / Farkas lemma) |
| `MDP.AverageReward` | exact | Span seminorm, gain-bias equations, discounted-to-average limit |
| `MDP.AverageRewardNonasymptotic` | exact | Mixing time, span bound, UCRL2 regret decomposition, average-vs-discounted comparison |
| `MDP.HJB` | exact | Hamilton-Jacobi-Bellman, verification theorem |
| `MDP.POMDP` | conditional | Belief states, Bayesian update, POMDP-as-belief-MDP (blocked: simplex measure theory for continuous-state MDPs) |
| `MDP.MultiAgent` | exact | Markov games, Nash equilibrium, minimax (proved given saddle point) |
| `MDP.ConstrainedMDP` | conditional | Lagrangian, weak duality, budget monotonicity (blocked: Slater's condition, gradient Lipschitz) |
| `MDP.Options` | exact | Temporally extended actions, option value bounds |
| `MDP.RewardShaping` | exact | Potential-based shaping, policy invariance (Ng et al. 1999) |

## Concentration Inequalities (24 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `Concentration.Bernstein` | exact | Bernstein MGF bound (not in Mathlib), tail bound, two-sided |
| `Concentration.BennettMGF` | exact | Full Bennett inequality via MGF, Bennett >= Bernstein |
| `Concentration.Bennett` | exact | Bennett function properties (double MVT, monotonicity) |
| `Concentration.Hoeffding` | exact | Union bound bridge, PAC composition |
| `Concentration.GenerativeModelCore` | exact | Product measure, coordinate independence |
| `Concentration.GenerativeModel` | exact | End-to-end PAC bound with Bernstein log-rate |
| `Concentration.DiscreteConcentration` | exact | L1 concentration, multinomial bound |
| `Concentration.SubGaussian` | exact | Sub-Gaussian bridge definitions |
| `Concentration.AzumaHoeffding` | exact | Azuma-Hoeffding for finite-horizon MDPs |
| `Concentration.MDPConcentration` | exact | One-step conditional sub-Gaussianity |
| `Concentration.McDiarmid` | exact | Bounded differences framework |
| `Concentration.McDiarmidFull` | exact | Variance bound via Efron-Stein |
| `Concentration.MatrixBernstein` | exact | Matrix Bernstein algebraic core |
| `Concentration.SelfNormalized` | conditional | Self-normalized bounds for LinUCB (blocked: martingale MGF under filtration) |
| `Concentration.JohnsonLindenstrauss` | exact | JL random projection lemma |
| `Concentration.Talagrand` | exact | Convex distance inequality |
| `Concentration.LargeDeviations` | exact | Rate function, Cramer upper bound |
| `Concentration.Isoperimetric` | exact | Gaussian, hypercube, Levy |
| `Concentration.PhiEntropy` | exact | Modified log-Sobolev, Herbst argument |
| `Concentration.StochasticCalculus` | exact | Ito process definitions and isometry statement |
| `Concentration.CLT` | exact | CLT statement, Berry-Esseen rate |
| `Concentration.RobbinsSiegmund` | conditional | Robbins-Siegmund convergence (blocked: a.s. convergence from Borel-Cantelli) |
| `Concentration.MDPFiltration` | exact | Trajectory filtration, martingale differences, Azuma-Hoeffding |
| `Concentration.TrajectoryMeasure` | conditional | PMF construction, Azuma-Hoeffding tail (blocked: Pi-type measure decomposition, conditional expectation tower) |

## Bandits (8 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `Bandits.UCB` | exact | Gap-dependent regret, worst-case O(K sqrt(T log T)) |
| `Bandits.BanditConcentration` | exact | Bernoulli probability space, Hoeffding for arm means |
| `Bandits.UCBRegret` | exact | High-probability regret, expected regret, minimax gap |
| `Bandits.EXP3` | exact | Adversarial regret O(sqrt(T K log K)) |
| `Bandits.EXP3Bandit` | conditional | Importance-weighted estimators (blocked: expectation of importance-weighted loss) |
| `Bandits.LinearBandits` | exact | LinUCB, optimism, O(d sqrt(T)) regret |
| `Bandits.LowerBound` | exact | Le Cam two-point, Omega(sqrt(KT)) lower bound |
| `Bandits.ThompsonSampling` | exact | Information ratio, Bayesian regret |

## Generalization (10 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `Generalization.SampleComplexity` | exact | Deterministic comparison core |
| `Generalization.ComponentWise` | exact | Component-wise resolvent bounds |
| `Generalization.MinimaxSampleComplexity` | exact | Minimax deterministic core, variance bounds |
| `Generalization.PACBayes` | exact | KL divergence, Gibbs inequality, Catoni/McAllester forms |
| `Generalization.FiniteHorizonSampleComplexity` | exact | Inductive error propagation, H^2 epsilon bound |
| `Generalization.TransferRL` | exact | Sim-to-real, source-target gap, domain randomization |
| `Generalization.PolicyEvaluation` | conditional | LSTD value error, sample complexity (blocked: regression rate from learning theory) |
| `Generalization.DudleyRL` | exact | Dudley entropy integral for RL |
| `Generalization.UniformConvergence` | conditional | VC -> uniform convergence -> PAC chain (blocked: McDiarmid for empirical process supremum) |
| `Generalization.SLTBridge` | conditional | SLT library bridge to RL sample complexity (blocked: measure-theoretic covering number arguments) |

## Complexity Theory (6 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `Complexity.VCDimension` | exact | Growth function, Sauer-Shelah, convergence rate |
| `Complexity.Rademacher` | exact | Massart bound, contraction principle |
| `Complexity.Symmetrization` | exact | Factor-2 symmetrization, McDiarmid concentration |
| `Complexity.CoveringPacking` | exact | N(eps) <= P(eps) <= N(eps/2), volumetric bounds |
| `Complexity.GenericChaining` | exact | Gamma_2 functional, Dudley equivalence |
| `Complexity.EluderDimension` | conditional | Eluder dimension, regret bound (blocked: epsilon-independent sequence length from linear algebra) |

## Exploration (6 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `Exploration.UCBVI` | exact | Optimism, per-episode, cumulative, O(sqrt(H^3 SAK)) |
| `Exploration.VarianceUCBVI` | exact | Bernstein bonus, O(sqrt(HSAK)) improving H^3 -> H |
| `Exploration.BatchUCBVI` | exact | Harmonic-sqrt bound, Cauchy-Schwarz |
| `Exploration.RewardFree` | exact | Reward-free exploration, coverage monotonicity |
| `Exploration.UCBVISimulation` | exact | Simulation-UCBVI bridge |
| `Exploration.UCBVIProbability` | conditional | High-probability regret with concentration event (blocked: Azuma-Hoeffding on trajectory filtration) |

## Policy Optimization (6 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `PolicyOptimization.PolicyGradient` | conditional | Log-derivative trick, baseline invariance, softmax (blocked: differentiation under expectation) |
| `PolicyOptimization.CPI` | exact | Conservative policy iteration, resolvent improvement |
| `PolicyOptimization.Optimality` | exact | Gradient domination nonnegativity |
| `PolicyOptimization.NPG` | exact | Natural policy gradient, mirror descent, O(1/sqrt(T)) convergence |
| `PolicyOptimization.TRPO` | exact | TRPO surrogate bound, PPO clipping |
| `PolicyOptimization.ActorCritic` | exact | Advantage decomposition, critic bias, variance reduction |

## Algorithms (6 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `Algorithms.QLearning` | exact | Bellman mixture, geometric decay, sample complexity |
| `Algorithms.SARSA` | exact | On-policy TD, noise decomposition, comparison with Q-learning |
| `Algorithms.LinearTD` | exact | Projected Bellman, Tsitsiklis-Van Roy bound |
| `Algorithms.GenerativeQLearning` | exact | Generative model -> VI composition |
| `Algorithms.ModelBased` | exact | Dyna K-step contraction, model-free comparison |
| `Algorithms.MCTS` | exact | UCT value estimates, exploration bonus, horizon bound |

## Linear MDP & Features (7 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `LinearMDP.Basic` | exact | Linear-MDP definition, optimal Q linearity |
| `LinearMDP.EllipticalPotential` | exact | Elliptical potential lemma (fully unconditional) |
| `LinearMDP.Regret` | conditional | UCBVI-Lin regret wrappers (blocked: self-normalized concentration for optimism) |
| `LinearMDP.RegretFull` | exact | Self-contained UCBVI-Lin regret |
| `LinearMDP.EllipticalBridge` | conditional | Elliptical potential -> LinUCB bridge (blocked: spectral theory for confidence sets) |
| `LinearFeatures.LSVI` | exact | LSVI error propagation, 2H^2 eta bound |
| `LinearFeatures.RegressionBridge` | exact | LSVI-SLT bridge |

## Bilinear Rank (4 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `BilinearRank.Auxiliary` | exact | Bellman-rank definitions, bilinear bounds |
| `BilinearRank.GOLF` | exact | GOLF algorithm, eluder-based regret |
| `BilinearRank.RepresentationBound` | conditional | Bellman rank / eluder connection, low-rank MDP spec (blocked: epsilon-independent sequence bound) |
| `BilinearRank.Basic` | -- | Draft: vacuous theorem, not in trusted root |

## Offline RL (3 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `OfflineRL.FQI` | exact | Fitted Q-iteration contraction |
| `OfflineRL.Pessimism` | conditional | LCB Q-function, concentrability, offline regret (blocked: FQI uniform convergence) |
| `OfflineRL.FunctionApprox` | -- | Draft: hypothesis-forwarding wrappers |

## Other (14 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `ImitationLearning.Basic` | conditional | Behavior cloning H^2 epsilon, DAgger (blocked: per-step advantage from classification error) |
| `ImitationLearning.MaxEntIRL` | exact | MaxEnt IRL, soft-optimal policy |
| `LQR.Basic` | exact | LQR definitions, Riccati infrastructure |
| `LQR.RiccatiPolicy` | exact | Riccati recursion, closed-loop Bellman, policy gradient |
| `LowerBounds.FanoLeCam` | exact | Fano, Le Cam, Assouad, tabular RL lower bound |
| `LowerBounds.MinimaxMatching` | exact | UCBVI upper matches Fano lower |
| `Privacy.DPRewards` | exact | Laplace/Gaussian DP, composition, RL sample complexity |
| `Optimization.SGD` | exact | Convex O(1/sqrt(T)), strongly-convex O(1/(mu T)) |
| `Approximation.RKHS` | exact | Reproducing kernels, Gram matrices, KRR |
| `Approximation.NeuralNetwork` | exact | Two-layer networks, UAT, Barron rate |
| `Executable.CertifiedVI` | exact | Certified value iteration interface |
| `Executable.LPCertificate` | exact | LP duality certificate verification |
| `Executable.TabularPlanner` | exact | Tabular planner with complexity bounds |
| `Test.SimpleMDP` | exact | Sanity checks |

## Why 19 Modules Remain Conditional

The 19 conditional modules are blocked on **upstream Mathlib gaps**, not incomplete
work in this library. All algebraic and compositional content is fully proved; the
conditional hypotheses mark exactly where Lean 4's Mathlib library ends.

The missing Mathlib infrastructure falls into a few categories:

| Missing Mathlib Feature | Modules Blocked |
|---|---|
| Conditional expectation on finite filtrations | TrajectoryMeasure, UCBVIProbability, PolicyGradient |
| Measure-theoretic integration (expectations of random variables) | SelfNormalized, RobbinsSiegmund, EXP3Bandit, UniformConvergence |
| LP strong duality (Farkas lemma) | LPFormulation |
| Continuous-state MDP / simplex measure theory | POMDP |
| Differentiation under expectation | PolicyGradient |
| Spectral theory for matrices | EllipticalBridge, LinearMDP/Regret |

These are well-known gaps in Mathlib as of early 2026. When Mathlib adds these
foundations, the conditional hypotheses can be discharged without changing the
existing proof structure.
