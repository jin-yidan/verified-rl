# Module Index

119 Lean 4 modules organized by topic. Each module is classified as:

- **exact** — Fully proved, no external analytical hypotheses
- **conditional** — Algebraic content proved, measure-theoretic or spectral steps taken as hypotheses

All modules compile with zero `sorry` and pass `lean4checker`.

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
| `MDP.SimulationLemma` | exact | Kearns-Singh simulation inequality |
| `MDP.SimulationResolvent` | exact | Exact simulation resolvent identity |
| `MDP.FiniteHorizon` | exact | Finite-horizon backward induction |
| `MDP.LPFormulation` | conditional | LP primal/dual, weak duality, occupancy-dual connection |
| `MDP.AverageReward` | conditional | Span seminorm, gain-bias equations, discounted-to-average limit |
| `MDP.HJB` | conditional | Hamilton-Jacobi-Bellman, verification theorem (blocked by ODE/viscosity) |
| `MDP.POMDP` | conditional | Belief states, Bayesian update, POMDP-as-belief-MDP |
| `MDP.MultiAgent` | conditional | Markov games, Nash equilibrium, minimax |
| `MDP.ConstrainedMDP` | exact | Lagrangian, weak duality, budget monotonicity |
| `MDP.Options` | exact | Temporally extended actions, option value bounds |
| `MDP.RewardShaping` | exact | Potential-based shaping, policy invariance (Ng et al. 1999) |
| `MDP.AverageRewardNonasymptotic` | conditional | Finite-sample bound (draft) |
| `MDP.POmdpBeliefMDP` | conditional | Belief-MDP value equivalence (draft) |

## Concentration Inequalities (25 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `Concentration.Bernstein` | exact | Bernstein MGF bound (not in Mathlib), tail bound, two-sided |
| `Concentration.BennettMGF` | exact | Full Bennett inequality via MGF, Bennett >= Bernstein |
| `Concentration.Bennett` | conditional | Bennett function properties (double MVT, monotonicity) |
| `Concentration.Hoeffding` | exact | Union bound bridge, PAC composition |
| `Concentration.GenerativeModelCore` | exact | Product measure, coordinate independence |
| `Concentration.GenerativeModel` | exact | End-to-end PAC bound with Bernstein log-rate |
| `Concentration.DiscreteConcentration` | exact | L1 concentration, multinomial bound |
| `Concentration.SubGaussian` | conditional | Sub-Gaussian bridge definitions |
| `Concentration.AzumaHoeffding` | conditional | Azuma-Hoeffding for finite-horizon MDPs |
| `Concentration.MDPConcentration` | conditional | One-step conditional sub-Gaussianity |
| `Concentration.McDiarmid` | conditional | Bounded differences framework |
| `Concentration.McDiarmidFull` | conditional | Variance bound via Efron-Stein |
| `Concentration.MatrixBernstein` | conditional | Matrix Bernstein algebraic core |
| `Concentration.SelfNormalized` | conditional | Self-normalized bounds for LinUCB |
| `Concentration.JohnsonLindenstrauss` | conditional | JL random projection lemma |
| `Concentration.Talagrand` | conditional | Convex distance inequality |
| `Concentration.LargeDeviations` | conditional | Rate function, Cramer upper bound |
| `Concentration.Isoperimetric` | conditional | Gaussian, hypercube, Levy |
| `Concentration.PhiEntropy` | conditional | Modified log-Sobolev, Herbst argument |
| `Concentration.StochasticCalculus` | conditional | Ito process (blocked by Brownian motion) |
| `Concentration.CLT` | conditional | CLT statement, Berry-Esseen rate |
| `Concentration.RobbinsSiegmund` | conditional | Robbins-Siegmund convergence |
| `Concentration.MDPFiltration` | conditional | Trajectory filtration, martingale differences |
| `Concentration.TrajectoryMeasure` | conditional | PMF construction, Azuma-Hoeffding tail |
| `Concentration.MarkovChain` | excluded | Excluded: theorem surface too thin |

## Bandits (8 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `Bandits.UCB` | exact | Gap-dependent regret, worst-case O(K sqrt(T log T)) |
| `Bandits.BanditConcentration` | exact | Bernoulli probability space, Hoeffding for arm means |
| `Bandits.UCBRegret` | conditional | High-probability regret, expected regret, minimax gap |
| `Bandits.EXP3` | exact | Adversarial regret O(sqrt(T K log K)) |
| `Bandits.EXP3Bandit` | conditional | Importance-weighted estimators |
| `Bandits.LinearBandits` | conditional | LinUCB, optimism, O(d sqrt(T)) regret |
| `Bandits.LowerBound` | exact | Le Cam two-point, Omega(sqrt(KT)) lower bound |
| `Bandits.ThompsonSampling` | conditional | Information ratio, Bayesian regret |

## Generalization (10 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `Generalization.SampleComplexity` | exact | Deterministic comparison core |
| `Generalization.ComponentWise` | exact | Component-wise resolvent bounds |
| `Generalization.MinimaxSampleComplexity` | exact | Minimax deterministic core, variance bounds |
| `Generalization.PACBayes` | exact | KL divergence, Gibbs inequality, Catoni/McAllester forms |
| `Generalization.FiniteHorizonSampleComplexity` | exact | Inductive error propagation, H^2 epsilon bound |
| `Generalization.TransferRL` | exact | Sim-to-real, source-target gap, domain randomization |
| `Generalization.PolicyEvaluation` | conditional | LSTD value error, sample complexity |
| `Generalization.DudleyRL` | conditional | Dudley entropy integral for RL |
| `Generalization.UniformConvergence` | conditional | VC -> uniform convergence -> PAC chain |
| `Generalization.SLTBridge` | conditional | SLT library bridge to RL sample complexity |

## Complexity Theory (6 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `Complexity.VCDimension` | exact | Growth function, Sauer-Shelah, convergence rate |
| `Complexity.Rademacher` | exact | Massart bound, contraction principle |
| `Complexity.Symmetrization` | exact | Factor-2 symmetrization, McDiarmid concentration |
| `Complexity.CoveringPacking` | exact | N(eps) <= P(eps) <= N(eps/2), volumetric bounds |
| `Complexity.GenericChaining` | exact | Gamma_2 functional, Dudley equivalence |
| `Complexity.EluderDimension` | conditional | Eluder dimension, regret bound |

## Exploration (6 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `Exploration.UCBVI` | exact | Optimism, per-episode, cumulative, O(sqrt(H^3 SAK)) |
| `Exploration.VarianceUCBVI` | exact | Bernstein bonus, O(sqrt(HSAK)) improving H^3 -> H |
| `Exploration.BatchUCBVI` | exact | Harmonic-sqrt bound, Cauchy-Schwarz |
| `Exploration.RewardFree` | exact | Reward-free exploration, coverage monotonicity |
| `Exploration.UCBVISimulation` | conditional | Simulation-UCBVI bridge |
| `Exploration.UCBVIProbability` | conditional | High-probability regret with concentration event |

## Policy Optimization (6 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `PolicyOptimization.PolicyGradient` | conditional | Log-derivative trick, baseline invariance, softmax |
| `PolicyOptimization.CPI` | exact | Conservative policy iteration, resolvent improvement |
| `PolicyOptimization.Optimality` | exact | Gradient domination nonnegativity |
| `PolicyOptimization.NPG` | conditional | Natural policy gradient, mirror descent, O(1/sqrt(T)) |
| `PolicyOptimization.TRPO` | conditional | TRPO surrogate bound, PPO clipping |
| `PolicyOptimization.ActorCritic` | conditional | Advantage decomposition, critic bias, variance reduction |

## Algorithms (6 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `Algorithms.QLearning` | exact | Bellman mixture, geometric decay, sample complexity |
| `Algorithms.SARSA` | exact | On-policy TD, noise decomposition, comparison with Q-learning |
| `Algorithms.LinearTD` | conditional | Projected Bellman, Tsitsiklis-Van Roy bound |
| `Algorithms.GenerativeQLearning` | conditional | Generative model -> VI composition |
| `Algorithms.ModelBased` | conditional | Dyna K-step contraction, model-free comparison |
| `Algorithms.MCTS` | exact | UCT value estimates, exploration bonus, horizon bound |

## Linear MDP & Features (7 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `LinearMDP.Basic` | exact | Linear-MDP definition, optimal Q linearity |
| `LinearMDP.EllipticalPotential` | exact | Elliptical potential lemma (fully unconditional) |
| `LinearMDP.Regret` | conditional | UCBVI-Lin regret wrappers |
| `LinearMDP.RegretFull` | conditional | Self-contained UCBVI-Lin regret |
| `LinearMDP.EllipticalBridge` | conditional | Elliptical potential -> LinUCB bridge |
| `LinearFeatures.LSVI` | exact | LSVI error propagation, 2H^2 eta bound |
| `LinearFeatures.RegressionBridge` | conditional | LSVI-SLT bridge |

## Bilinear Rank (4 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `BilinearRank.Auxiliary` | exact | Bellman-rank definitions, bilinear bounds |
| `BilinearRank.GOLF` | exact | GOLF algorithm, eluder-based regret |
| `BilinearRank.Basic` | conditional | Bellman-rank helpers (draft) |
| `BilinearRank.RepresentationBound` | conditional | Bellman rank / eluder connection (draft) |

## Offline RL (3 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `OfflineRL.FQI` | exact | Fitted Q-iteration contraction |
| `OfflineRL.Pessimism` | exact | LCB Q-function, concentrability, offline regret |
| `OfflineRL.FunctionApprox` | conditional | FQI under realizability (draft) |

## Other (14 modules)

| Module | Status | Contents |
|--------|--------|----------|
| `ImitationLearning.Basic` | conditional | Behavior cloning H^2 epsilon, DAgger |
| `ImitationLearning.MaxEntIRL` | conditional | MaxEnt IRL, soft-optimal policy |
| `LQR.Basic` | exact | LQR definitions, Riccati infrastructure |
| `LQR.RiccatiPolicy` | exact | Riccati recursion, closed-loop Bellman, policy gradient |
| `LowerBounds.FanoLeCam` | exact | Fano, Le Cam, Assouad, tabular RL lower bound |
| `LowerBounds.MinimaxMatching` | exact | UCBVI upper matches Fano lower |
| `Privacy.DPRewards` | exact | Laplace/Gaussian DP, composition, RL sample complexity |
| `Optimization.SGD` | exact | Convex O(1/sqrt(T)), strongly-convex O(1/(mu T)) |
| `Approximation.RKHS` | conditional | Reproducing kernels, Gram matrices, KRR |
| `Approximation.NeuralNetwork` | conditional | Two-layer networks, UAT, Barron rate |
| `Executable.CertifiedVI` | conditional | Certified value iteration interface |
| `Executable.LPCertificate` | conditional | LP duality certificate verification |
| `Executable.TabularPlanner` | conditional | Tabular planner with complexity bounds |
| `Test.SimpleMDP` | exact | Sanity checks |
