-- RLGeneralization: Formally Verified RL Theory in Lean 4
--
-- Formalizes core results from Agarwal, Brantley, Jiang, Kakade, Sun,
-- "Reinforcement Learning: Theory and Algorithms" (2026).
--
-- VERIFICATION STATUS:
--   This file is the trusted benchmark target.
--   `lake build RLGeneralization` is the enforced build target for exactly
--   these imports.
--   Scope: core discounted/finite-horizon MDP theory,
--   deterministic generalization infrastructure, concentration inequalities,
--   Banach fixed-point policy-evaluation infrastructure, Bellman-rank
--   auxiliaries, UCBVI algebraic core, optimal Q linearity for linear MDPs,
--   and policy-gradient/CPI algebraic identities.
--
--   Modules marked `conditional` (e.g. RegressionBridge) take key
--   analytical hypotheses externally; see verification_manifest.json
--   for per-module status.  Pure proof-scaffolding and wrapper modules
--   live in `RLGeneralization.Draft`.

-- MDP definitions and Bellman equations
import RLGeneralization.MDP.Basic
-- Bellman contraction and value bounds
import RLGeneralization.MDP.BellmanContraction
-- Simulation inequality (Kearns-Singh style)
import RLGeneralization.MDP.SimulationLemma
-- Value iteration convergence core
import RLGeneralization.MDP.ValueIteration
-- Sandwich contraction and convergence lemmas
import RLGeneralization.MDP.PolicyIteration
-- Resolvent bounds, fixed-point optimality, and crude value bounds
import RLGeneralization.MDP.Resolvent
-- Banach fixed-point bridge for policy Q-evaluation existence/convergence
import RLGeneralization.MDP.BanachFixedPoint
-- Algebraic performance-difference infrastructure
import RLGeneralization.MDP.PerformanceDifference
-- Occupancy measure, transition powers, truncated PDL
import RLGeneralization.MDP.OccupancyMeasure
-- Matrix resolvent (I - γP^π)⁻¹ via Neumann series
import RLGeneralization.MDP.MatrixResolvent
-- Exact simulation resolvent identity
import RLGeneralization.MDP.SimulationResolvent
-- Finite-horizon MDPs and backward induction
import RLGeneralization.MDP.FiniteHorizon
-- LP formulation of discounted MDPs: primal/dual, weak duality
import RLGeneralization.MDP.LPFormulation
-- Average-reward MDPs: span seminorm, gain-bias equations
import RLGeneralization.MDP.AverageReward
-- Average-reward non-asymptotic: mixing time, span bound, UCRL2 regret
import RLGeneralization.MDP.AverageRewardNonasymptotic
-- Empirical model, comparison lemmas, and component-wise bounds
import RLGeneralization.Generalization.SampleComplexity
-- Component-wise value bounds
import RLGeneralization.Generalization.ComponentWise
-- LSVI approximate dynamic-programming core
import RLGeneralization.LinearFeatures.LSVI
-- Transfer RL: sim-to-real, source-target value gap, sample reuse
import RLGeneralization.Generalization.TransferRL
-- Concentration: Hoeffding bridge + union bound + PAC composition
import RLGeneralization.Concentration.Hoeffding
-- Concentration: Bernstein MGF bound + tail bound (Appendix A)
import RLGeneralization.Concentration.Bernstein
-- Concentration: Bennett's inequality and Bennett-Bernstein comparison
import RLGeneralization.Concentration.Bennett
-- Concentration: Bennett MGF bound and full Bennett tail inequality
import RLGeneralization.Concentration.BennettMGF
-- Concentration: Matrix Bernstein inequality (algebraic core)
import RLGeneralization.Concentration.MatrixBernstein
-- Concentration: Self-normalized bounds for LinUCB (Abbasi-Yadkori et al. 2011)
import RLGeneralization.Concentration.SelfNormalized
-- Concentration: Sub-Gaussian bridge definitions for Azuma-Hoeffding
import RLGeneralization.Concentration.SubGaussian
-- Concentration: Azuma-Hoeffding bridge for finite-horizon MDP concentration
import RLGeneralization.Concentration.AzumaHoeffding
-- Concentration: MDP trajectory concentration (Hoeffding's lemma for transitions)
import RLGeneralization.Concentration.MDPConcentration
-- Concentration: McDiarmid bounded differences inequality
import RLGeneralization.Concentration.McDiarmid
-- Concentration: McDiarmid variance bound via Efron-Stein
import RLGeneralization.Concentration.McDiarmidFull
-- Concentration: Johnson-Lindenstrauss random projection lemma
import RLGeneralization.Concentration.JohnsonLindenstrauss
-- Concentration: Talagrand convex distance inequality
import RLGeneralization.Concentration.Talagrand
-- Concentration: Large deviation principles / Cramer's theorem
import RLGeneralization.Concentration.LargeDeviations
-- Concentration: Isoperimetric inequalities (Gaussian, hypercube, Levy)
import RLGeneralization.Concentration.Isoperimetric
-- Concentration: Phi-entropy and modified log-Sobolev inequalities
import RLGeneralization.Concentration.PhiEntropy
-- Concentration: trusted generative-model probability space and PAC bound
import RLGeneralization.Concentration.GenerativeModelCore
-- Concentration: Bernstein PAC analysis, canonical fixed-point construction
import RLGeneralization.Concentration.GenerativeModel
-- Concentration: Discrete distribution L1 concentration, multinomial bound, RL transition
import RLGeneralization.Concentration.DiscreteConcentration
-- Generalization: minimax deterministic core, variance/deviation bounds
import RLGeneralization.Generalization.MinimaxSampleComplexity
-- Generalization: PAC-Bayes bounds, KL divergence, RL instantiation
import RLGeneralization.Generalization.PACBayes
-- Generalization: LSTD policy evaluation with conditional finite-sample bound
import RLGeneralization.Generalization.PolicyEvaluation
-- Generalization: Dudley entropy integral for RL function class generalization
import RLGeneralization.Generalization.DudleyRL
-- Generalization: finite-horizon minimax sample complexity
import RLGeneralization.Generalization.FiniteHorizonSampleComplexity
-- Generalization: VC → uniform convergence → PAC learning chain
import RLGeneralization.Generalization.UniformConvergence
-- Generalization: SLT library bridge to RL sample complexity
import RLGeneralization.Generalization.SLTBridge
-- Bandits: ETC oracle witness, UCB algebraic core, gap-dependent regret
import RLGeneralization.Bandits.UCB
-- Bandits: LinUCB for linear bandits (Abbasi-Yadkori 2011)
import RLGeneralization.Bandits.LinearBandits
-- Bandits: probability space, Hoeffding concentration for arm means
import RLGeneralization.Bandits.BanditConcentration
-- Bandits: EXP3 adversarial bandit regret bound (exponential weights)
import RLGeneralization.Bandits.EXP3
-- Bandits: EXP3 bandit version with importance-weighted estimators
import RLGeneralization.Bandits.EXP3Bandit
-- Bandits: UCB probabilistic regret bound, expected regret, minimax gap
import RLGeneralization.Bandits.UCBRegret
-- Bandits: minimax lower bound via Le Cam's two-point method
import RLGeneralization.Bandits.LowerBound
-- Bandits: Thompson Sampling Bayesian regret analysis
import RLGeneralization.Bandits.ThompsonSampling
-- LSVI-SLT regression bridge: connects LSVI to statistical learning theory
import RLGeneralization.LinearFeatures.RegressionBridge
-- Bellman-rank auxiliary structure and exact bilinear bounds
import RLGeneralization.BilinearRank.Auxiliary
-- GOLF algorithm: bilinear class exploration, eluder regret bound
import RLGeneralization.BilinearRank.GOLF
-- Bellman-rank / eluder dimension connection, low-rank MDP regret spec
import RLGeneralization.BilinearRank.RepresentationBound

-- UCBVI definitions and regret-decomposition core
import RLGeneralization.Exploration.UCBVI
-- Variance-aware UCBVI: Bernstein-style bonuses, H-factor improvement
import RLGeneralization.Exploration.VarianceUCBVI
-- UCBVI-Simulation bridge: connects simulation lemma to UCBVI regret
import RLGeneralization.Exploration.UCBVISimulation
-- Batch UCBVI: harmonic-sqrt bound, Cauchy-Schwarz bonus bound
import RLGeneralization.Exploration.BatchUCBVI
-- Reward-free exploration: dataset, planning bounds, coverage monotonicity
import RLGeneralization.Exploration.RewardFree
-- UCBVI with actual probability bounds (concentration event, optimism, high-probability regret)
import RLGeneralization.Exploration.UCBVIProbability
-- Policy-gradient definitions and algebraic identities
import RLGeneralization.PolicyOptimization.PolicyGradient
-- Conservative policy iteration mixture/resolvent results
import RLGeneralization.PolicyOptimization.CPI
-- Gradient-domination infrastructure for policy optimization
import RLGeneralization.PolicyOptimization.Optimality
-- Natural policy gradient: Fisher PSD, mirror-descent convergence analysis
import RLGeneralization.PolicyOptimization.NPG
-- Trust region and proximal policy optimization: surrogate bound, PPO clipping
import RLGeneralization.PolicyOptimization.TRPO
-- Actor-critic methods: advantage decomposition, critic bias, variance reduction
import RLGeneralization.PolicyOptimization.ActorCritic

-- Fitted Q-iteration / offline RL contraction core
import RLGeneralization.OfflineRL.FQI
-- Offline RL: pessimism principle, concentrability, LCB Q-function
import RLGeneralization.OfflineRL.Pessimism

-- Imitation learning: behavior-cloning bound from PDL
import RLGeneralization.ImitationLearning.Basic
-- Imitation learning: MaxEnt IRL (Ziebart 2008), soft-optimal policy, feature matching
import RLGeneralization.ImitationLearning.MaxEntIRL

-- Linear MDPs: optimal Q linearity
import RLGeneralization.LinearMDP.Basic
-- Elliptical-potential lemma (analytic core) for linear MDPs
import RLGeneralization.LinearMDP.EllipticalPotential
-- UCBVI-Lin regret bound for linear MDPs
import RLGeneralization.LinearMDP.Regret
-- UCBVI-Lin self-contained regret: elliptical potential + bonus composition
import RLGeneralization.LinearMDP.RegretFull
-- Bridge: elliptical potential → LinUCB regret composition
import RLGeneralization.LinearMDP.EllipticalBridge
-- LQR infrastructure: quadratic costs and Riccati equations
import RLGeneralization.LQR.Basic
-- LQR: finite-horizon Riccati recursion, closed-loop Bellman, policy gradient
import RLGeneralization.LQR.RiccatiPolicy

-- Complexity: VC dimension, Sauer-Shelah growth function bounds
import RLGeneralization.Complexity.VCDimension
-- Complexity: Rademacher complexity, Massart's lemma, VC-Rademacher connection
import RLGeneralization.Complexity.Rademacher
-- Complexity: Symmetrization lemma, ghost sample argument, McDiarmid application
import RLGeneralization.Complexity.Symmetrization
-- Complexity: Covering/packing duality, volumetric bounds, metric entropy
import RLGeneralization.Complexity.CoveringPacking
-- Complexity: Generic chaining / gamma_2 functional
import RLGeneralization.Complexity.GenericChaining
-- Complexity: Eluder dimension for function-approximation RL (Russo-Van Roy 2013)
import RLGeneralization.Complexity.EluderDimension

-- Lower bounds: Fano's inequality, Assouad's method, tabular RL lower bound
import RLGeneralization.LowerBounds.FanoLeCam
-- Lower bounds: Minimax matching between UCBVI upper and Fano lower bounds
import RLGeneralization.LowerBounds.MinimaxMatching

-- Algorithms: Q-learning convergence (contraction, error recursion, sample complexity)
import RLGeneralization.Algorithms.QLearning
-- Algorithms: Linear TD(0) convergence (ODE method, projected Bellman, approximation error)
import RLGeneralization.Algorithms.LinearTD
-- Algorithms: Generative model → value iteration → sample complexity composition
import RLGeneralization.Algorithms.GenerativeQLearning
-- Algorithms: Model-based RL, Dyna K-step contraction, model-free comparison
import RLGeneralization.Algorithms.ModelBased
-- Algorithms: MCTS / UCT value estimates, exploration bonus, horizon bound, pigeonhole
import RLGeneralization.Algorithms.MCTS
-- Algorithms: SARSA on-policy TD, comparison with Q-learning
import RLGeneralization.Algorithms.SARSA

-- Privacy: differential privacy for RL (Laplace, Gaussian, composition, sample complexity)
import RLGeneralization.Privacy.DPRewards

-- SGD convergence: convex and strongly-convex rate structures
import RLGeneralization.Optimization.SGD
-- RKHS: reproducing kernels, Gram matrices, kernel ridge regression
import RLGeneralization.Approximation.RKHS
-- Neural network approximation: two-layer networks, UAT statement
import RLGeneralization.Approximation.NeuralNetwork
-- Hamilton-Jacobi-Bellman: continuous-time optimal control stub
import RLGeneralization.MDP.HJB
-- POMDPs: partially observable MDPs, belief states, belief update
import RLGeneralization.MDP.POMDP
-- Multi-agent RL: Markov games, Nash equilibrium, minimax theorem
import RLGeneralization.MDP.MultiAgent
-- Options framework: temporally extended actions, option value bounds
import RLGeneralization.MDP.Options
-- Constrained MDPs: Lagrangian, weak duality, budget monotonicity
import RLGeneralization.MDP.ConstrainedMDP
-- Reward shaping: potential-based shaping, policy invariance (Ng et al. 1999)
import RLGeneralization.MDP.RewardShaping
-- Stochastic calculus stub: Ito processes, Ito isometry statement
import RLGeneralization.Concentration.StochasticCalculus
-- Central Limit Theorem stub: CLT statement, Berry-Esseen rate
import RLGeneralization.Concentration.CLT
-- Robbins-Siegmund convergence: a.s. convergence for stochastic approximation
import RLGeneralization.Concentration.RobbinsSiegmund
-- MDP trajectory filtration: conditional expectations, martingale differences, Azuma-Hoeffding
import RLGeneralization.Concentration.MDPFiltration
-- Trajectory measure: PMF construction, expectation, Azuma-Hoeffding tail, UCBVI confidence
import RLGeneralization.Concentration.TrajectoryMeasure

-- Executable: certified value iteration interface
import RLGeneralization.Executable.CertifiedVI
-- Executable: LP duality certificate verification
import RLGeneralization.Executable.LPCertificate
-- Executable: tabular planner with complexity bounds
import RLGeneralization.Executable.TabularPlanner

-- Tests
import RLGeneralization.Test.SimpleMDP

-- DRAFT OR EXCLUDED MODULES:
--
-- RLGeneralization.Draft
--   Aggregates conditional frontier chapters and proof-scaffolding modules.
--   These compile, but they are not part of the trusted benchmark root.
--
-- RLGeneralization.Generalization.PolicyEvaluation
--   LSTD conditional module: definitions + value error bound + sample complexity.
--   Rate hypothesis taken from learning theory side.
--   (Promoted to trusted root with conditional status.)
--
-- RLGeneralization.Concentration.MarkovChain
--   excluded frontier module. Current contents only include setup lemmas
--   and a thin positivity check, not a genuine Markov-chain concentration theorem.
--
-- RLGeneralization.Test.ConcreteExample
--   concrete example module outside the trusted benchmark root.
