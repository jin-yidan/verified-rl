-- RLGeneralization: Formally Verified RL Theory in Lean 4
--
-- Formalizes core results from Agarwal, Brantley, Jiang, Kakade, Sun,
-- "Reinforcement Learning: Theory and Algorithms" (2026).
--
-- VERIFICATION STATUS:
--   This file is the trusted benchmark target.
--   `lake build --wfail` is expected to pass on exactly these imports.
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
-- Empirical model, comparison lemmas, and component-wise bounds
import RLGeneralization.Generalization.SampleComplexity
-- Component-wise value bounds
import RLGeneralization.Generalization.ComponentWise
-- LSVI approximate dynamic-programming core
import RLGeneralization.LinearFeatures.LSVI
-- Concentration: Hoeffding bridge + union bound + PAC composition
import RLGeneralization.Concentration.Hoeffding
-- Concentration: Bernstein MGF bound + tail bound (Appendix A)
import RLGeneralization.Concentration.Bernstein
-- Concentration: trusted generative-model probability space and PAC bound
import RLGeneralization.Concentration.GenerativeModelCore
-- Concentration: Bernstein PAC analysis, canonical fixed-point construction
import RLGeneralization.Concentration.GenerativeModel
-- Generalization: minimax deterministic core, variance/deviation bounds
import RLGeneralization.Generalization.MinimaxSampleComplexity
-- Bandits: ETC oracle witness, UCB algebraic core, gap-dependent regret
import RLGeneralization.Bandits.UCB
-- Bandits: probability space, Hoeffding concentration for arm means
import RLGeneralization.Bandits.BanditConcentration
-- LSVI-SLT regression bridge: connects LSVI to statistical learning theory
import RLGeneralization.LinearFeatures.RegressionBridge
-- Bellman-rank auxiliary structure and exact bilinear bounds
import RLGeneralization.BilinearRank.Auxiliary

-- UCBVI definitions and regret-decomposition core
import RLGeneralization.Exploration.UCBVI
-- Batch UCBVI: harmonic-sqrt bound, Cauchy-Schwarz bonus bound
import RLGeneralization.Exploration.BatchUCBVI
-- Policy-gradient definitions and algebraic identities
import RLGeneralization.PolicyOptimization.PolicyGradient
-- Conservative policy iteration mixture/resolvent results
import RLGeneralization.PolicyOptimization.CPI
-- Gradient-domination infrastructure for policy optimization
import RLGeneralization.PolicyOptimization.Optimality

-- Fitted Q-iteration / offline RL contraction core
import RLGeneralization.OfflineRL.FQI

-- Imitation learning: behavior-cloning bound from PDL
import RLGeneralization.ImitationLearning.Basic

-- Linear MDPs: optimal Q linearity
import RLGeneralization.LinearMDP.Basic
-- Elliptical-potential lemma (analytic core) for linear MDPs
import RLGeneralization.LinearMDP.EllipticalPotential
-- UCBVI-Lin regret bound for linear MDPs
import RLGeneralization.LinearMDP.Regret
-- LQR infrastructure: quadratic costs and Riccati equations
import RLGeneralization.LQR.Basic

-- Tests
import RLGeneralization.Test.SimpleMDP

-- DRAFT OR EXCLUDED MODULES:
--
-- RLGeneralization.Draft
--   Aggregates conditional frontier chapters and proof-scaffolding modules.
--   These compile, but they are not part of the trusted benchmark root.
--
-- RLGeneralization.Generalization.PolicyEvaluation
--   LSTD definitions only. Finite-sample bound requires measure-theoretic
--   plumbing to connect to SLT's linear_minimax_rate (version-compatible).
--
-- RLGeneralization.Concentration.MarkovChain
--   excluded frontier module. Current contents only include setup lemmas
--   and a thin positivity check, not a genuine Markov-chain concentration theorem.
--
-- RLGeneralization.Test.ConcreteExample
--   concrete example module outside the trusted benchmark root.
