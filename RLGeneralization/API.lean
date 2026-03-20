/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# RLGeneralization Library API

This file re-exports all trusted-root modules from the lean4-rl
formalization. It mirrors `RLGeneralization.lean` exactly (minus the
test module). Import this file to access all trusted-root results.

Some imported modules are exact, while others are explicitly weaker or
conditional. See `verification_manifest.json` for theorem-surface status.

## Key Results

### Sample Complexity (PAC Bounds)
* `FiniteMDP.pac_rl_generative_model_bernstein` — PAC bound with O(log(1/δ)) rate
* `FiniteMDP.pac_rl_generative_model` — PAC bound (existential, polynomial rate)
* `FiniteMDP.pac_rl_generative_model_optimal` — PAC bound constructing V* internally

### Dynamic Programming
* `FiniteMDP.value_iteration_epsilon_optimal_constructed` — ε-optimal value iteration
* `FiniteMDP.policy_iteration_convergence` — policy iteration converges geometrically
* `FiniteMDP.cpi_improvement_bound` — CPI mixture improvement bound

### Policy Comparison
* `FiniteMDP.pdl_normalized` — Kakade-Langford PDL (normalized form)
* `FiniteMDP.pdl_occupancy_form` — PDL with unnormalized occupancy
* `FiniteMDP.simulation_lemma` — Kearns-Singh simulation inequality

### Concentration Inequalities
* `FiniteMDP.generative_model_pac_bernstein` — Bernstein PAC event
* `FiniteMDP.generative_model_pac` — Hoeffding PAC event
* `bernstein_sum` — Bernstein tail inequality

### Occupancy Measure
* `FiniteMDP.stateOccupancy` — normalized d^π(s₀,s) = (1-γ)·∑γ^t P^t
* `FiniteMDP.discountedVisitation` — unnormalized ∑γ^t P^t
* `FiniteMDP.stateOccupancy_sum_one` — normalized occupancy sums to 1

### Core Definitions
* `FiniteMDP` — finite discounted MDP structure
* `FiniteMDP.StochasticPolicy` — stochastic policy
* `FiniteMDP.isValueOf` — Bellman equation for value functions
* `FiniteMDP.isBellmanOptimalQ` — Bellman optimality equation

## Syllabus Context

The repository scope follows the Agarwal et al. syllabus, but theorem naming
and claim wording in this codebase are repository-native.
-/

-- Core MDP theory
import RLGeneralization.MDP.Basic
import RLGeneralization.MDP.BellmanContraction
import RLGeneralization.MDP.SimulationLemma
import RLGeneralization.MDP.ValueIteration
import RLGeneralization.MDP.PolicyIteration
import RLGeneralization.MDP.Resolvent
import RLGeneralization.MDP.BanachFixedPoint
import RLGeneralization.MDP.PerformanceDifference
import RLGeneralization.MDP.OccupancyMeasure
import RLGeneralization.MDP.MatrixResolvent
import RLGeneralization.MDP.SimulationResolvent
import RLGeneralization.MDP.FiniteHorizon

-- Concentration and PAC bounds
import RLGeneralization.Concentration.Hoeffding
import RLGeneralization.Concentration.Bernstein
import RLGeneralization.Concentration.GenerativeModelCore
import RLGeneralization.Concentration.GenerativeModel

-- Generalization bounds
import RLGeneralization.Generalization.SampleComplexity
import RLGeneralization.Generalization.ComponentWise
import RLGeneralization.Generalization.MinimaxSampleComplexity

-- Bandits
import RLGeneralization.Bandits.UCB
import RLGeneralization.Bandits.BanditConcentration

-- LSVI and regression bridge
import RLGeneralization.LinearFeatures.LSVI
import RLGeneralization.LinearFeatures.RegressionBridge

-- Bellman rank
import RLGeneralization.BilinearRank.Auxiliary

-- Exploration
import RLGeneralization.Exploration.UCBVI
import RLGeneralization.Exploration.BatchUCBVI

-- Policy optimization
import RLGeneralization.PolicyOptimization.PolicyGradient
import RLGeneralization.PolicyOptimization.CPI
import RLGeneralization.PolicyOptimization.Optimality

-- Offline RL
import RLGeneralization.OfflineRL.FQI

-- Imitation learning
import RLGeneralization.ImitationLearning.Basic

-- Linear MDPs
import RLGeneralization.LinearMDP.Basic
import RLGeneralization.LinearMDP.EllipticalPotential
import RLGeneralization.LinearMDP.Regret

-- LQR
import RLGeneralization.LQR.Basic
