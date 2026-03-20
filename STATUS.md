# Status Summary

This file is machine-derived from `verification_manifest.json`.

## Trusted Root

- Modules: 36
- Exact: 26
- Weaker: 7
- Conditional: 3
- Build command: `lake build --wfail`

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
- `RLGeneralization.Concentration.Hoeffding` — Hoeffding/union-bound bridge used by the verified target.
- `RLGeneralization.Concentration.Bernstein` — Bernstein MGF and tail bounds.
- `RLGeneralization.Concentration.GenerativeModelCore` — Trusted generative-model product measure, coordinate independence, and PAC concentration.
- `RLGeneralization.Concentration.GenerativeModel` — Bernstein PAC analysis with log-rate sample complexity (pac_rl_generative_model_bernstein), canonical fixed-point construction, end-to-end minimax value-gap theorem, and Bernstein composition (minimax_pac_bernstein_composed). Uses uniform variance bound p(1-p) ≤ 1/4 for clean sample-complexity formula; exact per-entry variance is preserved in the intermediate theorem generative_model_pac_bernstein.
- `RLGeneralization.Bandits.BanditConcentration` — Bernoulli reward probability space, Hoeffding concentration for arm means, union bound over all arms. Zero sorry.
- `RLGeneralization.BilinearRank.Auxiliary` — Trusted Bellman-rank definitions and exact bilinear Bellman-error bounds.
- `RLGeneralization.Exploration.BatchUCBVI` — Harmonic-sqrt bound, Cauchy-Schwarz for visit counts, pigeonhole bonus bound. Zero sorry.
- `RLGeneralization.PolicyOptimization.CPI` — Resolvent-based conservative policy-iteration improvement theorems.
- `RLGeneralization.PolicyOptimization.Optimality` — Gradient-domination structure and nonnegativity theorem.
- `RLGeneralization.OfflineRL.FQI` — Fitted Q-iteration contraction and error-propagation theorem.
- `RLGeneralization.LinearMDP.Basic` — Linear-MDP definition and the optQ_linear proof.
- `RLGeneralization.LinearMDP.EllipticalPotential` — Elliptical-potential analytic core. Matrix-algebra hypotheses fully discharged via spectral theory + AM-GM. elliptical_potential_unconditional provides the fully self-contained version.
- `RLGeneralization.LQR.Basic` — LQR definitions, Riccati infrastructure, and stageCost_nonneg theorem.
- `RLGeneralization.Test.SimpleMDP` — Sanity checks/examples for the trusted target.

### Weaker Modules

- `RLGeneralization.Generalization.SampleComplexity` — Deterministic comparison/sample-complexity core.
- `RLGeneralization.Generalization.ComponentWise` — Component-wise resolvent-style bounds.
- `RLGeneralization.LinearFeatures.LSVI` — Approximate dynamic-programming error-propagation core for linear-feature value iteration.
- `RLGeneralization.Generalization.MinimaxSampleComplexity` — Minimax deterministic core, variance/deviation bounds, rate scaling.
- `RLGeneralization.Bandits.UCB` — Bandit definitions, oracle ETC regret, UCB algebraic core, confidence threshold, index domination lemmas, gap-dependent regret bound, and composed presentation form with pull-count counting argument.
- `RLGeneralization.Exploration.UCBVI` — Algebraic core of the UCBVI regret argument.
- `RLGeneralization.PolicyOptimization.PolicyGradient` — Definitions and algebraic identities; the full policy-gradient theorem is not proved.

### Conditional Modules

- `RLGeneralization.LinearFeatures.RegressionBridge` — LSVI-SLT bridge: type adapters, per-stage regression model, and deterministic sample-complexity chain. Key theorems take the regression rate as a hypothesis; lsvi_stage_slt_bound re-exports SLT's linear_minimax_rate.
- `RLGeneralization.ImitationLearning.Basic` — Behavior-cloning algebraic wrapper and DAgger setup definitions. The PDL-based state-distribution argument is taken as hypothesis.
- `RLGeneralization.LinearMDP.Regret` — UCBVI-Lin regret wrappers built on external optimism/bonus hypotheses.

## Draft Root

- Modules: 2
- Build command: `lake build RLGeneralization.Draft`

- `RLGeneralization.BilinearRank.Basic` — Draft Bellman-rank degenerate helper and GOLF wrappers.
- `RLGeneralization.PolicyOptimization.NPG` — Natural policy-gradient update structure and step-size nonnegativity.

## Excluded Modules

- Modules: 5

- `RLGeneralization.API` — Public re-export surface. This is an import convenience module, not a theorem-bearing verification target.
- `RLGeneralization.Basic` — Placeholder utility module; not part of the formal theorem surface.
- `RLGeneralization.Concentration.MarkovChain` — Excluded frontier file. Current theorem surface is too thin for trusted use and does not yet formalize a genuine concentration result.
- `RLGeneralization.Generalization.PolicyEvaluation` — Excluded stub file for LSTD policy evaluation. Definitions compile, but the finite-sample theorem is not formalized.
- `RLGeneralization.Test.ConcreteExample` — Concrete worked example and sanity-check module outside the trusted benchmark root.
