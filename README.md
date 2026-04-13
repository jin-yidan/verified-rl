# Verified RL: Formally Verified Reinforcement Learning Theory in Lean 4

A machine-checked formalization of reinforcement learning theory, built on
[Mathlib](https://github.com/leanprover-community/mathlib4). The library
contains **117 trusted modules** and **46,000+ lines** of Lean 4
code with **zero `sorry`** anywhere in the codebase.

## What's Proved

Two complete end-to-end proof chains connect definitions to final theorems
with no gaps, no assumptions, and no sorry:

### 1. Generative Model PAC Bound (Sample Complexity)

The full pipeline from concentration inequalities to a PAC sample complexity
guarantee for the plug-in empirical greedy policy:

```
Bernstein MGF bound (proved from scratch, not in Mathlib)
  -> Bernstein tail bound for sums of independent r.v.s
    -> Union bound over all (s, a, s') transition entries
      -> Deterministic value gap given epsilon-close model
        -> Sample complexity inversion (Hoeffding + Bernstein rates)
          -> PAC theorem: for N >= N_0, empirical greedy is epsilon-optimal
             with probability >= 1 - delta
```

**Key theorem** (`Concentration/GenerativeModel.lean`):
`pac_rl_generative_model_bernstein_optimal` -- For any finite discounted MDP,
there exists an optimal value function V* and a sample count
N_0 = O(log(1/delta)) such that the empirical greedy policy is epsilon-optimal
with high probability.

### 2. Value Iteration Convergence

Complete Bellman contraction theory through to epsilon-optimal policy
construction:

```
Weighted sum contraction lemma
  -> Bellman evaluation operator is a gamma-contraction
  -> Bellman optimality operator is a gamma-contraction
    -> Banach fixed point theorem (via Mathlib) gives unique Q*
      -> Geometric convergence: ||Q^k - Q*|| <= gamma^k * ||Q^0 - Q*||
        -> Iteration threshold: K >= log(C/eps)/(1-gamma) suffices
          -> Q-error amplification: ||Q - Q*|| <= eps => V* - V^pi <= 2eps/(1-gamma)
            -> Greedy policy is epsilon-optimal
```

**Key theorem** (`MDP/ValueIteration.lean`):
`value_iteration_epsilon_optimal_constructed` -- Constructs the greedy policy
via Banach fixed point and proves it is epsilon-optimal after finitely many
iterations.

### Bernstein Concentration (New Formalization)

The Bernstein MGF bound `E[exp(lambda X)] <= exp(lambda^2 sigma^2 / (2(1 - lambda b/3)))`
is proved from first principles in ~110 lines (`Concentration/Bernstein.lean`).
This result is **not available in Mathlib** and is a standalone contribution.

## Module Overview

| Area | Modules | Contents |
|------|---------|----------|
| **MDP Theory** | 21 | Bellman equations, contraction, value/policy iteration, simulation lemma, finite-horizon, LP formulation, average reward, POMDP, constrained MDP, options, reward shaping, HJB |
| **Concentration** | 28 | Hoeffding, Bernstein, Bennett, Azuma-Hoeffding, McDiarmid, Talagrand, sub-Gaussian, matrix Bernstein, self-normalized, Johnson-Lindenstrauss, large deviations, generative model PAC |
| **Bandits** | 8 | UCB (gap-dependent + worst-case), LinUCB, EXP3, Thompson sampling, lower bounds, probabilistic regret |
| **Generalization** | 10 | Sample complexity, uniform convergence, PAC-Bayes, Dudley integral, transfer RL, SLT bridge |
| **Complexity** | 6 | VC dimension, Rademacher complexity, symmetrization, covering/packing, generic chaining, eluder dimension |
| **Exploration** | 6 | UCBVI, variance-aware UCBVI, batch UCBVI, reward-free exploration |
| **Policy Optimization** | 6 | Policy gradient, NPG, CPI, TRPO, actor-critic, gradient domination |
| **Algorithms** | 6 | Q-learning, SARSA, linear TD, MCTS, model-based RL, generative Q-learning |
| **Linear MDP** | 7 | Optimal Q linearity, elliptical potential lemma, regret bounds, LinUCB bridge, LSVI |
| **Other** | 19 | Offline RL, bilinear rank, imitation learning, LQR, lower bounds, privacy, optimization, approximation, executable planners |

## Proof Architecture

The library uses two proof tiers:

- **Unconditional** (90 modules): Fully proved from definitions to final
  theorem, building only on Mathlib. No assumptions beyond the problem setup.

- **Conditional** (27 modules): The algebraic/compositional content is fully
  proved, but measure-theoretic steps (taking expectations, proving
  measurability, applying concentration to specific probability spaces) are
  taken as hypotheses. These hypotheses mark where Mathlib's current API
  ends — the math on both sides is done, the wiring through Lean's measure
  theory API is deferred pending upstream Mathlib additions. See
  [`MODULES.md`](MODULES.md) for per-module blockers.

Every module compiles with `--wfail` (warnings as failures) and passes
`lean4checker`. See [`MODULES.md`](MODULES.md) for the full per-module index
and [`PROJECT_STANDARD.md`](PROJECT_STANDARD.md) for the formalization criteria.

## Setup

```bash
lake update SLT
bash scripts/prepare_slt.sh
lake build RLGeneralization
```

Depends on [lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory)
at a pinned commit, with a compatibility patch for Lean 4 v4.28.0 applied by
`scripts/prepare_slt.sh`.

## Build Targets

```bash
lake build RLGeneralization     # Trusted root: 117 modules
```

## CI

GitHub Actions runs on every push:
- `lake build --wfail RLGeneralization` (full build, warnings as errors)
- `lean4checker` (independent verification of compiled .olean files)
- Manifest and status consistency checks
- Benchmark smoke test

## References

- Agarwal, Brantley, Jiang, Kakade, Sun. *Reinforcement Learning: Theory and Algorithms*. 2026.
- Zhang. *Towards Formalizing Reinforcement Learning Theory*. arXiv:2511.03618, 2025.
- Zhang, Lee, Liu. *Statistical Learning Theory in Lean 4*. arXiv:2602.02285, 2026.
- Boucheron, Lugosi, Massart. *Concentration Inequalities: A Nonasymptotic Theory of Independence*. Oxford, 2013.
