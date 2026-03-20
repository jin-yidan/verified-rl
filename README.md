# Formally Verified Reinforcement Learning Theory

A Lean 4 formalization of core reinforcement learning theory: Bellman equations, value/policy iteration convergence, sample complexity with PAC guarantees, bandit regret analysis, concentration inequalities, and linear MDP structure. All theorems are kernel-checked with zero `sorry`.

## Setup

This repository depends on the `SLT` library as a pinned Lake git dependency.
The pinned upstream commit needs a small compatibility patch for Lean 4
`v4.28.0`, and this repository tracks that patch explicitly.

Minimal setup:

```bash
lake update SLT
bash scripts/prepare_slt.sh
lake build RLGeneralization
```

The pinned dependency is
`https://github.com/YuanheZ/lean-stat-learning-theory` at commit
`4aaea15591360ccfffa1befdf0e7162f5af17f60`, with the local compatibility patch
recorded in [`patches/slt-v4.28.patch`](patches/slt-v4.28.patch) and applied by
[`scripts/prepare_slt.sh`](scripts/prepare_slt.sh). The preparation script
verifies the dependency is exactly at the pinned commit before applying the
patch.

## Targets

The repository now distinguishes between two build targets:

```bash
lake build --wfail RLGeneralization
```

Builds the trusted benchmark root [`RLGeneralization.lean`](RLGeneralization.lean).
This target is intended to stay warning-free and to contain only modules that
we are comfortable using as benchmark data for proof-auditing agents.

```bash
lake build RLGeneralization.Draft
```

Builds [`RLGeneralization/Draft.lean`](RLGeneralization/Draft.lean),
which aggregates frontier modules that are useful research scaffolding but are
currently conditional, hypothesis-forwarding, or otherwise excluded from the
trusted benchmark root.

## Current State

The trusted root currently covers:

- core discounted and finite-horizon MDP theory,
- Banach fixed-point policy-evaluation existence/convergence bridge,
- deterministic model-comparison infrastructure,
- LSVI error-propagation core,
- concentration inequalities (Hoeffding/Bernstein),
- FQI contraction core,
- UCBVI algebraic core,
- optimal-Q linearity for linear MDPs,
- policy-gradient definitions and algebraic identities.

The machine-derived status summary is in [`STATUS.md`](STATUS.md). Current
module counts from `verification_manifest.json`:

- trusted root: 36 modules,
- exact: 26 modules,
- weaker: 7 modules,
- conditional: 3 modules,
- draft root: 2 modules,
- excluded modules: 5 modules.

The draft target (`RLGeneralization.Draft`) currently contains frontier work
for Bellman rank / GOLF and natural policy-gradient definitions.

## Status Data

Four files track theorem honesty explicitly, plus one project-standard file:

- [`STATUS.md`](STATUS.md)
  Machine-derived module summary generated from `verification_manifest.json`.
- [`FORMALIZATION_MAP.md`](FORMALIZATION_MAP.md)
  Human-readable summary of what is trusted, weaker, conditional, or blocked.
- [`THEOREM_CATALOG.md`](THEOREM_CATALOG.md)
  Theorem-by-theorem human-language catalog for the trusted benchmark root.
- [`verification_manifest.json`](verification_manifest.json)
  Machine-readable status labels for trusted, draft, excluded, and selected theorem surfaces.
- [`PROJECT_STANDARD.md`](PROJECT_STANDARD.md)
  Project goal and the repository's standard for what counts as genuine formalization.

The status vocabulary is:

- `exact`
- `weaker`
- `conditional`
- `wrapper`
- `stub`
- `vacuous`

## Repository Check

CI runs [`scripts/check_verified_target.sh`](scripts/check_verified_target.sh)
,[`scripts/check_manifest_consistency.sh`](scripts/check_manifest_consistency.sh),
[`scripts/generate_status.py --check`](scripts/generate_status.py), and
[`scripts/check_benchmark_metadata.py`](scripts/check_benchmark_metadata.py)
and a `ground_truth` benchmark smoke replay in addition to the normal Lean
build. The checks currently enforce:

- the pinned `SLT` dependency resolves through Lake and the tracked compatibility patch applies cleanly,
- the trusted root builds with `--wfail` and without interactive `Try this:` diagnostics,
- the draft root builds,
- trusted-root modules in `verification_manifest.json` are not labeled `wrapper`,
- imported verified files do not contain literal `True` theorem conclusions,
- imported verified files do not self-identify as excluded,
- imported verified files do not contain a few high-signal draft/stub markers,
- trusted-root imports match `verification_manifest.json`,
- draft-root imports match `verification_manifest.json`,
- `STATUS.md` matches `verification_manifest.json`,
- `benchmark/README.md` matches `benchmark/mlstatbench.json`,
- a 3-problem `ground_truth` benchmark smoke replay succeeds end-to-end,
- theorem entries in `verification_manifest.json` refer only to modules that are
  explicitly listed in the trusted, draft, or excluded manifests,
- every Lean module under `RLGeneralization/` is classified as trusted, draft,
  or excluded.

## Conventions

The development uses standard unnormalized discounted Bellman equations with
bounded real rewards. Some source texts normalize return by `(1 - γ)` and take
rewards in `[0, 1]`, so some formal statements use equivalent constant-scaled
forms.

## References

- Agarwal, Brantley, Jiang, Kakade, Sun. *Reinforcement Learning: Theory and Algorithms*. 2026.
- Zhang. *Towards Formalizing Reinforcement Learning Theory*. arXiv:2511.03618, 2025.
- Zhang, Lee, Liu. *Statistical Learning Theory in Lean 4*. arXiv:2602.02285, 2026.
