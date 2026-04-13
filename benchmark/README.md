# MLStatBench: Machine Learning & Statistics Theorem Benchmark

A benchmark for evaluating automated theorem provers on ML/statistics theory,
with machine-verified ground-truth proofs in Lean 4.

## Overview

MLStatBench contains 200 theorem-proving problems extracted from two formally
verified libraries. The curated set is explicitly domain-balanced, and the
README tables below are checked against `benchmark/mlstatbench.json`.

- **lean4-rl** (this project): RL generalization theory (Bellman equations,
  concentration inequalities, PAC bounds, policy optimization)
- **lean-stat-learning-theory**: Statistical learning theory (covering numbers,
  regression, empirical processes)

All ground-truth proofs are kernel-checked by Lean 4 with zero `sorry`.

## Problem Format

Each problem in `mlstatbench.json` has:

```json
{
  "id": "mlstatbench_0042",
  "source": "rl",
  "source_file": "RLGeneralization/Concentration/Bernstein.lean",
  "source_line": 89,
  "theorem_name": "bernstein_mgf_bound",
  "kind": "theorem",
  "statement": "theorem bernstein_mgf_bound ...",
  "domain": "concentration",
  "difficulty": "hard",
  "status": "exact",
  "problem_type": "full_theorem_proving"
}
```

## Domains

| Domain | Count | Description |
|--------|-------|-------------|
| bellman | 35 | Bellman equations, contraction, fixed points |
| concentration | 25 | Hoeffding, Bernstein, PAC bounds |
| exploration | 20 | UCB, UCBVI, optimistic bonus arguments |
| other | 15 | LQR, differential privacy, miscellaneous |
| policy_optimization | 15 | Policy gradient, CPI, advantage |
| regression | 70 | LSVI, FQI, linear MDP, SLT covering numbers |
| sample_complexity | 15 | Generalization bounds, minimax rates |
| simulation | 5 | Simulation lemma and resolvent identities |

## Difficulty Levels

| Level | Count | Description |
|-------|-------|-------------|
| bridge | 28 | Cross-domain problems combining multiple areas |
| easy | 10 | Short proofs (≤5 lines), single-domain |
| hard | 65 | Long proofs or weak-status theorems |
| medium | 97 | Moderate proofs, standard techniques |

## Running Evaluations

```bash
# Extract problems from source
python benchmark/extract_theorems.py > benchmark/problems_raw.json

# Curate the benchmark
python benchmark/curate_benchmark.py

# Evaluate a prover
python benchmark/evaluate.py --prover dummy          # dry run
python benchmark/evaluate.py --prover ground_truth   # benchmark self-check
python benchmark/evaluate.py --prover deepseek       # DeepSeek-Prover-V2

# Analyze failures
python benchmark/analyze_failures.py benchmark/results/<prover>_results.local.json
```

## Requirements

- Python 3.10+
- Lean 4 v4.28.0 (for ground-truth verification)
- `httpx` (for DeepSeek-Prover-V2 API calls)
- Prover-specific: `DEEPSEEK_API_KEY` for DeepSeek-Prover-V2

## Key Differentiators vs Existing Benchmarks

| Feature | miniF2F | ProofNet | MLStatBench |
|---------|---------|----------|-------------|
| Domain | Competition math | Undergrad math | ML/stats theory |
| Language | Lean 4 / Isabelle | Lean 4 | Lean 4 |
| Ground truth | Human proofs | Varied | Machine-verified (0 sorry) |
| Bridge problems | No | No | Yes (28 cross-domain) |
| ML-specific | No | No | Yes |

## Citation

If you use MLStatBench, please cite:

```bibtex
@inproceedings{mlstatbench2026,
  title={MLStatBench: A Benchmark for Automated Theorem Proving in Machine Learning Theory},
  year={2026},
}
```
