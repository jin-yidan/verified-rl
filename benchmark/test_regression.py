#!/usr/bin/env python3
"""Run the ground_truth prover on the known-failure regression set.

This targets the 15 theorems that failed in the last full replay, allowing
fast iteration on replay-harness fixes before running the full 200-problem
sweep.

Usage:
    python benchmark/test_regression.py
"""

import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "benchmark"))

from evaluate import LeanCheckProver, make_lean_problem, RESULTS_DIR  # noqa: E402

# The 15 theorems that failed in the last full ground_truth replay.
REGRESSION_THEOREMS = [
    "generative_model_pac",
    "generative_model_pac_bernstein",
    "optArm_gap",
    "exists_optimal_arm",
    "gap_nonneg",
    "pseudoRegret_nonneg",
    "gap_eq_zero_iff_opt",
    "pseudoRegret_eq_sum_gap",
    "oracle_worst_case_bound_via_etc",
    "minimax_rate_scaling_V_abs",
    "minimax_rate_scaling_V",
    "optimalQFixedPoint_isBellmanOptimalQ",
    "gamma_pow_le_exp_neg",
    "stageCost_nonneg",
    "R_max_pos",
]


def main() -> None:
    bench_path = ROOT / "benchmark" / "mlstatbench.json"
    try:
        benchmark = json.loads(bench_path.read_text())
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"error: failed to load {bench_path}: {e}", file=sys.stderr)
        sys.exit(1)

    regression_set = set(REGRESSION_THEOREMS)
    problems = [
        p for p in benchmark["problems"]
        if p["theorem_name"] in regression_set
    ]

    if not problems:
        print("No regression problems found in benchmark.", file=sys.stderr)
        sys.exit(1)

    found = {p["theorem_name"] for p in problems}
    missing = regression_set - found
    if missing:
        print(f"warning: {len(missing)} regression theorems not in benchmark: "
              f"{sorted(missing)}", file=sys.stderr)

    prover = LeanCheckProver()
    passed = 0
    failed = 0
    results = []

    print(f"Running regression set: {len(problems)} problems\n",
          file=sys.stderr)

    for p in problems:
        lean_code = make_lean_problem(p)
        start = time.time()
        result = prover.attempt(p, lean_code)
        elapsed = time.time() - start

        result["problem_id"] = p["id"]
        result["theorem_name"] = p["theorem_name"]
        results.append(result)

        status = "PASS" if result["success"] else "FAIL"
        if result["success"]:
            passed += 1
        else:
            failed += 1

        tactic_info = result.get("tactic") or "-"
        print(f"  [{status}] {p['theorem_name']:<45} "
              f"{elapsed:5.1f}s  tactic: {tactic_info}", file=sys.stderr)
        if not result["success"] and result.get("error"):
            # Show first few lines of error for quick debugging.
            err_lines = result["error"].splitlines()[:5]
            for line in err_lines:
                print(f"         {line}", file=sys.stderr)

    print(f"\n{'='*60}", file=sys.stderr)
    print(f"Regression: {passed}/{len(problems)} passed, "
          f"{failed} failed", file=sys.stderr)

    out = RESULTS_DIR / "regression_results.local.json"
    out.write_text(json.dumps({"results": results}, indent=2))
    print(f"Details written to {out}", file=sys.stderr)

    sys.exit(0 if failed == 0 else 1)


if __name__ == "__main__":
    main()
