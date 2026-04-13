#!/usr/bin/env python3
"""Run the ground_truth prover on the known-failure regression set.

This targets the theorems that failed in the last full replay, allowing
fast iteration on replay-harness fixes before running the full sweep.
Fails if fewer than half the listed theorems are present in the benchmark.

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

# Theorems that failed in a prior ground_truth replay and still exist in
# the current benchmark.  Twelve entries were removed because their
# underlying theorems were renamed or dropped from mlstatbench.json.
REGRESSION_THEOREMS = [
    "generative_model_pac",
    "pseudoRegret_eq_sum_gap",
    "stageCost_nonneg",
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

    # Fail if too many regression theorems are missing — the benchmark file
    # has drifted and the regression set needs updating.
    min_required = len(REGRESSION_THEOREMS) // 2
    if len(problems) < min_required:
        print(f"error: only {len(problems)}/{len(REGRESSION_THEOREMS)} regression "
              f"theorems found (minimum {min_required}); update REGRESSION_THEOREMS "
              f"or benchmark/mlstatbench.json", file=sys.stderr)
        sys.exit(1)

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
