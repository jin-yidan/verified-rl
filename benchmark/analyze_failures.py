#!/usr/bin/env python3
"""Analyze prover failures from MLStatBench evaluation results.

Categorizes failures into the taxonomy from the paper:
1. Measure-theoretic reasoning — probability spaces, measurability, integrals
2. Multi-domain bridging — combining probability + analysis + algebra
3. Long-horizon search — proofs requiring >10 tactic steps
4. Missing lemma identification — prover doesn't find required Mathlib lemma
5. Numerical reasoning — exp, log, sqrt bounds

Usage:
    python benchmark/analyze_failures.py benchmark/results/deepseek_results.json
"""

import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------
# Failure classification heuristics
# ---------------------------------------------------------------------------

MEASURE_KEYWORDS = [
    "MeasureTheory", "Measure", "measurable", "integral", "∫",
    "probability", "ae", "filter_upwards", "PMF", "IsProbabilityMeasure",
    "iIndepFun", "Integrable", "HasSum", "tsum",
]

NUMERICAL_KEYWORDS = [
    "Real.exp", "Real.log", "Real.sqrt", "pow_nonneg", "pow_pos",
    "exp_le_exp", "log_le_log", "div_le_iff", "mul_le_mul",
    "geometric", "abs_le",
]

ALGEBRA_KEYWORDS = [
    "ring", "field_simp", "nlinarith", "linarith", "norm_num",
    "Finset.sum", "sup'", "resolvent",
]


def classify_failure(problem: dict, result: dict) -> str:
    """Classify a failure into one of the taxonomy categories."""
    stmt = problem.get("statement", "")
    domain = problem.get("domain", "")
    proof_lines = problem.get("proof_lines", 0)
    error = result.get("error", "") or ""

    # Long-horizon search: long proofs
    if proof_lines > 15:
        # Check if it's also a bridge problem
        if problem.get("difficulty") == "bridge":
            return "multi_domain_bridging"
        return "long_horizon_search"

    # Measure-theoretic: concentration/probability domains
    if domain == "concentration":
        if any(kw in stmt for kw in MEASURE_KEYWORDS):
            return "measure_theoretic"

    # Multi-domain bridging: bridge difficulty
    if problem.get("difficulty") == "bridge":
        return "multi_domain_bridging"

    # Numerical reasoning: exp/log/sqrt
    if any(kw in stmt for kw in NUMERICAL_KEYWORDS):
        return "numerical_reasoning"

    # Missing lemma: medium difficulty, short proof (likely one key lemma)
    if proof_lines <= 5 and domain not in ("concentration",):
        return "missing_lemma"

    # Default based on domain
    if domain == "concentration":
        return "measure_theoretic"
    if domain in ("sample_complexity", "regression"):
        return "multi_domain_bridging"

    return "long_horizon_search"


def analyze(results_path: Path) -> None:
    try:
        data = json.loads(results_path.read_text())
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"error: failed to load {results_path}: {e}", file=sys.stderr)
        sys.exit(1)
    prover = data["prover"]
    results = data["results"]

    # Load benchmark for problem metadata
    bench_path = ROOT / "benchmark" / "mlstatbench.json"
    try:
        benchmark = json.loads(bench_path.read_text())
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"error: failed to load {bench_path}: {e}", file=sys.stderr)
        sys.exit(1)
    problems_by_id = {p["id"]: p for p in benchmark["problems"]}

    failures = [r for r in results if not r.get("success")]
    successes = [r for r in results if r.get("success")]

    print(f"\n{'='*60}")
    print(f"Failure Analysis: {prover}")
    print(f"{'='*60}")
    print(f"Total: {len(results)}, Success: {len(successes)}, "
          f"Failure: {len(failures)}")
    print(f"Success rate: {len(successes)/len(results):.1%}")

    # Classify failures
    failure_types = Counter()
    failure_details = {}

    for r in failures:
        pid = r["problem_id"]
        problem = problems_by_id.get(pid, {})
        ftype = classify_failure(problem, r)
        failure_types[ftype] += 1
        failure_details.setdefault(ftype, []).append({
            "problem_id": pid,
            "theorem": r.get("theorem_name", ""),
            "domain": r.get("domain", ""),
            "difficulty": r.get("difficulty", ""),
            "proof_lines": problem.get("proof_lines", 0),
        })

    print(f"\n--- Failure Taxonomy ---")
    for ftype, count in failure_types.most_common():
        pct = count / len(failures) * 100 if failures else 0
        print(f"  {ftype}: {count} ({pct:.1f}%)")

    # Cross-tabulation: domain × failure type
    print(f"\n--- Domain × Failure Type ---")
    domains = sorted(set(r.get("domain", "?") for r in failures))
    ftypes = sorted(failure_types.keys())

    # Header
    header = f"{'Domain':<25}" + "".join(f"{ft:<22}" for ft in ftypes) + "Total"
    print(header)
    print("-" * len(header))

    for domain in domains:
        domain_failures = [r for r in failures if r.get("domain") == domain]
        counts = Counter()
        for r in domain_failures:
            problem = problems_by_id.get(r["problem_id"], {})
            ftype = classify_failure(problem, r)
            counts[ftype] += 1
        row = f"{domain:<25}" + "".join(
            f"{counts.get(ft, 0):<22}" for ft in ftypes
        ) + str(len(domain_failures))
        print(row)

    # Difficulty × success rate
    print(f"\n--- Success Rate by Difficulty ---")
    for diff in ["easy", "medium", "hard", "bridge"]:
        diff_results = [r for r in results if r.get("difficulty") == diff]
        if diff_results:
            succ = sum(1 for r in diff_results if r.get("success"))
            print(f"  {diff}: {succ}/{len(diff_results)} "
                  f"({succ/len(diff_results):.1%})")

    # Example failures for each type (for paper)
    print(f"\n--- Example Failures (for paper) ---")
    for ftype in ftypes:
        examples = failure_details.get(ftype, [])[:3]
        print(f"\n  [{ftype}]")
        for ex in examples:
            print(f"    {ex['theorem']} ({ex['domain']}, "
                  f"{ex['difficulty']}, {ex['proof_lines']} lines)")

    # Save analysis
    analysis = {
        "prover": prover,
        "total": len(results),
        "successes": len(successes),
        "failures": len(failures),
        "failure_taxonomy": dict(failure_types),
        "failure_details": {k: v[:5] for k, v in failure_details.items()},
    }
    out = results_path.parent / f"{prover}_analysis.json"
    out.write_text(json.dumps(analysis, indent=2))
    print(f"\nAnalysis saved to {out}")


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python benchmark/analyze_failures.py <results.json>",
              file=sys.stderr)
        sys.exit(1)
    analyze(Path(sys.argv[1]))
