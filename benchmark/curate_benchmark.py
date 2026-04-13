#!/usr/bin/env python3
"""Curate the MLStatBench benchmark from raw extracted problems.

Selects a balanced set of 200 problems across domains and difficulties,
with ground-truth proofs from our verified codebase.

Usage:
    python benchmark/curate_benchmark.py
"""

import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PRIVATE_DECL_RE = re.compile(
    r"^private\s+(?:def|theorem|lemma|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)"
)
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def load_raw() -> list[dict]:
    raw_path = ROOT / "benchmark" / "problems_raw.json"
    try:
        return json.loads(raw_path.read_text())
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"error: failed to load {raw_path}: {e}", file=sys.stderr)
        sys.exit(1)


def import_exists(module: str) -> bool:
    rel = Path(*module.split("."))
    candidates = [
        ROOT / rel.with_suffix(".lean"),
        ROOT / ".lake" / "packages" / "mathlib" / rel.with_suffix(".lean"),
    ]
    return any(path.exists() for path in candidates)


def private_names_in_source(source_file: str) -> set[str]:
    path = ROOT / source_file
    if not path.exists():
        return set()
    names: set[str] = set()
    for line in path.read_text().splitlines():
        match = PRIVATE_DECL_RE.match(line.strip())
        if match:
            names.add(match.group(1))
    return names


def mentions_private_name(problem: dict) -> bool:
    private_names = private_names_in_source(problem["source_file"])
    if not private_names:
        return False
    tokens = set(TOKEN_RE.findall(problem["statement"]))
    return bool(tokens & private_names)


def curate(problems: list[dict], target: int = 200) -> list[dict]:
    """Select a benchmark with explicit domain balance and difficulty spread."""

    difficulty_rank = {"bridge": 0, "hard": 1, "medium": 2, "easy": 3}
    source_rank = {"slt": 0, "rl": 1}

    def usable(problem: dict) -> bool:
        return (
            problem["proof_lines"] >= 2
            and problem["theorem_name"] != "hello"
            and "throughout" not in problem["theorem_name"]
            and not mentions_private_name(problem)
        )

    pool = [problem for problem in problems if usable(problem)]

    domain_targets = {
        "regression": 70,
        "bellman": 35,
        "concentration": 25,
        "exploration": 20,
        "policy_optimization": 15,
        "sample_complexity": 15,
        "simulation": 5,
        "other": 15,
    }
    difficulty_targets = {
        "bridge": 28,
        "hard": 65,
        "medium": 97,
        "easy": 10,
    }

    selected: list[dict] = []
    selected_ids: set[str] = set()
    remaining_domain = dict(domain_targets)
    remaining_difficulty = dict(difficulty_targets)

    def choose(candidates: list[dict], count: int) -> None:
        ordered = sorted(
            candidates,
            key=lambda problem: (
                source_rank.get(problem["source"], 99),
                difficulty_rank.get(problem["difficulty"], 99),
                problem["proof_lines"],
                problem["source_module"],
                problem["theorem_name"],
            ),
        )
        for problem in ordered:
            if len(selected) >= target or count <= 0:
                break
            if problem["id"] in selected_ids:
                continue
            selected.append(problem)
            selected_ids.add(problem["id"])
            count -= 1

    difficulties = ["bridge", "hard", "medium", "easy"]

    for difficulty in difficulties:
        for domain in domain_targets:
            quota = min(
                remaining_domain.get(domain, 0),
                remaining_difficulty.get(difficulty, 0),
            )
            if quota <= 0:
                continue
            before = len(selected)
            choose(
                [
                    problem
                    for problem in pool
                    if problem["domain"] == domain and problem["difficulty"] == difficulty
                ],
                quota,
            )
            taken = len(selected) - before
            remaining_domain[domain] -= taken
            remaining_difficulty[difficulty] -= taken

    for domain in domain_targets:
        quota = remaining_domain.get(domain, 0)
        if quota <= 0:
            continue
        before = len(selected)
        choose([problem for problem in pool if problem["domain"] == domain], quota)
        taken = len(selected) - before
        remaining_domain[domain] -= taken

    for difficulty in difficulties:
        quota = remaining_difficulty.get(difficulty, 0)
        if quota <= 0:
            continue
        before = len(selected)
        choose([problem for problem in pool if problem["difficulty"] == difficulty], quota)
        taken = len(selected) - before
        remaining_difficulty[difficulty] -= taken

    if len(selected) < target:
        choose(pool, target - len(selected))

    # Reassign IDs after selection for stable benchmark numbering.
    for i, p in enumerate(selected[:target]):
        p["id"] = f"mlstatbench_{i:04d}"

    return selected[:target]


def add_required_imports(problems: list[dict]) -> None:
    """Add required Mathlib import hints based on domain."""
    import_hints = {
        "bellman": ["Mathlib.Order.Filter.Basic", "Mathlib.Topology.Algebra.Order"],
        "concentration": [
            "Mathlib.Probability.Independence.Basic",
            "Mathlib.Probability.Moments",
            "Mathlib.Analysis.SpecialFunctions.ExpDeriv",
        ],
        "sample_complexity": [
            "Mathlib.Probability.Independence.Basic",
            "Mathlib.Analysis.SpecialFunctions.Log.Basic",
        ],
        "policy_optimization": ["Mathlib.Order.Filter.Basic"],
        "regression": [
            "Mathlib.Analysis.InnerProductSpace.Basic",
            "Mathlib.LinearAlgebra.Dimension.Finrank",
        ],
        "exploration": [],
        "simulation": [],
    }
    for p in problems:
        hints = import_hints.get(p["domain"], [])
        p["import_hints"] = [hint for hint in hints if import_exists(hint)]


def print_summary(problems: list[dict]) -> None:
    by_source = Counter(p["source"] for p in problems)
    by_domain = Counter(p["domain"] for p in problems)
    by_difficulty = Counter(p["difficulty"] for p in problems)
    by_kind = Counter(p["kind"] for p in problems)

    print(f"\n=== MLStatBench Curated Benchmark ===", file=sys.stderr)
    print(f"Total problems: {len(problems)}", file=sys.stderr)
    print(f"\nBy source: {dict(by_source)}", file=sys.stderr)
    print(f"By domain: {dict(by_domain)}", file=sys.stderr)
    print(f"By difficulty: {dict(by_difficulty)}", file=sys.stderr)
    print(f"By kind: {dict(by_kind)}", file=sys.stderr)

    # Show proof-line distribution
    proof_lines = [p["proof_lines"] for p in problems]
    print(f"\nProof lines: min={min(proof_lines)}, "
          f"median={sorted(proof_lines)[len(proof_lines)//2]}, "
          f"max={max(proof_lines)}, "
          f"mean={sum(proof_lines)/len(proof_lines):.1f}", file=sys.stderr)


if __name__ == "__main__":
    raw = load_raw()
    curated = curate(raw, target=200)
    add_required_imports(curated)
    print_summary(curated)

    out = ROOT / "benchmark" / "mlstatbench.json"
    out.write_text(json.dumps({
        "benchmark": "MLStatBench",
        "version": "0.1.0",
        "description": (
            "Machine Learning and Statistics Theorem Benchmark for "
            "automated theorem provers. Problems extracted from formally "
            "verified RL generalization theory (lean4-rl) and statistical "
            "learning theory (lean-stat-learning-theory) in Lean 4."
        ),
        "lean_version": "v4.28.0",
        "mathlib_version": "v4.28.0",
        "total_problems": len(curated),
        "problems": curated,
    }, indent=2))
    print(f"\nWrote {len(curated)} problems to {out}", file=sys.stderr)
