#!/usr/bin/env python3
"""Export a retrieval corpus of theorem statements (without proofs).

Scans all .lean files under RLGeneralization/ and outputs one JSON object
per line containing the theorem statement, module ID, verification status,
and domain tags derived from the module path.

Output: benchmark/retrieval_corpus.jsonl

Usage:
    python scripts/export_retrieval_corpus.py
    python scripts/export_retrieval_corpus.py --root /path/to/lean4-rl
    python scripts/export_retrieval_corpus.py --out benchmark/retrieval_corpus.jsonl
"""

import argparse
import json
import re
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

DECL_RE = re.compile(r"^(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)")

# Tag derivation from module path components
TAG_MAP: dict[str, list[str]] = {
    "Concentration": ["concentration"],
    "Hoeffding": ["concentration", "hoeffding"],
    "Bernstein": ["concentration", "bernstein"],
    "Bennett": ["concentration", "bennett"],
    "BennettMGF": ["concentration", "bennett"],
    "MatrixBernstein": ["concentration", "matrix"],
    "SelfNormalized": ["concentration", "self-normalized"],
    "SubGaussian": ["concentration", "sub-gaussian"],
    "AzumaHoeffding": ["concentration", "azuma-hoeffding"],
    "MDPConcentration": ["concentration", "mdp"],
    "McDiarmid": ["concentration", "mcdiarmid"],
    "McDiarmidFull": ["concentration", "mcdiarmid"],
    "JohnsonLindenstrauss": ["concentration", "jl"],
    "Talagrand": ["concentration", "talagrand"],
    "LargeDeviations": ["concentration", "large-deviations"],
    "Isoperimetric": ["concentration", "isoperimetric"],
    "PhiEntropy": ["concentration", "entropy-method"],
    "StochasticCalculus": ["concentration", "stochastic-calculus"],
    "CLT": ["concentration", "clt"],
    "GenerativeModel": ["concentration", "generative-model", "pac"],
    "GenerativeModelCore": ["concentration", "generative-model"],
    "DiscreteConcentration": ["concentration", "discrete"],
    "MarkovChain": ["concentration", "markov-chain"],
    "MDP": ["mdp"],
    "Basic": ["mdp", "definitions"],
    "BellmanContraction": ["mdp", "bellman", "contraction"],
    "SimulationLemma": ["mdp", "simulation"],
    "SimulationResolvent": ["mdp", "simulation", "resolvent"],
    "ValueIteration": ["mdp", "value-iteration"],
    "PolicyIteration": ["mdp", "policy-iteration"],
    "Resolvent": ["mdp", "resolvent"],
    "BanachFixedPoint": ["mdp", "fixed-point"],
    "PerformanceDifference": ["mdp", "pdl"],
    "OccupancyMeasure": ["mdp", "occupancy"],
    "MatrixResolvent": ["mdp", "matrix-resolvent"],
    "FiniteHorizon": ["mdp", "finite-horizon"],
    "LPFormulation": ["mdp", "lp"],
    "AverageReward": ["mdp", "average-reward"],
    "HJB": ["mdp", "continuous"],
    "POMDP": ["mdp", "pomdp"],
    "MultiAgent": ["mdp", "multi-agent"],
    "Bandits": ["bandit"],
    "UCB": ["bandit", "ucb"],
    "EXP3": ["bandit", "exp3", "adversarial"],
    "LowerBound": ["lower-bound"],
    "ThompsonSampling": ["bandit", "thompson-sampling", "bayesian"],
    "LinearBandits": ["bandit", "linear"],
    "BanditConcentration": ["bandit", "concentration"],
    "Generalization": ["generalization"],
    "SampleComplexity": ["sample-complexity"],
    "ComponentWise": ["generalization", "component-wise"],
    "MinimaxSampleComplexity": ["generalization", "minimax"],
    "PACBayes": ["pac-bayes"],
    "PolicyEvaluation": ["policy-evaluation"],
    "DudleyRL": ["generalization", "dudley", "covering-number"],
    "FiniteHorizonSampleComplexity": ["generalization", "finite-horizon"],
    "LinearFeatures": ["linear", "regression"],
    "LSVI": ["lsvi", "regression"],
    "RegressionBridge": ["regression", "bridge"],
    "BilinearRank": ["bilinear-rank"],
    "GOLF": ["bilinear-rank", "golf"],
    "Exploration": ["exploration"],
    "UCBVI": ["ucbvi", "exploration"],
    "VarianceUCBVI": ["ucbvi", "variance", "exploration"],
    "UCBVISimulation": ["ucbvi", "simulation"],
    "BatchUCBVI": ["ucbvi", "batch"],
    "PolicyOptimization": ["policy-optimization"],
    "PolicyGradient": ["policy-gradient"],
    "CPI": ["cpi", "conservative"],
    "Optimality": ["optimality"],
    "NPG": ["npg", "natural-gradient"],
    "TRPO": ["trpo", "trust-region"],
    "ImitationLearning": ["imitation"],
    "MaxEntIRL": ["imitation", "irl", "max-entropy"],
    "OfflineRL": ["offline-rl"],
    "FQI": ["fqi", "regression"],
    "Pessimism": ["offline-rl", "pessimism"],
    "LinearMDP": ["linear-mdp"],
    "EllipticalPotential": ["linear-mdp", "elliptical-potential"],
    "Regret": ["regret"],
    "Complexity": ["complexity"],
    "VCDimension": ["vc-dimension", "complexity"],
    "Rademacher": ["rademacher", "complexity"],
    "Symmetrization": ["symmetrization", "complexity"],
    "CoveringPacking": ["covering-number", "complexity"],
    "GenericChaining": ["generic-chaining", "complexity"],
    "EluderDimension": ["eluder-dimension", "complexity"],
    "LowerBounds": ["lower-bound"],
    "FanoLeCam": ["lower-bound", "fano", "le-cam"],
    "Algorithms": ["algorithm"],
    "QLearning": ["q-learning", "algorithm"],
    "LinearTD": ["td-learning", "linear"],
    "Privacy": ["privacy"],
    "DPRewards": ["privacy", "differential-privacy"],
    "Optimization": ["optimization"],
    "SGD": ["sgd", "optimization"],
    "Approximation": ["approximation"],
    "RKHS": ["rkhs", "kernel"],
    "NeuralNetwork": ["neural-network"],
    "LQR": ["lqr", "control"],
    "RiccatiPolicy": ["lqr", "riccati"],
}


def derive_tags(module: str) -> list[str]:
    """Derive tags from module path components."""
    parts = module.replace("RLGeneralization.", "").split(".")
    tags: list[str] = []
    seen: set[str] = set()
    for part in parts:
        for tag in TAG_MAP.get(part, []):
            if tag not in seen:
                tags.append(tag)
                seen.add(tag)
    # If no specific tags, use the first path component lowercased
    if not tags and parts:
        tags.append(parts[0].lower())
    return tags


# ---------------------------------------------------------------------------
# Manifest loader
# ---------------------------------------------------------------------------


def load_manifest_statuses(root: Path) -> dict[str, str]:
    """Load module-level and theorem-level statuses from verification_manifest.json."""
    manifest_path = root / "verification_manifest.json"
    if not manifest_path.exists():
        return {}
    data = json.loads(manifest_path.read_text())
    statuses: dict[str, str] = {}
    for entry in data.get("verified_target", {}).get("modules", []):
        statuses[entry["module"]] = entry.get("status", "unknown")
    for entry in data.get("theorems", []):
        statuses[entry["name"]] = entry.get("status", "unknown")
    return statuses


# ---------------------------------------------------------------------------
# Statement extraction
# ---------------------------------------------------------------------------


def find_assignment(lines: list[str], start: int) -> tuple[int, int] | None:
    """Find the top-level `:=` that starts the proof body."""
    depth = 0
    for li in range(start, min(start + 80, len(lines))):
        line = lines[li]
        col = 0
        while col < len(line):
            if line.startswith("--", col):
                break
            ch = line[col]
            if ch in "({[":
                depth += 1
            elif ch in ")}]":
                depth = max(depth - 1, 0)
            elif ch == ":" and col + 1 < len(line) and line[col + 1] == "=" and depth == 0:
                return li, col
            col += 1
    return None


def extract_statements_from_file(filepath: Path, root: Path,
                                  statuses: dict[str, str]) -> list[dict]:
    """Extract theorem statements (without proofs) from a .lean file."""
    text = filepath.read_text()
    all_lines = text.splitlines()
    results: list[dict] = []

    try:
        rel = filepath.relative_to(root)
    except ValueError:
        rel = filepath
    module_name = str(rel).replace("/", ".").removesuffix(".lean")
    tags = derive_tags(module_name)

    i = 0
    while i < len(all_lines):
        m = DECL_RE.match(all_lines[i])
        if not m:
            i += 1
            continue

        kind = m.group(1)
        name = m.group(2)
        decl_start = i

        assignment = find_assignment(all_lines, i)
        if assignment is None:
            i += 1
            continue

        body_line, assign_col = assignment

        # Statement: everything up to (but not including) `:=`
        stmt_lines = all_lines[decl_start:body_line + 1]
        stmt_lines[-1] = stmt_lines[-1][:assign_col].rstrip()
        statement = "\n".join(stmt_lines).strip()

        # Determine status
        status = "unknown"
        qualified = f"{module_name}.{name}"
        for key in [qualified, name, module_name]:
            if key in statuses:
                status = statuses[key]
                break

        theorem_id = f"{module_name}.{name}"

        results.append({
            "id": theorem_id,
            "kind": kind,
            "statement": statement,
            "status": status,
            "tags": tags,
            "source_file": str(rel),
            "source_line": decl_start + 1,
        })

        # Skip to end of proof
        proof_end = body_line + 1
        while proof_end < len(all_lines):
            stripped = all_lines[proof_end].strip()
            if DECL_RE.match(all_lines[proof_end]):
                break
            if stripped.startswith("/-"):
                break
            if re.match(r"^end\b", stripped):
                break
            if re.match(
                r"^(variable|variables|open|local|scoped|attribute|namespace|section|noncomputable)\b",
                stripped,
            ):
                break
            proof_end += 1
        i = proof_end

    return results


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Export theorem statements as a retrieval corpus.")
    parser.add_argument("--root", type=Path,
                        default=Path(__file__).resolve().parent.parent,
                        help="Project root directory (default: auto-detect)")
    parser.add_argument("--out", type=Path, default=None,
                        help="Output JSONL path (default: <root>/benchmark/retrieval_corpus.jsonl)")
    parser.add_argument("--source-dir", type=str, default="RLGeneralization",
                        help="Subdirectory to scan (default: RLGeneralization)")
    args = parser.parse_args()

    root = args.root.resolve()
    out_path = (args.out or root / "benchmark" / "retrieval_corpus.jsonl").resolve()
    source_dir = root / args.source_dir

    if not source_dir.is_dir():
        print(f"error: {source_dir} is not a directory", file=sys.stderr)
        sys.exit(1)

    statuses = load_manifest_statuses(root)

    all_entries: list[dict] = []
    lean_files = sorted(source_dir.rglob("*.lean"))
    print(f"Scanning {len(lean_files)} .lean files under {source_dir.name}/",
          file=sys.stderr)

    for filepath in lean_files:
        entries = extract_statements_from_file(filepath, root, statuses)
        all_entries.extend(entries)

    # Write JSONL
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        for entry in all_entries:
            f.write(json.dumps(entry) + "\n")

    # Summary
    by_status: dict[str, int] = {}
    by_tag: dict[str, int] = {}
    for e in all_entries:
        by_status[e["status"]] = by_status.get(e["status"], 0) + 1
        for tag in e["tags"]:
            by_tag[tag] = by_tag.get(tag, 0) + 1

    print(f"\nExported {len(all_entries)} theorem statements", file=sys.stderr)
    print(f"  Output: {out_path}", file=sys.stderr)
    print(f"  By status: {json.dumps(by_status, indent=4)}", file=sys.stderr)
    top_tags = sorted(by_tag.items(), key=lambda x: -x[1])[:15]
    print(f"  Top tags: {json.dumps(dict(top_tags), indent=4)}", file=sys.stderr)


if __name__ == "__main__":
    main()
