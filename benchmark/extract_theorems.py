#!/usr/bin/env python3
"""Extract theorem statements and metadata from the lean4-rl trusted root.

Produces a JSON dataset of benchmark problems for the MLStatBench evaluation.
Each problem includes the theorem statement, source location, domain tags,
difficulty level, and ground-truth proof status.

Usage:
    python benchmark/extract_theorems.py > benchmark/problems.json
"""

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------
# 1. Parse the trusted root import list
# ---------------------------------------------------------------------------

def get_trusted_modules() -> list[str]:
    """Read module names from RLGeneralization.lean."""
    root_file = ROOT / "RLGeneralization.lean"
    try:
        text = root_file.read_text()
    except FileNotFoundError:
        print(f"error: {root_file} not found", file=sys.stderr)
        sys.exit(1)
    modules = []
    for line in text.splitlines():
        m = re.match(r"^import\s+(RLGeneralization\.\S+)", line)
        if m:
            modules.append(m.group(1))
    return modules


def module_to_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")

# ---------------------------------------------------------------------------
# 2. Extract theorem/lemma declarations from .lean files
# ---------------------------------------------------------------------------

# Regex for theorem/lemma declarations (handles multiline via subsequent reads)
DECL_RE = re.compile(
    r"^(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)

# Domain classification rules based on module path
DOMAIN_MAP = {
    "MDP.Basic": "bellman",
    "MDP.BellmanContraction": "bellman",
    "MDP.SimulationLemma": "simulation",
    "MDP.ValueIteration": "bellman",
    "MDP.PolicyIteration": "bellman",
    "MDP.Resolvent": "bellman",
    "MDP.BanachFixedPoint": "bellman",
    "MDP.PerformanceDifference": "policy_optimization",
    "MDP.OccupancyMeasure": "policy_optimization",
    "MDP.MatrixResolvent": "bellman",
    "MDP.SimulationResolvent": "simulation",
    "MDP.FiniteHorizon": "bellman",
    "Generalization.SampleComplexity": "sample_complexity",
    "Generalization.ComponentWise": "sample_complexity",
    "Generalization.MinimaxSampleComplexity": "sample_complexity",
    "Generalization.PACBayes": "sample_complexity",
    "Generalization.FiniteHorizonSampleComplexity": "sample_complexity",
    "LinearFeatures.LSVI": "regression",
    "LinearFeatures.RegressionBridge": "regression",
    "Concentration.Hoeffding": "concentration",
    "Concentration.Bernstein": "concentration",
    "Concentration.GenerativeModelCore": "concentration",
    "Concentration.GenerativeModel": "concentration",
    "Concentration.SubGaussian": "concentration",
    "Concentration.Bennett": "concentration",
    "Concentration.McDiarmid": "concentration",
    "Concentration.MatrixBernstein": "concentration",
    "Concentration.JohnsonLindenstrauss": "concentration",
    "Concentration.AzumaHoeffding": "concentration",
    "Concentration.MarkovChain": "concentration",
    "BilinearRank.Auxiliary": "bellman",
    "Bandits.BanditConcentration": "concentration",
    "Exploration.UCBVI": "exploration",
    "Exploration.VarianceUCBVI": "exploration",
    "Exploration.BatchUCBVI": "exploration",
    "PolicyOptimization.PolicyGradient": "policy_optimization",
    "PolicyOptimization.CPI": "policy_optimization",
    "PolicyOptimization.Optimality": "policy_optimization",
    "PolicyOptimization.NPG": "policy_optimization",
    "ImitationLearning.Basic": "policy_optimization",
    "OfflineRL.FQI": "regression",
    "LinearMDP.Basic": "regression",
    "LinearMDP.EllipticalPotential": "regression",
    "LinearMDP.Regret": "exploration",
    "MDP.LPFormulation": "bellman",
    "MDP.AverageReward": "bellman",
    "OfflineRL.Pessimism": "regression",
    "Complexity.VCDimension": "sample_complexity",
    "Complexity.Rademacher": "sample_complexity",
    "Complexity.Symmetrization": "sample_complexity",
    "Complexity.CoveringPacking": "sample_complexity",
    "LowerBounds.FanoLeCam": "sample_complexity",
    "Algorithms.QLearning": "bellman",
    "Algorithms.LinearTD": "regression",
    "Concentration.Talagrand": "concentration",
    "Concentration.LargeDeviations": "concentration",
    "Concentration.Isoperimetric": "concentration",
    "Concentration.PhiEntropy": "concentration",
    "Concentration.StochasticCalculus": "concentration",
    "Concentration.CLT": "concentration",
    "Complexity.GenericChaining": "sample_complexity",
    "Privacy.DPRewards": "other",
    "Optimization.SGD": "regression",
    "Approximation.RKHS": "regression",
    "Approximation.NeuralNetwork": "regression",
    "MDP.HJB": "bellman",
    "MDP.POMDP": "bellman",
    "MDP.MultiAgent": "bellman",
    "LQR.Basic": "other",
    "Bandits.UCB": "exploration",
    "Bandits.EXP3": "exploration",
    "Bandits.LowerBound": "exploration",
    "Bandits.ThompsonSampling": "exploration",
    "Test.SimpleMDP": "bellman",
    # --- Added: 44 modules previously defaulting to "other" ---
    "Algorithms.GenerativeQLearning": "bellman",
    "Algorithms.MCTS": "bellman",
    "Algorithms.ModelBased": "bellman",
    "Algorithms.SARSA": "bellman",
    "Bandits.EXP3Bandit": "exploration",
    "Bandits.LinearBandits": "exploration",
    "Bandits.UCBRegret": "exploration",
    "BilinearRank.GOLF": "exploration",
    "BilinearRank.RepresentationBound": "sample_complexity",
    "Complexity.EluderDimension": "sample_complexity",
    "Concentration.BennettMGF": "concentration",
    "Concentration.DiscreteConcentration": "concentration",
    "Concentration.GenerativeModelBernstein": "concentration",
    "Concentration.GenerativeModelEmpirical": "concentration",
    "Concentration.GenerativeModelMinimax": "concentration",
    "Concentration.GenerativeModelPAC": "concentration",
    "Concentration.MDPConcentration": "concentration",
    "Concentration.MDPFiltration": "concentration",
    "Concentration.McDiarmidFull": "concentration",
    "Concentration.RobbinsSiegmund": "concentration",
    "Concentration.SelfNormalized": "concentration",
    "Concentration.TrajectoryMeasure": "concentration",
    "Executable.CertifiedVI": "bellman",
    "Executable.LPCertificate": "bellman",
    "Executable.TabularPlanner": "bellman",
    "Exploration.RewardFree": "exploration",
    "Exploration.UCBVIProbability": "exploration",
    "Exploration.UCBVISimulation": "exploration",
    "Generalization.DudleyRL": "sample_complexity",
    "Generalization.PolicyEvaluation": "sample_complexity",
    "Generalization.SLTBridge": "sample_complexity",
    "Generalization.TransferRL": "sample_complexity",
    "Generalization.UniformConvergence": "sample_complexity",
    "ImitationLearning.MaxEntIRL": "policy_optimization",
    "LQR.RiccatiPolicy": "bellman",
    "LinearMDP.EllipticalBridge": "regression",
    "LinearMDP.RegretFull": "exploration",
    "LowerBounds.MinimaxMatching": "sample_complexity",
    "MDP.AverageRewardNonasymptotic": "bellman",
    "MDP.ConstrainedMDP": "bellman",
    "MDP.Options": "bellman",
    "MDP.RewardShaping": "bellman",
    "PolicyOptimization.ActorCritic": "policy_optimization",
    "PolicyOptimization.TRPO": "policy_optimization",
}


def classify_domain(module: str) -> str:
    """Classify a module into a domain category."""
    suffix = module.removeprefix("RLGeneralization.")
    return DOMAIN_MAP.get(suffix, "other")


def classify_difficulty(status: str, proof_lines: int, domain: str) -> str:
    """Heuristic difficulty classification."""
    if status == "exact" and proof_lines <= 5:
        return "easy"
    if status == "exact" and proof_lines <= 20:
        return "medium"
    if status in ("weaker", "conditional"):
        return "hard"
    if domain == "concentration":
        return "hard"
    return "medium"


def is_bridge_problem(decl_name: str, module: str) -> bool:
    """Detect cross-domain 'bridge' problems that combine multiple areas."""
    bridge_keywords = [
        "pac_rl_generative_model",
        "minimax_value_gap",
        "sample_complexity",
        "generative_model_pac",
        "value_iteration_epsilon_optimal",
        "pdl_occupancy_form",
        "empiricalGreedyValue_isValueOf",
        "minimax_from_empirical",
        "lsvi_sample_complexity",
    ]
    return any(kw in decl_name for kw in bridge_keywords)


def binder_names_from_lines(lines: list[str]) -> list[str]:
    def is_valid_name(token: str) -> bool:
        if not token or token == "_":
            return False
        base = token.rstrip("'")
        if not base or base[0].isdigit() or "." in base:
            return False
        return not any(ch in " (){}[],:;→" for ch in base)

    names: list[str] = []
    for line in lines:
        for chunk in re.findall(r"[\(\{]([^:(){}]+?)\s*:", line):
            for token in chunk.replace("→", " ").split():
                token = token.strip()
                if is_valid_name(token):
                    names.append(token)
    return names


def top_level_binder_names(lines: list[str]) -> list[str]:
    def is_valid_name(token: str) -> bool:
        if not token or token == "_":
            return False
        base = token.rstrip("'")
        if not base or base[0].isdigit() or "." in base:
            return False
        return not any(ch in " (){}[],:;→" for ch in base)

    text = "\n".join(lines)
    names: list[str] = []
    depth = 0
    group_start: int | None = None
    opening: str | None = None

    for idx, ch in enumerate(text):
        if ch in "({[":
            if depth == 0:
                group_start = idx + 1
                opening = ch
            depth += 1
            continue
        if ch in ")}]":
            if depth == 0:
                continue
            depth -= 1
            if depth == 0 and group_start is not None and opening in "({":
                group = text[group_start:idx]
                if ":" in group:
                    head = group.split(":", 1)[0]
                    for token in head.split():
                        token = token.strip()
                        if is_valid_name(token):
                            names.append(token)
                group_start = None
                opening = None
    return names


def context_binder_names_with_mode(lines: list[str]) -> list[tuple[str, str]]:
    """Extract binder names from variable lines with their binding mode.

    Returns (name, mode) pairs where mode is ``"explicit"`` for ``(x : T)``,
    ``"implicit"`` for ``{x : T}``, or ``"instance"`` for ``[C x]``.
    Only explicit and implicit binders are returned (instances are unnamed).
    """
    def _valid(token: str) -> bool:
        if not token or token == "_":
            return False
        base = token.rstrip("'")
        if not base or base[0].isdigit() or "." in base:
            return False
        return not any(ch in " (){}[],:;→" for ch in base)

    text = "\n".join(lines)
    result: list[tuple[str, str]] = []
    depth = 0
    group_start: int | None = None
    opening: str | None = None

    for idx, ch in enumerate(text):
        if ch in "({[":
            if depth == 0:
                group_start = idx + 1
                opening = ch
            depth += 1
            continue
        if ch in ")}]":
            if depth == 0:
                continue
            depth -= 1
            if depth == 0 and group_start is not None:
                mode = {"(": "explicit", "{": "implicit"}.get(opening)
                if mode is not None:
                    group = text[group_start:idx]
                    if ":" in group:
                        head = group.split(":", 1)[0]
                        for token in head.split():
                            token = token.strip()
                            if _valid(token):
                                result.append((token, mode))
                group_start = None
                opening = None
    return result


def normalize_proof_arg_names(names: list[str]) -> list[str]:
    normalized: list[str] = []
    seen: set[str] = set()
    for name in names:
        base = name.rstrip("'")
        if (
            not base
            or base[0].isdigit()
            or "." in base
            or any(ch in " (){}[],:;→" for ch in base)
        ):
            continue
        if name in seen:
            continue
        normalized.append(name)
        seen.add(name)
    return normalized


def theorem_binder_names(statement: str) -> list[str]:
    statement = "\n".join(
        line for line in statement.splitlines() if not line.strip().startswith("--")
    )
    depth = 0
    prefix_end = len(statement)
    for idx, ch in enumerate(statement):
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth = max(depth - 1, 0)
        elif ch == ":" and depth == 0:
            prefix_end = idx
            break
    return top_level_binder_names(statement[:prefix_end].splitlines())


def identifier_tokens(text: str) -> set[str]:
    """Extract all identifier tokens from a Lean expression.

    Splits qualified names like ``M.gap`` into their components (``M``, ``gap``)
    so that namespace receiver variables are detected.
    """
    tokens: set[str] = set()
    for raw in re.split(r"[\s(){}\[\],:;→]+", text):
        raw = raw.strip()
        if not raw:
            continue
        # Split qualified names so "B.gap" yields {"B", "gap"}
        for part in raw.split("."):
            part = part.strip()
            if not part:
                continue
            base = part.rstrip("'")
            if not base or base[0].isdigit():
                continue
            if any(ch in " (){}[],:;→" for ch in base):
                continue
            tokens.add(part)
    return tokens


def find_top_level_assignment(lines: list[str], start_idx: int) -> tuple[int, int] | None:
    """Find the `:=` that starts the proof body for a declaration.

    This must ignore `:=` tokens that appear inside binders, terms, or `let`
    expressions in the theorem statement itself.
    """
    depth = 0
    fallback: tuple[int, int] | None = None
    for line_idx in range(start_idx, len(lines)):
        if line_idx > start_idx and fallback is not None:
            stripped = lines[line_idx].strip()
            if DECL_RE.match(lines[line_idx]) or stripped.startswith("/-") or stripped.startswith("end "):
                return fallback
        line = lines[line_idx]
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
                remainder = line[col + 2:].strip()
                if remainder == "" or remainder.startswith("by"):
                    return line_idx, col
                fallback = (line_idx, col)
            col += 1
    return fallback


def find_last_top_level_type_colon(decl_lines: list[str], assign_col: int) -> tuple[int, int] | None:
    """Find the final top-level `:` separating binders from the theorem type."""
    depth = 0
    last: tuple[int, int] | None = None
    for line_idx, line in enumerate(decl_lines):
        limit = assign_col if line_idx == len(decl_lines) - 1 else len(line)
        col = 0
        while col < limit:
            if line.startswith("--", col):
                break
            ch = line[col]
            if ch in "({[":
                depth += 1
            elif ch in ")}]":
                depth = max(depth - 1, 0)
            elif ch == ":" and depth == 0:
                if col + 1 >= limit or line[col + 1] != "=":
                    last = (line_idx, col)
            col += 1
    return last


def extract_declarations(filepath: Path, module: str) -> list[dict]:
    """Extract theorem/lemma declarations from a .lean file."""
    text = filepath.read_text()
    lines = text.splitlines()
    decls = []
    block_stack = [{"kind": "root", "name": "", "open_line": "", "context_lines": []}]

    i = 0
    while i < len(lines):
        stripped = lines[i].strip()

        ns_match = re.match(r"^namespace\s+([A-Za-z0-9_.']+)\s*$", stripped)
        if ns_match:
            block_stack.append({
                "kind": "namespace",
                "name": ns_match.group(1),
                "open_line": lines[i],
                "context_lines": [],
            })
            i += 1
            continue

        if re.match(r"^(section|noncomputable\s+section)\b", stripped):
            block_stack.append({
                "kind": "section",
                "name": "",
                "open_line": lines[i],
                "context_lines": [],
            })
            i += 1
            continue

        if re.match(r"^(variable|variables|open|local|scoped|attribute)\b", stripped):
            block_stack[-1]["context_lines"].append(lines[i])
            i += 1
            continue

        if stripped.startswith("end"):
            if len(block_stack) > 1:
                block_stack.pop()
            i += 1
            continue

        m = DECL_RE.match(lines[i])
        if m:
            kind = m.group(1)       # theorem or lemma
            name = m.group(2)
            namespaces = [frame["name"] for frame in block_stack if frame["kind"] == "namespace"]
            qualified_name = ".".join(namespaces + [name]) if namespaces else name
            context_prefix = []
            for frame in block_stack:
                if frame["kind"] == "namespace":
                    context_prefix.append(frame["open_line"])
                context_prefix.extend(frame["context_lines"])
            context_suffix = [f"end {frame['name']}" for frame in reversed(block_stack)
                              if frame["kind"] == "namespace"]

            assignment = find_top_level_assignment(lines, i)
            if assignment is None:
                i += 1
                continue
            body_start, assign_col = assignment
            decl_lines = lines[i:body_start + 1]

            # Count proof lines (rough: from := to next theorem/end).
            proof_end = body_start + 1
            while proof_end < len(lines):
                stripped_end = lines[proof_end].strip()
                if (DECL_RE.match(lines[proof_end]) or
                    stripped_end.startswith("/-") or
                    stripped_end.startswith("end ") or
                    re.match(r"^(variable|variables|open|local|scoped|attribute)\b", stripped_end)):
                    break
                proof_end += 1
            proof_lines = proof_end - body_start

            # Extract the statement (type signature only) by trimming the
            # top-level proof-introducing `:=` from the final declaration line.
            statement_lines = decl_lines.copy()
            statement_lines[-1] = statement_lines[-1][:assign_col].rstrip()
            statement = "\n".join(statement_lines).strip()
            context_var_lines = [
                line for line in context_prefix
                if re.match(r"^(variable|variables)\b", line.strip())
            ]
            thm_binder_names = theorem_binder_names(statement)
            statement_tokens = identifier_tokens(statement)

            # Split context variables into receiver (explicit) vs implicit.
            # Receivers are the namespace-scoped variables like (M : FiniteMDP)
            # that Lean auto-inserts when they appear free in the theorem type.
            binders_with_mode = context_binder_names_with_mode(context_var_lines)
            receiver_args = [
                name for name, mode in binders_with_mode
                if mode == "explicit" and name in statement_tokens
            ]
            context_arg_names = [
                name for name, mode in binders_with_mode
                if name in statement_tokens
            ]
            proof_arg_names = normalize_proof_arg_names(
                context_arg_names + thm_binder_names
            )

            # Extract docstring (look backwards from declaration)
            docstring = ""
            k = i - 1
            while k >= 0 and lines[k].strip() == "":
                k -= 1
            if k >= 0 and (lines[k].strip().endswith("-/") or
                           lines[k].strip().startswith("-/")):
                doc_end = k
                while k >= 0 and "/-" not in lines[k]:
                    k -= 1
                if k >= 0:
                    docstring = "\n".join(lines[k:doc_end+1]).strip()
                    # Clean up
                    docstring = re.sub(r"/--?\s*", "", docstring)
                    docstring = re.sub(r"\s*-/", "", docstring)
                    docstring = docstring.strip()

            domain = classify_domain(module)

            decls.append({
                "name": name,
                "qualified_name": qualified_name,
                "kind": kind,
                "module": module,
                "file": str(filepath.relative_to(ROOT)),
                "line": i + 1,
                "context_prefix": context_prefix,
                "context_suffix": context_suffix,
                "proof_arg_names": proof_arg_names,
                "receiver_args": receiver_args,
                "theorem_binders": thm_binder_names,
                "has_receiver": len(receiver_args) > 0,
                "statement": statement,
                "docstring": docstring[:500] if docstring else "",
                "domain": domain,
                "proof_lines": proof_lines,
            })

            i = proof_end
        else:
            i += 1

    return decls

# ---------------------------------------------------------------------------
# 3. Load status metadata from verification_manifest.json
# ---------------------------------------------------------------------------

def load_statuses() -> dict[str, str]:
    """Load theorem statuses from verification_manifest.json."""
    manifest_path = ROOT / "verification_manifest.json"
    try:
        manifest = json.loads(manifest_path.read_text())
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"error: failed to load {manifest_path}: {e}", file=sys.stderr)
        sys.exit(1)
    statuses = {}

    # Module-level statuses
    for entry in manifest.get("verified_target", {}).get("modules", []):
        statuses[entry["module"]] = entry.get("status", "unknown")

    # Theorem-level statuses
    for entry in manifest.get("theorems", []):
        statuses[entry["name"]] = entry.get("status", "unknown")

    return statuses

# ---------------------------------------------------------------------------
# 4. Build the benchmark problem set
# ---------------------------------------------------------------------------

def build_problems() -> list[dict]:
    modules = get_trusted_modules()
    statuses = load_statuses()

    all_decls = []
    for module in modules:
        path = module_to_path(module)
        if path.exists():
            decls = extract_declarations(path, module)
            all_decls.extend(decls)

    # Also extract from the SLT reference library (for diversity)
    # Prefer Lake-managed path (.lake/packages/SLT), fall back to references/
    slt_root = ROOT / ".lake" / "packages" / "SLT"
    if not slt_root.exists():
        slt_root = ROOT / "references" / "lean-stat-learning-theory"
    slt_count = 0
    if slt_root.exists():
        for lean_file in sorted(slt_root.rglob("SLT/**/*.lean")):
            module_name = str(lean_file.relative_to(slt_root)).replace("/", ".").removesuffix(".lean")
            decls = extract_declarations(lean_file, module_name)
            for d in decls:
                d["source"] = "slt"
                d["domain"] = "regression"  # SLT is mostly regression/learning theory
            slt_count += len(decls)
            all_decls.extend(decls)

    problems = []
    for idx, decl in enumerate(all_decls):
        source = decl.pop("source", "rl")

        # Look up status
        status = "unknown"
        # Try full qualified name
        for key in [
            decl["qualified_name"],
            decl["name"],
            f"FiniteMDP.{decl['name']}",
            f"FiniteHorizonMDP.{decl['name']}",
            f"BanditInstance.{decl['name']}",
            f"ImitationSetting.{decl['name']}",
            f"MixingChain.{decl['name']}",
        ]:
            if key in statuses:
                status = statuses[key]
                break
        # Fall back to module status
        if status == "unknown" and decl["module"] in statuses:
            status = statuses[decl["module"]]

        # SLT library compiles without sorry; infer all its theorems as exact
        if status == "unknown" and source == "slt":
            status = "exact"

        if status == "unknown":
            print(f"warning: no status found for {decl['qualified_name']} "
                  f"in {decl['module']}", file=sys.stderr)

        difficulty = classify_difficulty(status, decl["proof_lines"], decl["domain"])
        if is_bridge_problem(decl["name"], decl["module"]):
            difficulty = "bridge"

        problems.append({
            "id": f"{'rl' if source == 'rl' else 'slt'}_{idx:04d}",
            "source": source,
            "source_file": decl["file"],
            "source_line": decl["line"],
            "source_module": decl["module"],
            "theorem_name": decl["name"],
            "qualified_name": decl["qualified_name"],
            "context_prefix": decl["context_prefix"],
            "context_suffix": decl["context_suffix"],
            "proof_arg_names": decl["proof_arg_names"],
            "receiver_args": decl.get("receiver_args", []),
            "theorem_binders": decl.get("theorem_binders", []),
            "has_receiver": decl.get("has_receiver", False),
            "kind": decl["kind"],
            "statement": decl["statement"],
            "informal_description": decl["docstring"],
            "domain": decl["domain"],
            "difficulty": difficulty,
            "status": status,
            "proof_lines": decl["proof_lines"],
            "problem_type": "full_theorem_proving",
        })

    return problems


def print_summary(problems: list[dict]) -> None:
    """Print summary statistics to stderr."""
    total = len(problems)
    by_source = {}
    by_domain = {}
    by_difficulty = {}
    by_status = {}

    for p in problems:
        by_source[p["source"]] = by_source.get(p["source"], 0) + 1
        by_domain[p["domain"]] = by_domain.get(p["domain"], 0) + 1
        by_difficulty[p["difficulty"]] = by_difficulty.get(p["difficulty"], 0) + 1
        by_status[p["status"]] = by_status.get(p["status"], 0) + 1

    print(f"\n=== MLStatBench Problem Extraction ===", file=sys.stderr)
    print(f"Total problems: {total}", file=sys.stderr)
    print(f"\nBy source:", file=sys.stderr)
    for k, v in sorted(by_source.items()):
        print(f"  {k}: {v}", file=sys.stderr)
    print(f"\nBy domain:", file=sys.stderr)
    for k, v in sorted(by_domain.items()):
        print(f"  {k}: {v}", file=sys.stderr)
    print(f"\nBy difficulty:", file=sys.stderr)
    for k, v in sorted(by_difficulty.items()):
        print(f"  {k}: {v}", file=sys.stderr)
    print(f"\nBy status:", file=sys.stderr)
    for k, v in sorted(by_status.items()):
        print(f"  {k}: {v}", file=sys.stderr)


if __name__ == "__main__":
    problems = build_problems()
    print_summary(problems)
    print(json.dumps(problems, indent=2))
