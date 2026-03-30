#!/usr/bin/env python3
"""Evaluate automated theorem provers on the MLStatBench benchmark.

For each problem, generates a Lean 4 file with the theorem statement
and a `sorry` proof, then invokes the specified prover to attempt
the proof. Records success/failure, time, and generated tactics.

Usage:
    python benchmark/evaluate.py --prover dummy         # dry run
    python benchmark/evaluate.py --prover ground_truth  # verify source builds
    python benchmark/evaluate.py --prover deepseek      # DeepSeek-Prover-V2 (needs httpx, DEEPSEEK_API_KEY)

Results are written to benchmark/results/<prover>_results.local.json
"""

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RESULTS_DIR = ROOT / "benchmark" / "results"
RESULTS_DIR.mkdir(exist_ok=True)

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

LEAN_VERIFY_TIMEOUT = 120   # seconds to wait for Lean to check a proof
SOURCE_BUILD_TIMEOUT = 120  # seconds to wait for a source module build
API_REQUEST_TIMEOUT = 60    # seconds to wait for an external prover API call

# ---------------------------------------------------------------------------
# Lean file generation
# ---------------------------------------------------------------------------

VERIFY_DIR = ROOT / "benchmark" / ".verify_tmp"
VERIFY_DIR.mkdir(exist_ok=True)


def make_lean_problem(problem: dict, tactic: str = "sorry") -> str:
    """Generate a Lean 4 file that states the theorem with a proof attempt."""
    module = problem["source_module"]
    imports = [f"import {module}"]
    # Use import_hints from curate_benchmark if available
    for hint in problem.get("import_hints", []):
        imp = f"import {hint}"
        if imp not in imports:
            imports.append(imp)
    header = "\n".join(imports)
    statement = problem["statement"]
    theorem_decl = statement.splitlines()[0]
    benchmark_decl = theorem_decl.replace(f" {problem['theorem_name']}", " benchmark_problem", 1)
    statement = "\n".join([benchmark_decl, *statement.splitlines()[1:]])
    context_prefix = "\n".join(problem.get("context_prefix", []))
    context_suffix = "\n".join(problem.get("context_suffix", []))

    return f"""{header}

open Finset BigOperators

noncomputable section

-- Problem: {problem['id']}
-- Source: {problem['source_file']}:{problem['source_line']}

{context_prefix}

{statement} := by
{tactic}

{context_suffix}
"""


def verify_lean_proof(problem: dict, tactic: str,
                      timeout_sec: int = LEAN_VERIFY_TIMEOUT) -> tuple[bool, str]:
    """Verify a tactic proof by writing a .lean file and running Lean.

    Returns (success: bool, error_message: str).
    """
    lean_code = make_lean_problem(problem, tactic=tactic)
    tmp_file = VERIFY_DIR / f"{problem['id']}.lean"
    tmp_file.write_text(lean_code)

    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(tmp_file)],
            capture_output=True, text=True,
            timeout=timeout_sec, cwd=str(ROOT),
        )
        # Reject sorry-based tactics so the dummy/fallback path cannot
        # count as a success even if Lean accepts the file.
        success = result.returncode == 0 and "sorry" not in tactic.lower()
        if not success:
            # Combine stdout + stderr and filter Lake noise so the real
            # Lean error is preserved instead of being masked by warnings
            # like "SLT: repository ... has local changes".
            combined = (result.stdout + "\n" + result.stderr).strip()
            lines = [
                line for line in combined.splitlines()
                if "has local changes" not in line
                and not line.startswith("warning: manifest out of date")
            ]
            error = "\n".join(lines)[-2000:]
        else:
            error = ""
        return success, error
    except subprocess.TimeoutExpired:
        return False, "verification timeout"
    finally:
        tmp_file.unlink(missing_ok=True)


# ---------------------------------------------------------------------------
# Prover backends
# ---------------------------------------------------------------------------

class DummyProver:
    """Baseline that always fails — used for testing the harness."""
    name = "dummy"

    def attempt(self, problem: dict, lean_code: str) -> dict:
        return {
            "success": False,
            "tactic": None,
            "time_seconds": 0.0,
            "error": "dummy prover always fails",
        }


class LeanCheckProver:
    """Check if the extracted benchmark problem is self-contained.

    This first verifies the extracted benchmark file by proving it with
    `simpa using <qualified theorem name>`, then rebuilds the source
    module as a sanity check. A malformed extraction should now fail.
    """
    name = "ground_truth"

    @staticmethod
    def _filter_names(names: list[str]) -> list[str]:
        """Keep only valid Lean identifier names, deduplicated."""
        result = []
        for name in names:
            base = name.rstrip("'")
            if (
                base
                and not base[0].isdigit()
                and "." not in base
                and not any(ch in " (){}[],:;→" for ch in base)
            ):
                result.append(name)
        return list(dict.fromkeys(result))

    def attempt(self, problem: dict, lean_code: str) -> dict:
        module = problem["source_module"]
        theorem_ref = problem.get("qualified_name") or problem["theorem_name"]

        # Split metadata: namespace receivers vs theorem's own binders.
        receiver_args = self._filter_names(problem.get("receiver_args", []))
        thm_binders = self._filter_names(problem.get("theorem_binders", []))

        # Backward compat: fall back to proof_arg_names if new fields missing.
        if not receiver_args and not thm_binders:
            thm_binders = self._filter_names(
                problem.get("proof_arg_names", []))

        start = time.time()
        try:
            build_result = subprocess.run(
                ["lake", "build", module],
                capture_output=True, text=True,
                timeout=SOURCE_BUILD_TIMEOUT, cwd=str(ROOT),
            )
            if build_result.returncode != 0:
                elapsed = time.time() - start
                build_error = (build_result.stdout + build_result.stderr)[:1000]
                return {
                    "success": False,
                    "tactic": None,
                    "time_seconds": elapsed,
                    "error": f"source module failed to build: {build_error}",
                }

            # Build tactic ladder, ordered by specificity.
            # Priority 1: receiver + binder args (most explicit).
            # Priority 2: receiver args only (namespace-receiver theorems).
            # Priority 3: binder args only (legacy path).
            # Priority 4: bare application (let Lean unify everything).
            tactics: list[str] = []

            if receiver_args and thm_binders:
                all_named = " ".join(
                    f"({n} := {n})" for n in receiver_args + thm_binders)
                tactics.append(f"  simpa using ({theorem_ref} {all_named})")
                tactics.append(f"  exact ({theorem_ref} {all_named})")

            if receiver_args:
                recv_named = " ".join(
                    f"({n} := {n})" for n in receiver_args)
                tactics.append(f"  simpa using ({theorem_ref} {recv_named})")
                tactics.append(f"  exact ({theorem_ref} {recv_named})")

            if thm_binders:
                binder_named = " ".join(
                    f"({n} := {n})" for n in thm_binders)
                tactics.append(f"  simpa using ({theorem_ref} {binder_named})")
                tactics.append(f"  exact ({theorem_ref} {binder_named})")

            tactics.append(f"  simpa using {theorem_ref}")
            tactics.append(f"  exact {theorem_ref}")

            seen_tactics: set[str] = set()
            last_error = ""
            attempted_tactic: str | None = None
            for proof_tactic in tactics:
                if proof_tactic in seen_tactics:
                    continue
                seen_tactics.add(proof_tactic)
                attempted_tactic = proof_tactic
                verified, verify_error = verify_lean_proof(
                    problem, proof_tactic, timeout_sec=LEAN_VERIFY_TIMEOUT)
                if verified:
                    elapsed = time.time() - start
                    return {
                        "success": True,
                        "tactic": proof_tactic.strip(),
                        "time_seconds": elapsed,
                        "error": None,
                    }
                last_error = verify_error

            elapsed = time.time() - start
            return {
                "success": False,
                "tactic": attempted_tactic.strip() if attempted_tactic else None,
                "time_seconds": elapsed,
                "error": f"extracted problem failed: {last_error}",
            }
        except subprocess.TimeoutExpired:
            return {
                "success": False,
                "tactic": None,
                "time_seconds": float(SOURCE_BUILD_TIMEOUT),
                "error": "timeout",
            }


class DeepSeekProver:
    """Interface to DeepSeek-Prover-V2 API.

    Requires DEEPSEEK_API_KEY environment variable.
    Falls back to dry-run mode if not set.
    """
    name = "deepseek_prover_v2"

    def __init__(self):
        self.api_key = os.environ.get("DEEPSEEK_API_KEY", "")
        if not self.api_key:
            print("WARNING: DEEPSEEK_API_KEY not set, using dry-run mode",
                  file=sys.stderr)

    def attempt(self, problem: dict, lean_code: str) -> dict:
        if not self.api_key:
            return {
                "success": False,
                "tactic": None,
                "time_seconds": 0.0,
                "error": "DEEPSEEK_API_KEY not set",
            }

        # Build the prompt for DeepSeek-Prover-V2
        prompt = self._build_prompt(problem, lean_code)

        start = time.time()
        try:
            import httpx
            response = httpx.post(
                "https://api.deepseek.com/chat/completions",
                headers={
                    "Authorization": f"Bearer {self.api_key}",
                    "Content-Type": "application/json",
                },
                json={
                    "model": "deepseek-prover-v2-671b",
                    "messages": [
                        {"role": "system", "content": (
                            "You are a Lean 4 theorem prover. Given a theorem "
                            "statement, produce a correct tactic proof. Output "
                            "ONLY the tactic block (no markdown, no explanation)."
                        )},
                        {"role": "user", "content": prompt},
                    ],
                    "temperature": 0.0,
                    "max_tokens": 2048,
                },
                timeout=API_REQUEST_TIMEOUT,
            )
            elapsed = time.time() - start
            data = response.json()
            try:
                tactic = data["choices"][0]["message"]["content"].strip()
            except (KeyError, IndexError, TypeError):
                return {
                    "success": False,
                    "tactic": None,
                    "time_seconds": elapsed,
                    "error": f"unexpected API response structure: {str(data)[:500]}",
                }

            # Strip markdown code fences if present
            if tactic.startswith("```"):
                tactic = "\n".join(tactic.split("\n")[1:])
            if tactic.endswith("```"):
                tactic = "\n".join(tactic.split("\n")[:-1])
            tactic = tactic.strip()

            # Indent tactic block for Lean
            tactic_indented = "\n".join(
                "  " + line if line.strip() else ""
                for line in tactic.splitlines()
            )

            # Verify the proof by running Lean
            gen_time = elapsed
            verified, verify_error = verify_lean_proof(
                problem, tactic_indented, timeout_sec=LEAN_VERIFY_TIMEOUT)
            total_time = time.time() - start

            return {
                "success": verified,
                "tactic": tactic,
                "time_seconds": total_time,
                "generation_time": gen_time,
                "error": verify_error if not verified else None,
            }

        except Exception as e:
            # Sanitize to avoid leaking the API key in error logs.
            error_msg = str(e)
            if self.api_key and self.api_key in error_msg:
                error_msg = error_msg.replace(self.api_key, "<REDACTED>")
            return {
                "success": False,
                "tactic": None,
                "time_seconds": time.time() - start,
                "error": error_msg,
            }

    def _build_prompt(self, problem: dict, lean_code: str) -> str:
        desc = problem.get("informal_description", "")
        stmt = problem["statement"]
        return f"""Prove the following Lean 4 theorem.

{f'Description: {desc}' if desc else ''}

```lean4
{stmt} := by
  sorry  -- replace this with your proof
```

Provide ONLY the tactic proof (the part after `:= by`), no explanations."""


class _OpenAICompatibleProver:
    """Base class for provers that use an OpenAI-compatible chat API.

    Subclasses set ``name``, ``_api_key_env``, ``_api_url_env``,
    ``_default_url``, and ``_model``.
    """
    name: str = ""
    _api_key_env: str = ""
    _api_url_env: str = ""
    _default_url: str = ""
    _model: str = ""

    def __init__(self):
        self.api_key = os.environ.get(self._api_key_env, "")
        self.api_url = os.environ.get(self._api_url_env, self._default_url)
        if not self.api_key:
            print(f"WARNING: {self._api_key_env} not set, using dry-run mode",
                  file=sys.stderr)

    def attempt(self, problem: dict, lean_code: str) -> dict:
        if not self.api_key:
            return {
                "success": False,
                "tactic": None,
                "time_seconds": 0.0,
                "error": f"{self._api_key_env} not set",
            }

        prompt = self._build_prompt(problem, lean_code)
        start = time.time()
        try:
            import httpx
            response = httpx.post(
                self.api_url,
                headers={
                    "Authorization": f"Bearer {self.api_key}",
                    "Content-Type": "application/json",
                },
                json={
                    "model": self._model,
                    "messages": [
                        {"role": "system", "content": (
                            "You are a Lean 4 theorem prover. Given a theorem "
                            "statement, produce a correct tactic proof. Output "
                            "ONLY the tactic block (no markdown, no explanation)."
                        )},
                        {"role": "user", "content": prompt},
                    ],
                    "temperature": 0.0,
                    "max_tokens": 2048,
                },
                timeout=API_REQUEST_TIMEOUT,
            )
            elapsed = time.time() - start
            data = response.json()
            try:
                tactic = data["choices"][0]["message"]["content"].strip()
            except (KeyError, IndexError, TypeError):
                return {
                    "success": False,
                    "tactic": None,
                    "time_seconds": elapsed,
                    "error": f"unexpected API response structure: {str(data)[:500]}",
                }

            # Strip markdown code fences if present
            if tactic.startswith("```"):
                tactic = "\n".join(tactic.split("\n")[1:])
            if tactic.endswith("```"):
                tactic = "\n".join(tactic.split("\n")[:-1])
            tactic = tactic.strip()

            # Indent tactic block for Lean
            tactic_indented = "\n".join(
                "  " + line if line.strip() else ""
                for line in tactic.splitlines()
            )

            # Verify the proof by running Lean
            gen_time = elapsed
            verified, verify_error = verify_lean_proof(
                problem, tactic_indented, timeout_sec=LEAN_VERIFY_TIMEOUT)
            total_time = time.time() - start

            return {
                "success": verified,
                "tactic": tactic,
                "time_seconds": total_time,
                "generation_time": gen_time,
                "error": verify_error if not verified else None,
            }

        except Exception as e:
            error_msg = str(e)
            if self.api_key and self.api_key in error_msg:
                error_msg = error_msg.replace(self.api_key, "<REDACTED>")
            return {
                "success": False,
                "tactic": None,
                "time_seconds": time.time() - start,
                "error": error_msg,
            }

    def _build_prompt(self, problem: dict, lean_code: str) -> str:
        desc = problem.get("informal_description", "")
        stmt = problem["statement"]
        return f"""Prove the following Lean 4 theorem.

{f'Description: {desc}' if desc else ''}

```lean4
{stmt} := by
  sorry  -- replace this with your proof
```

Provide ONLY the tactic proof (the part after `:= by`), no explanations."""


class DeepSeekV2Prover(_OpenAICompatibleProver):
    """Updated DeepSeek-Prover-V2 with model name deepseek-prover-v2-671b.

    Uses the same API as the original DeepSeekProver but with an explicit
    model identifier for the V2-671B variant.

    Requires DEEPSEEK_API_KEY environment variable.
    """
    name = "deepseek_prover_v2"
    _api_key_env = "DEEPSEEK_API_KEY"
    _api_url_env = "DEEPSEEK_API_URL"
    _default_url = "https://api.deepseek.com/chat/completions"
    _model = "deepseek-prover-v2-671b"


class KiminaProver(_OpenAICompatibleProver):
    """Interface to Kimina-Prover via OpenAI-compatible endpoint.

    Kimina-Prover is a formal-mathematics LLM specializing in Lean 4 proofs.

    Requires KIMINA_API_KEY and optionally KIMINA_API_URL environment variables.
    """
    name = "kimina"
    _api_key_env = "KIMINA_API_KEY"
    _api_url_env = "KIMINA_API_URL"
    _default_url = "https://api.kimina.ai/v1/chat/completions"
    _model = "kimina-prover-preview"


class GoedelProver(_OpenAICompatibleProver):
    """Interface to Goedel-Prover-V2 via OpenAI-compatible endpoint.

    Goedel-Prover-V2 is trained on large-scale formal math corpora and
    excels at structured mathematical reasoning.

    Requires GOEDEL_API_KEY and optionally GOEDEL_API_URL environment variables.
    """
    name = "goedel"
    _api_key_env = "GOEDEL_API_KEY"
    _api_url_env = "GOEDEL_API_URL"
    _default_url = "https://api.goedel-prover.org/v1/chat/completions"
    _model = "goedel-prover-v2"


class LeanstralProver(_OpenAICompatibleProver):
    """Interface to Mistral's Leanstral model.

    Leanstral is Mistral's fine-tuned model for Lean 4 theorem proving.

    Requires LEANSTRAL_API_KEY and optionally LEANSTRAL_API_URL environment variables.
    """
    name = "leanstral"
    _api_key_env = "LEANSTRAL_API_KEY"
    _api_url_env = "LEANSTRAL_API_URL"
    _default_url = "https://api.mistral.ai/v1/chat/completions"
    _model = "leanstral-v1"


PROVERS = {
    "dummy": DummyProver,
    "ground_truth": LeanCheckProver,
    "deepseek": DeepSeekProver,
    "deepseek_v2": DeepSeekV2Prover,
    "kimina": KiminaProver,
    "goedel": GoedelProver,
    "leanstral": LeanstralProver,
}


# ---------------------------------------------------------------------------
# Evaluation loop
# ---------------------------------------------------------------------------

def evaluate(benchmark_path: Path, prover_name: str,
             limit: int | None = None) -> list[dict]:
    try:
        benchmark = json.loads(benchmark_path.read_text())
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"Failed to load benchmark {benchmark_path}: {e}", file=sys.stderr)
        sys.exit(1)
    problems = benchmark["problems"]
    if limit:
        problems = problems[:limit]

    prover_cls = PROVERS.get(prover_name)
    if not prover_cls:
        print(f"Unknown prover: {prover_name}. Available: {list(PROVERS.keys())}",
              file=sys.stderr)
        sys.exit(1)

    prover = prover_cls()
    results = []

    print(f"Evaluating {len(problems)} problems with {prover.name}...",
          file=sys.stderr)

    for i, problem in enumerate(problems):
        lean_code = make_lean_problem(problem)

        result = prover.attempt(problem, lean_code)
        result["problem_id"] = problem["id"]
        result["theorem_name"] = problem["theorem_name"]
        result["domain"] = problem["domain"]
        result["difficulty"] = problem["difficulty"]
        result["source"] = problem["source"]
        results.append(result)

        status = "OK" if result["success"] else "FAIL"
        if i % 20 == 0 or i == len(problems) - 1:
            print(f"  [{i+1}/{len(problems)}] {problem['id']}: {status}",
                  file=sys.stderr)

    return results


def summarize(results: list[dict]) -> dict:
    """Compute summary statistics."""
    total = len(results)
    successes = sum(1 for r in results if r["success"])
    failures = sum(1 for r in results if r["success"] is False)
    unknown = sum(1 for r in results if r["success"] is None)

    by_domain = {}
    by_difficulty = {}
    for r in results:
        d = r["domain"]
        diff = r["difficulty"]
        by_domain.setdefault(d, {"total": 0, "success": 0})
        by_domain[d]["total"] += 1
        if r["success"]:
            by_domain[d]["success"] += 1

        by_difficulty.setdefault(diff, {"total": 0, "success": 0})
        by_difficulty[diff]["total"] += 1
        if r["success"]:
            by_difficulty[diff]["success"] += 1

    times = [r["time_seconds"] for r in results if r["time_seconds"] > 0]

    return {
        "total": total,
        "successes": successes,
        "failures": failures,
        "unknown": unknown,
        "success_rate": successes / total if total > 0 else 0,
        "by_domain": {
            k: {**v, "rate": v["success"] / v["total"] if v["total"] > 0 else 0}
            for k, v in sorted(by_domain.items())
        },
        "by_difficulty": {
            k: {**v, "rate": v["success"] / v["total"] if v["total"] > 0 else 0}
            for k, v in sorted(by_difficulty.items())
        },
        "time_stats": {
            "mean": sum(times) / len(times) if times else 0,
            "max": max(times) if times else 0,
        } if times else {},
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="MLStatBench evaluator")
    parser.add_argument("--prover", default="dummy",
                        choices=list(PROVERS.keys()),
                        help="Prover to evaluate")
    parser.add_argument("--limit", type=int, default=None,
                        help="Limit number of problems")
    parser.add_argument("--benchmark", default="benchmark/mlstatbench.json",
                        help="Path to benchmark JSON")
    parser.add_argument("--output", default=None,
                        help="Output path for results JSON (default: benchmark/results/<prover>_results.local.json)")
    args = parser.parse_args()

    benchmark_path = ROOT / args.benchmark
    results = evaluate(benchmark_path, args.prover, args.limit)
    summary = summarize(results)

    output = {
        "prover": args.prover,
        "benchmark": str(benchmark_path),
        "summary": summary,
        "results": results,
    }

    out_path = Path(args.output) if args.output else RESULTS_DIR / f"{args.prover}_results.local.json"
    out_path.write_text(json.dumps(output, indent=2))
    print(f"\nResults written to {out_path}", file=sys.stderr)

    # Print summary
    print(f"\n=== {args.prover} Results ===", file=sys.stderr)
    print(f"Success rate: {summary['successes']}/{summary['total']} "
          f"({summary['success_rate']:.1%})", file=sys.stderr)
    print(f"\nBy domain:", file=sys.stderr)
    for domain, stats in summary["by_domain"].items():
        print(f"  {domain}: {stats['success']}/{stats['total']} "
              f"({stats['rate']:.1%})", file=sys.stderr)
    print(f"\nBy difficulty:", file=sys.stderr)
    for diff, stats in summary["by_difficulty"].items():
        print(f"  {diff}: {stats['success']}/{stats['total']} "
              f"({stats['rate']:.1%})", file=sys.stderr)
