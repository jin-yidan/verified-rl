# Project Standard

## Project Goal

The goal of this repository is not merely to accumulate Lean files about
reinforcement learning.

The goal is to build a trustworthy formalization benchmark for RL theory that
is useful for:

- reusable mathematical infrastructure,
- honest theorem verification,
- training and evaluating proof-auditing agents,
- exposing gaps between paper claims and fully checked formal statements.

This leads to a deliberate split:

- `RLGeneralization`
  The trusted benchmark root.
- `RLGeneralization.Draft`
  Frontier modules that are useful research scaffolding but are not yet part of
  the trusted benchmark corpus.

## Formalization Standard

A result counts as genuinely formalized in this repository only if all of the
following hold:

1. The Lean statement matches the intended mathematical claim closely enough
   that a skeptical reviewer would accept it as the same theorem, or as an
   explicitly weaker theorem.
2. The proof is kernel-checked with no `sorry`.
3. The key mathematical content is actually derived in Lean, not hidden inside
   a hypothesis that effectively restates the conclusion.
4. The theorem is not made artificially true by a trivial existential witness,
   a vacuous conclusion, or a placeholder such as `True`.
5. Any remaining assumptions are explicit, mathematically meaningful, and
   documented as such.

## Status Vocabulary

Every important module or theorem should be classifiable as one of:

- `exact`
  Faithful match, or very close, to the intended theorem.
- `weaker`
  A real theorem, but weaker than the intended target claim.
- `conditional`
  The proof is checked, but the main analytical content is supplied as a
  hypothesis, structure field, or wrapper assumption.
- `wrapper`
  A near-tautological forwarding or repackaging theorem whose mathematical
  content is too small to count as substantive progress on its headline claim.
- `stub`
  Proof scaffolding that should not be counted as end-to-end formalization.
- `vacuous`
  Too weak to count as meaningful formalization.

## Trust Boundary

The trusted benchmark root must satisfy:

- `lake build --wfail` passes,
- imported modules are suitable benchmark data for proof-auditing agents,
- imported modules are not labeled `wrapper` in `verification_manifest.json`,
- imported modules do not contain placeholder-level theorem statements,
- repository-level claims do not overstate theorem strength.

The draft root may contain:

- conditional theorem wrappers,
- open proof obligations,
- infrastructure experiments,
- partially formalized frontier chapters.

Draft material is valuable, but it must not be presented as if it were part of
the trusted benchmark target.

## Practical Rules

1. Prefer one honest theorem over ten inflated chapter-coverage claims.
2. If a theorem is conditional, say so in the theorem name, docstring, manifest,
   or placement in the draft root.
3. If a file is mainly an interface to external assumptions, keep it out of the
   trusted benchmark unless that is the intended benchmark task.
4. If documentation and theorem strength disagree, fix the documentation or the
   import boundary immediately.
5. The repo should be useful for training agents to detect gaps, not to learn
   bad habits such as hypothesis forwarding under grand theorem names.

## Benchmark Use

When using this repository for agent training or evaluation:

- use `RLGeneralization` as trusted benchmark data,
- use `RLGeneralization.Draft` as labeled frontier/scaffolding data,
- use `verification_manifest.json` as the machine-readable source of theorem
  status,
- treat conditional and weaker theorems as supervision for theorem-auditing,
  not as end-to-end formal verification success.
