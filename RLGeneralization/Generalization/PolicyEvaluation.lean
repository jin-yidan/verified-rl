/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Policy Evaluation with Linear Function Approximation (Stubs)

This file contains STUBS for LSTD finite-sample bounds in the
discounted infinite-horizon setting. These are NOT proved and
NOT imported into the trusted benchmark root.

## Status: PARTIAL

The theorems here require:
1. Matrix inverse for LSTD solution (Â⁻¹b̂)
2. SLT library integration for regression rates
   (lean-stat-learning-theory now uses Lean 4.28.0 / Mathlib v4.28.0,
    matching our toolchain -- the earlier version mismatch is resolved)
3. Covering number infrastructure from SLT

The LSTD finite-sample bound itself is not yet formalized: it would
require constructing a `LeastSquares.RegressionModel` from per-stage
data and applying `LeastSquares.linear_minimax_rate`.

For the finite-horizon analogue, see `LinearFeatures/LSVI.lean`
which proves the approximate dynamic-programming error bound without sorry.

For the regression bridge (hypothesis-based), see
`LinearFeatures/RegressionBridge.lean`.
-/

import RLGeneralization.MDP.BellmanContraction
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-- Linear function approximation setup. -/
structure LinearApprox (d : ℕ) where
  φ : M.S → Fin d → ℝ
  φ_bound : ∃ B : ℝ, 0 < B ∧ ∀ s i, |φ s i| ≤ B

/-- LSTD data: (s, r, s') triples. -/
structure LSTDData (n : ℕ) where
  states : Fin n → M.S
  rewards : Fin n → ℝ
  next_states : Fin n → M.S

/-- The empirical LSTD matrix Â:
    Â_ij = (1/n) ∑_k φ(s_k)_i · (φ(s_k)_j - γ·φ(s'_k)_j) -/
def lstdMatrix {d n : ℕ} (approx : M.LinearApprox d)
    (data : M.LSTDData n) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (∑ k : Fin n,
    approx.φ (data.states k) i *
    (approx.φ (data.states k) j -
      M.γ * approx.φ (data.next_states k) j)) / n

/-- The empirical LSTD vector b̂:
    b̂_i = (1/n) ∑_k φ(s_k)_i · r_k -/
def lstdVector {d n : ℕ} (approx : M.LinearApprox d)
    (data : M.LSTDData n) : Fin d → ℝ :=
  fun i => (∑ k : Fin n,
    approx.φ (data.states k) i * data.rewards k) / n

/-- LSTD solution: θ̂ = Â⁻¹ b̂ using Mathlib's matrix inverse. -/
def lstdSolution {d n : ℕ}
    (approx : M.LinearApprox d) (data : M.LSTDData n) :
    Fin d → ℝ :=
  (M.lstdMatrix approx data)⁻¹.mulVec (M.lstdVector approx data)

-- LSTD finite-sample bound: NOT FORMALIZED.
-- The target statement ‖V̂-V^π‖² ≤ C·σ²·d/n requires
-- constructing a `LeastSquares.RegressionModel` from per-stage
-- data and applying `LeastSquares.linear_minimax_rate` from the
-- SLT library (now version-compatible: both use Lean 4.28.0).
-- The remaining gap is measure-theoretic plumbing, not a version
-- mismatch.

end FiniteMDP

end
