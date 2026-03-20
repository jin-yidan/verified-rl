/-
Copyright (c) 2026 Yidan Jin. All rights reserved.
This source code is proprietary and not licensed for public use.

# Natural Policy Gradient

Abstract infrastructure for natural policy gradient updates.

## Main Definitions

* `NPGUpdate` - The NPG update rule: θ_{t+1} = θ_t + η · F⁻¹ · ∇J
* `npgStep` - The induced parameter update map

## Main Results

* `npg_eta_nonneg` - Step size is nonneg

## References

* [Agarwal et al., *RL: Theory and Algorithms*]
* [Kakade, 2001, Natural Policy Gradient]
-/

import RLGeneralization.PolicyOptimization.PolicyGradient

open Finset BigOperators

noncomputable section

namespace FiniteMDP

variable (M : FiniteMDP)

/-! ### Natural Policy Gradient Update -/

/-- The natural policy gradient update structure.

  The NPG update is:
    θ_{t+1} = θ_t + η · F(θ_t)⁻¹ · ∇J(θ_t)

  where F(θ) is the Fisher information matrix. The key insight
  is that F⁻¹∇J is the steepest ascent direction in the space
  of distributions (rather than parameters), making NPG
  invariant to reparameterization.

  We represent the update abstractly: given the current gradient
  and the "natural gradient" (F⁻¹∇J), the update adds a step. -/
structure NPGUpdate (d : ℕ) where
  /-- Step size η > 0 -/
  η : ℝ
  /-- Step size is positive -/
  η_pos : 0 < η
  /-- The natural gradient direction: F(θ)⁻¹ · ∇J(θ) -/
  naturalGrad : (Fin d → ℝ) → (Fin d → ℝ)

/-- The NPG parameter update: `θ_{t+1} = θ_t + η · F⁻¹∇J(θ_t)`. -/
def npgStep {d : ℕ} (upd : NPGUpdate d)
    (θ : Fin d → ℝ) : Fin d → ℝ :=
  fun i => θ i + upd.η * upd.naturalGrad θ i

/-- The step size η is nonneg. -/
theorem npg_eta_nonneg {d : ℕ} (upd : NPGUpdate d) :
    0 ≤ upd.η := le_of_lt upd.η_pos

/-! ### Fisher Information Matrix for Softmax

  For softmax π_θ(a|s) = exp(⟨θ,φ(s,a)⟩)/Z, the Fisher information
  at state s is:
    F_s(i,j) = ∑_a π(a|s) · (φ_i(s,a) − μ_i) · (φ_j(s,a) − μ_j)
  where μ_i = E_π[φ_i(s,·)] = ∑_a π(a|s) · φ_i(s,a).

  This is the covariance matrix of the features under π, and it is
  always positive semidefinite (as a sum of weighted outer products). -/

/-- The expected feature vector under softmax at state s. -/
def softmaxMeanFeature {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) (θ : Fin d → ℝ) (s : M.S) (i : Fin d) : ℝ :=
  ∑ a, M.softmaxProb φ θ s a * φ s a i

/-- The centered feature: φ(s,a) − E_π[φ(s,·)]. -/
def softmaxCenteredFeature {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) (θ : Fin d → ℝ) (s : M.S) (a : M.A) (i : Fin d) : ℝ :=
  φ s a i - M.softmaxMeanFeature φ θ s i

/-- The Fisher information matrix at state s for softmax policy.
    F_s(i,j) = E_π[(φ_i − μ_i)(φ_j − μ_j)] = Cov_π(φ_i, φ_j). -/
def softmaxFisher {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) (θ : Fin d → ℝ) (s : M.S)
    (i j : Fin d) : ℝ :=
  ∑ a, M.softmaxProb φ θ s a *
    M.softmaxCenteredFeature φ θ s a i *
    M.softmaxCenteredFeature φ θ s a j

/-- **The Fisher information matrix is positive semidefinite.**

  For any vector v ∈ ℝ^d:
    vᵀ F_s v = ∑_a π(a|s) · (⟨v, φ(s,a) − μ⟩)² ≥ 0

  This is a genuine matrix-analysis theorem about the softmax
  parameterization. It follows from the outer product structure:
  F_s = ∑_a π(a) · (φ̃(a))(φ̃(a))ᵀ where φ̃ = φ − μ.

  The PSD property ensures the Fisher metric is well-defined. -/
theorem softmaxFisher_posSemidef {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) (θ : Fin d → ℝ) (s : M.S)
    (v : Fin d → ℝ) :
    0 ≤ ∑ i : Fin d, ∑ j : Fin d,
      v i * M.softmaxFisher φ θ s i j * v j := by
  -- Rewrite as ∑_a π(a) · (∑_i v_i · (φ_i(a) − μ_i))²
  -- vᵀFv = ∑_a π(a) · (∑_i v_i · c_i(a))² ≥ 0
  -- Proof: expand F, distribute v, swap sums, factor as weighted sum of squares.
  -- vᵀFv = ∑_a π(a)(∑_i v_i c_i(a))² ≥ 0
  -- Step 1: Pull v into the sum over a, creating a triple sum
  have h_expand : ∀ (i j : Fin d),
      v i * softmaxFisher (M := M) φ θ s i j * v j =
      ∑ a, M.softmaxProb φ θ s a *
        (v i * M.softmaxCenteredFeature φ θ s a i) *
        (v j * M.softmaxCenteredFeature φ θ s a j) := by
    intro i j; simp only [softmaxFisher]
    rw [show v i * (∑ a, M.softmaxProb φ θ s a *
        M.softmaxCenteredFeature φ θ s a i *
        M.softmaxCenteredFeature φ θ s a j) * v j =
      ∑ a, v i * (M.softmaxProb φ θ s a *
        M.softmaxCenteredFeature φ θ s a i *
        M.softmaxCenteredFeature φ θ s a j) * v j from by
      rw [Finset.mul_sum]; simp_rw [Finset.sum_mul]]
    simp_rw [show ∀ a, v i * (M.softmaxProb φ θ s a *
        M.softmaxCenteredFeature φ θ s a i *
        M.softmaxCenteredFeature φ θ s a j) * v j =
      M.softmaxProb φ θ s a *
        (v i * M.softmaxCenteredFeature φ θ s a i) *
        (v j * M.softmaxCenteredFeature φ θ s a j) from fun a => by ring]
  simp_rw [h_expand]
  -- Goal: 0 ≤ ∑_i ∑_j ∑_a π · (v_i c_i) · (v_j c_j)
  -- Reorder to ∑_a ∑_i ∑_j, then factor as ∑_a π(∑_i v_i c_i)² ≥ 0
  calc (0 : ℝ)
      ≤ ∑ a, M.softmaxProb φ θ s a *
          (∑ i, v i * M.softmaxCenteredFeature φ θ s a i) ^ 2 :=
        Finset.sum_nonneg fun a _ =>
          mul_nonneg (M.softmaxProb_nonneg φ θ s a) (sq_nonneg _)
    _ = ∑ a, ∑ i : Fin d, ∑ j : Fin d,
          M.softmaxProb φ θ s a *
            (v i * M.softmaxCenteredFeature φ θ s a i) *
            (v j * M.softmaxCenteredFeature φ θ s a j) := by
        apply Finset.sum_congr rfl; intro a _
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring
    _ = ∑ i : Fin d, ∑ a, ∑ j : Fin d,
          M.softmaxProb φ θ s a *
            (v i * M.softmaxCenteredFeature φ θ s a i) *
            (v j * M.softmaxCenteredFeature φ θ s a j) :=
        Finset.sum_comm
    _ = ∑ i : Fin d, ∑ j : Fin d, ∑ a,
          M.softmaxProb φ θ s a *
            (v i * M.softmaxCenteredFeature φ θ s a i) *
            (v j * M.softmaxCenteredFeature φ θ s a j) := by
        apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm

/-- The centered features sum to zero under π:
    ∑_a π(a|s) · (φ_i(s,a) − μ_i) = 0. -/
theorem softmax_centered_feature_mean_zero {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) (θ : Fin d → ℝ) (s : M.S) (i : Fin d) :
    ∑ a, M.softmaxProb φ θ s a * M.softmaxCenteredFeature φ θ s a i = 0 := by
  simp only [softmaxCenteredFeature, softmaxMeanFeature]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [M.softmaxProb_sum_one φ θ s (M.softmax_denom_pos φ θ s), one_mul, sub_self]

/-- **Advantage-weighted centered features.**

  For any advantage function A with E_π[A(s,·)] = 0 (consistent advantage):
    ∑_a π(a|s) · A(s,a) · (φ_i(s,a) − μ_i) = ∑_a π(a|s) · A(s,a) · φ_i(s,a)

  This is because the μ_i term vanishes: ∑_a π A · μ_i = μ_i · ∑_a π A = μ_i · 0 = 0.

  This identity shows that the NPG direction (F⁻¹∇J) can be computed using
  raw features φ instead of centered features φ − μ, simplifying computation. -/
theorem advantage_weighted_feature_centering {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) (θ : Fin d → ℝ) (s : M.S)
    (A : M.A → ℝ)
    (h_zero_mean : ∑ a, M.softmaxProb φ θ s a * A a = 0)
    (i : Fin d) :
    ∑ a, M.softmaxProb φ θ s a * A a * M.softmaxCenteredFeature φ θ s a i =
    ∑ a, M.softmaxProb φ θ s a * A a * φ s a i := by
  simp only [softmaxCenteredFeature, softmaxMeanFeature]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [show ∑ a, M.softmaxProb φ θ s a * A a * (∑ a', M.softmaxProb φ θ s a' * φ s a' i) =
    (∑ a', M.softmaxProb φ θ s a' * φ s a' i) * ∑ a, M.softmaxProb φ θ s a * A a from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring]
  rw [h_zero_mean, mul_zero, sub_zero]

/-- **NPG update direction for softmax.**

  The advantage-weighted feature sum is the core of the NPG update.
  For consistent advantages (E_π[A] = 0), this gives the direction
  that the natural gradient computes:

    npgDir_i = ∑_a π(a|s) · A(s,a) · φ_i(s,a)

  Taking w_i = (1/(1-γ)) · ∑_s d^π(s) · npgDir_i(s) gives the
  full NPG update direction θ' = θ + η · w. -/
def npgDirectionAtState {d : ℕ}
    (φ : M.S → M.A → Fin d → ℝ) (θ : Fin d → ℝ) (s : M.S)
    (A : M.A → ℝ) (i : Fin d) : ℝ :=
  ∑ a, M.softmaxProb φ θ s a * A a * φ s a i


end FiniteMDP

end
