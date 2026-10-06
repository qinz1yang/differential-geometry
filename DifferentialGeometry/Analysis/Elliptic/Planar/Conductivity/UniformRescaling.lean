import DifferentialGeometry.Analysis.Elliptic.Coefficients
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.PositiveDefinite.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section

open Set Metric InnerProductSpace
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise NNReal

namespace DifferentialGeometry.Analysis

open DeGiorgi Laplacian.MetricExtension Parabolic.Euclidean

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℝ

/-- A single set of ellipticity, square-root distortion and oscillation constants
works for all small rescalings of the same `C¹` positive-definite conductivity.
The factor `ρ` in the oscillation bound is retained. No regularity or measurability
of the arbitrary field outside `Ω` is asserted. -/
theorem exists_uniform_rescaled_conductivity_bounds
    {Ω : Set E} (hΩ : IsOpen Ω) (h0 : (0 : E) ∈ Ω)
    (K : E → Mat)
    (hK : ∀ i j, ContDiffOn ℝ 1 (fun x => K x i j) Ω)
    (hpos : ∀ x ∈ Ω, (K x).PosDef)
    (hdet : ∀ x ∈ Ω, (K x).det = 1) :
    ∃ (ρ₀ lam Λ : ℝ) (L : ℝ≥0),
      0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ closedBall (0 : E) ρ₀ ⊆ Ω ∧
      0 < lam ∧ lam ≤ Λ ∧ 1 ≤ Λ ∧
      (∀ (ρ : ℝ), 0 < ρ → ρ ≤ ρ₀ → ∀ x ∈ closedBall (0 : E) 1,
        ρ • x ∈ Ω ∧ (K (ρ • x)).PosDef ∧ (K (ρ • x)).det = 1 ∧
        (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE (K (ρ • x)) ξ⟫_ℝ) ∧
        (∀ ξ : E, Λ⁻¹ * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE ((K (ρ • x))⁻¹) ξ⟫_ℝ) ∧
        ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (K (ρ • x))‖ ≤ Λ ∧
        (∀ hp : (K (ρ • x)).PosDef,
          ‖(spdSqrtEquiv (K (ρ • x)) hp : E →L[ℝ] E)‖ ≤ max 1 (Real.sqrt Λ) ∧
          ‖((spdSqrtEquiv (K (ρ • x)) hp).symm : E →L[ℝ] E)‖ ≤
            max 1 (Real.sqrt lam)⁻¹)) ∧
      (∀ (ρ : ℝ), 0 < ρ → ρ ≤ ρ₀ →
        ∀ x ∈ closedBall (0 : E) 1, ∀ y ∈ closedBall (0 : E) 1, ∀ ξ : E,
          ‖matMulE (K (ρ • x)) ξ - matMulE (K (ρ • y)) ξ‖ ≤
            ρ * (L : ℝ) * dist x y * ‖ξ‖) := by
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.mp hΩ 0 h0
  let ρ₀ : ℝ := min 1 (δ / 2)
  have hρ₀ : 0 < ρ₀ := lt_min zero_lt_one (half_pos hδ)
  have hρ₀1 : ρ₀ ≤ 1 := min_le_left _ _
  have hρ₀δ : ρ₀ < δ := (min_le_right 1 (δ / 2)).trans_lt (half_lt_self hδ)
  have hball : closedBall (0 : E) ρ₀ ⊆ Ω := by
    intro x hx
    apply hδΩ
    exact (Metric.mem_closedBall.mp hx).trans_lt hρ₀δ
  have hzero : (0 : E) ∈ closedBall (0 : E) ρ₀ := by
    simpa only [Metric.mem_closedBall, dist_self] using hρ₀.le
  have hmat : ContDiffOn ℝ 1 K Ω :=
    contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (hK i))
  let T : Mat ≃L[ℝ] (E →L[ℝ] E) :=
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv
  let F : E → E →L[ℝ] E := fun x => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (K x)
  have hFapply (x ξ : E) : F x ξ = matMulE (K x) ξ := by
    apply WithLp.ofLp_injective
    exact Matrix.ofLp_toEuclideanCLM (K x) ξ
  have hF : ContDiffOn ℝ 1 F Ω := by
    change ContDiffOn ℝ 1 (T ∘ K) Ω
    exact T.contDiff.comp_contDiffOn hmat
  obtain ⟨L, hL⟩ := (hF.mono hball).exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : E) ρ₀) (isCompact_closedBall (0 : E) ρ₀)
  obtain ⟨lam, μ, hlam, hμ, hcoer, hinv⟩ :=
    exists_uniform_matrix_and_inverse_quadratic_lower_bound
      (isCompact_closedBall (0 : E) ρ₀) K
      (fun i j => (hK i j).continuousOn.mono hball)
      (fun x hx => hpos x (hball hx))
  let C : ℝ := ‖F 0‖ + (L : ℝ) * ρ₀
  let Λ : ℝ := max 1 (max lam (max C μ⁻¹))
  have hΛ1 : 1 ≤ Λ := le_max_left _ _
  have hlamΛ : lam ≤ Λ := (le_max_left _ _).trans (le_max_right _ _)
  have hCΛ : C ≤ Λ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hμΛ : μ⁻¹ ≤ Λ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ1
  have hΛinv : Λ⁻¹ ≤ μ := by
    have hi := (inv_le_inv₀ hΛpos (inv_pos.mpr hμ)).2 hμΛ
    simpa only [inv_inv] using hi
  have hnorm : ∀ x ∈ closedBall (0 : E) ρ₀, ‖F x‖ ≤ Λ := by
    intro x hx
    have hd : ‖F x - F 0‖ ≤ (L : ℝ) * ρ₀ := by
      calc
        ‖F x - F 0‖ ≤ (L : ℝ) * dist x 0 := by
          simpa only [dist_eq_norm] using hL.dist_le_mul x hx 0 hzero
        _ ≤ (L : ℝ) * ρ₀ :=
          mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp hx) L.coe_nonneg
    calc
      ‖F x‖ ≤ ‖F x - F 0‖ + ‖F 0‖ := by
        simpa only [sub_add_cancel] using norm_add_le (F x - F 0) (F 0)
      _ ≤ (L : ℝ) * ρ₀ + ‖F 0‖ := by linarith only [hd]
      _ = C := add_comm _ _
      _ ≤ Λ := hCΛ
  have hscale : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ ρ₀ →
      ∀ x ∈ closedBall (0 : E) 1, ρ • x ∈ closedBall (0 : E) ρ₀ := by
    intro ρ hρ hρle x hx
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    exact (mul_le_mul_of_nonneg_left hxnorm hρ.le).trans (by simpa only [mul_one] using hρle)
  refine ⟨ρ₀, lam, Λ, L, hρ₀, hρ₀1, hball, hlam, hlamΛ, hΛ1, ?_, ?_⟩
  · intro ρ hρ hρle x hx
    have hxp := hscale ρ hρ hρle x hx
    have hxΩ := hball hxp
    refine ⟨hxΩ, hpos _ hxΩ, hdet _ hxΩ, hcoer _ hxp, ?_, hnorm _ hxp, ?_⟩
    · intro ξ
      exact (mul_le_mul_of_nonneg_right hΛinv (sq_nonneg ‖ξ‖)).trans (hinv _ hxp ξ)
    · intro hp
      have hlower : ∀ ξ : E,
          lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (K (ρ • x)) ξ⟫_ℝ := by
        intro ξ
        change lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, F (ρ • x) ξ⟫_ℝ
        rw [hFapply]
        exact hcoer _ hxp ξ
      have hupper : ∀ ξ : E,
          ⟪ξ, Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (K (ρ • x)) ξ⟫_ℝ ≤ Λ * ‖ξ‖ ^ 2 := by
        intro ξ
        calc
          ⟪ξ, F (ρ • x) ξ⟫_ℝ ≤ ‖ξ‖ * ‖F (ρ • x) ξ‖ := real_inner_le_norm _ _
          _ ≤ ‖ξ‖ * (‖F (ρ • x)‖ * ‖ξ‖) :=
            mul_le_mul_of_nonneg_left ((F (ρ • x)).le_opNorm ξ) (norm_nonneg _)
          _ ≤ ‖ξ‖ * (Λ * ‖ξ‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hnorm _ hxp) (norm_nonneg _)) (norm_nonneg _)
          _ = Λ * ‖ξ‖ ^ 2 := by ring
      exact ⟨(spdSqrt_norm_le _ hp hΛpos.le hupper).trans (le_max_right _ _),
        (spdSqrt_inv_le _ hp hlam hlower).trans (le_max_right _ _)⟩
  · intro ρ hρ hρle x hx y hy ξ
    have hdist := hL.dist_le_mul (ρ • x) (hscale ρ hρ hρle x hx)
      (ρ • y) (hscale ρ hρ hρle y hy)
    calc
      ‖matMulE (K (ρ • x)) ξ - matMulE (K (ρ • y)) ξ‖ =
          ‖(F (ρ • x) - F (ρ • y)) ξ‖ := by
        simp only [sub_apply, hFapply]
      _ ≤ ‖F (ρ • x) - F (ρ • y)‖ * ‖ξ‖ :=
        (F (ρ • x) - F (ρ • y)).le_opNorm ξ
      _ ≤ ((L : ℝ) * dist (ρ • x) (ρ • y)) * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right (by simpa only [dist_eq_norm] using hdist) (norm_nonneg _)
      _ = ρ * (L : ℝ) * dist x y * ‖ξ‖ := by
        rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hρ]
        ring

end DifferentialGeometry.Analysis
