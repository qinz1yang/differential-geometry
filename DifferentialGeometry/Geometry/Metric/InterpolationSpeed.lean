import DifferentialGeometry.Geometry.Metric.InterpolationBounds
import DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus



noncomputable section

open Bundle Manifold Set DifferentialGeometry
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] [Nonempty M] [PreconnectedSpace M]

set_option backward.isDefEq.respectTransparency false in



theorem exists_interpolation_endpoint_speed_bound (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ ρ C : ℝ≥0, 0 < ρ ∧ 0 < C ∧ ∀ v ∈ Icc (0 : ℝ) 1,
      ∀ (γ₀ γ₁ : ℝ → M) (t : ℝ),
        riemannianEDistOf g (γ₀ t) (γ₁ t) ≤ (ρ : ℝ≥0∞) →
        MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ₀ t →
        MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ₁ t →
        riemannianCurveSpeed g (fun s => geodesicInterpolation g (γ₀ s) (γ₁ s) v) t ≤
          C * (riemannianCurveSpeed g γ₀ t + riemannianCurveSpeed g γ₁ t) := by
  obtain ⟨n, e, r, he, hleft, ρ, C, O, hρ, hO, hF, hC⟩ :=
    exists_geodesicInterpolation_ambient_bound g
  obtain ⟨Ce, hCe⟩ := exists_metric_mfderiv_bound g (he.of_le (by simp))
  let F := fun p : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
    geodesicInterpolation g (r p.2.1) (r p.2.2) p.1
  refine ⟨ρ, C * Ce + 1, hρ, by positivity, fun v hv γ₀ γ₁ t hdist h₀ h₁ => ?_⟩
  let B₀ : ℝ → EuclideanSpace ℝ (Fin n) := e ∘ γ₀
  let B₁ : ℝ → EuclideanSpace ℝ (Fin n) := e ∘ γ₁
  let P : ℝ → ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    fun s => (v, (B₀ s, B₁ s))
  have hB₀ : DifferentiableAt ℝ B₀ t :=
    ((he.mdifferentiableAt (by simp)).comp t h₀).differentiableAt
  have hB₁ : DifferentiableAt ℝ B₁ t :=
    ((he.mdifferentiableAt (by simp)).comp t h₁).differentiableAt
  have hP : DifferentiableAt ℝ P t := (differentiableAt_const v).prodMk (hB₀.prodMk hB₁)
  have hder : deriv P t = (0, (deriv B₀ t, deriv B₁ t)) :=
    (hasDerivAt_const t v |>.prodMk (hB₀.hasDerivAt.prodMk hB₁.hasDerivAt)).deriv
  have h₀der : deriv B₀ t =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e (γ₀ t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ₀ t 1) := by
    rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv,
      mfderiv_comp t (he.mdifferentiableAt (by simp)) h₀]
    rfl
  have h₁der : deriv B₁ t =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e (γ₁ t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ₁ t 1) := by
    rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv,
      mfderiv_comp t (he.mdifferentiableAt (by simp)) h₁]
    rfl
  have hb₀ : ‖deriv B₀ t‖ ≤ Ce * riemannianCurveSpeed g γ₀ t := by
    rw [h₀der]
    exact hCe _ _
  have hb₁ : ‖deriv B₁ t‖ ≤ Ce * riemannianCurveSpeed g γ₁ t := by
    rw [h₁der]
    exact hCe _ _
  have hnorm : ‖deriv P t‖ ≤ Ce * (riemannianCurveSpeed g γ₀ t + riemannianCurveSpeed g γ₁ t) := by
    rw [hder, Prod.norm_def, norm_zero, Prod.norm_def, max_eq_right (le_max_of_le_left (norm_nonneg _))]
    apply max_le
    · exact hb₀.trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (riemannianCurveSpeed_nonneg g γ₁ t)) Ce.coe_nonneg)
    · exact hb₁.trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (riemannianCurveSpeed_nonneg g γ₀ t)) Ce.coe_nonneg)
  obtain ⟨hpO, hbound⟩ := hC v hv (γ₀ t) (γ₁ t) hdist
  have hdf : MDifferentiableAt 𝓘(ℝ, ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, E) F (P t) :=
    ((hF _ hpO).contMDiffAt (hO.mem_nhds hpO)).mdifferentiableAt (by simp)
  have heq : F ∘ P = fun s => geodesicInterpolation g (γ₀ s) (γ₁ s) v := by
    funext s
    simp only [F, P, B₀, B₁, Function.comp_apply, hleft]
  rw [← heq, riemannianCurveSpeed_comp g hdf hP]
  calc
    _ ≤ C * ‖deriv P t‖ := hbound _
    _ ≤ C * (Ce * (riemannianCurveSpeed g γ₀ t + riemannianCurveSpeed g γ₁ t)) :=
      mul_le_mul_of_nonneg_left hnorm C.coe_nonneg
    _ ≤ (C * Ce + 1 : ℝ≥0) * (riemannianCurveSpeed g γ₀ t + riemannianCurveSpeed g γ₁ t) := by
      simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (add_nonneg (riemannianCurveSpeed_nonneg g γ₀ t) (riemannianCurveSpeed_nonneg g γ₁ t))

end DifferentialGeometry.Geometry
