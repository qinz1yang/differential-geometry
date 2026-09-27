import DifferentialGeometry.Geometry.Metric.Conformal.VectorField
import DifferentialGeometry.Geometry.Metric.LieDerivative.Naturality

noncomputable section

namespace DifferentialGeometry.Geometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

theorem isConformalVectorField_pullbackMetric_iff
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    IsConformalVectorField (Diffeomorph.pullbackMetric g Φ) X ↔
      IsConformalVectorField g
        ⟨Diffeomorph.pushforward Φ X,
          Diffeomorph.pushforward_contMDiff Φ X.contMDiff⟩ := by
  rw [isConformalVectorField_iff_lieDerivMetric,
    isConformalVectorField_iff_lieDerivMetric]
  have hnatural (x : M) (v w : TangentSpace I x) :=
    PDE.RicciFlow.Pullback.lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise
      g Φ X X.contMDiff (Diffeomorph.pushforward_contMDiff Φ X.contMDiff) x v w
  have hXeq : (⟨X, X.contMDiff⟩ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) = X := by
    ext x
    rfl
  simp only [hXeq] at hnatural
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ ∘ Φ.symm, ?_⟩
    intro y v w
    obtain ⟨x, rfl⟩ := Φ.surjective y
    obtain ⟨v, rfl⟩ := (Φ.mfderivToContinuousLinearEquiv (by simp) x).surjective v
    obtain ⟨w, rfl⟩ := (Φ.mfderivToContinuousLinearEquiv (by simp) x).surjective w
    change PDE.DeTurck.lieDerivMetric g
      ⟨Diffeomorph.pushforward Φ X, Diffeomorph.pushforward_contMDiff Φ X.contMDiff⟩
      (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) = _
    rw [← hnatural, hφ, Diffeomorph.pullbackMetric_inner]
    change φ x * g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) =
      φ (Φ.symm (Φ x)) * g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w)
    rw [Φ.symm_apply_apply]
  · rintro ⟨φ, hφ⟩
    refine ⟨φ ∘ Φ, fun x v w => ?_⟩
    rw [hnatural, hφ, Diffeomorph.pullbackMetric_inner]
    rfl

end DifferentialGeometry.Geometry
