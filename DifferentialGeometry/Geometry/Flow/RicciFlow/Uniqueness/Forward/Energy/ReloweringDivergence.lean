import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Algebra.TensorDecomposition
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.ReloweringDivergence

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]
variable {Idx : Type*} [Fintype Idx]

theorem sdecRem_eq_sub_divergence
    (g₁ g₂ : SmoothRiemannianMetric I M) {x : M}
    (P : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 4)
    (b : Module.Basis Idx ℝ (TangentSpace I x))
    (R₀ : Idx → Idx → Idx → Idx → ℝ)
    (Rm2dot : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x) :
    sdecRem (I := I) g₁ g₂ P b R₀ Rm2dot =
      lowOfComp (I := I) g₁ b R₀ + gapDot (I := I) g₁ g₂ Rm2dot -
        covDiv0SField (I := I) g₁
          (reLower (I := I) g₂ g₁ (metricNabla0S (I := I) g₁ P) -
            metricNabla0S (I := I) g₁ P) x := by
  have h := congrArg (fun F => F x)
    (covariant_divergence_relowering_defect (I := I) g₁ g₂ P)
  change covDiv0SField (I := I) g₁
      (reLower (I := I) g₂ g₁ (metricNabla0S (I := I) g₁ P) -
        metricNabla0S (I := I) g₁ P) x =
    (reLower (I := I) g₂ g₁ (roughLap0SField (I := I) g₁ P) -
      roughLap0SField (I := I) g₁ P) x +
    metricTraceFirstTwoField (I := I) g₁
      (reLowerPair (I := I) g₁ (metricNabla0S (I := I) g₁ P)
        (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂))) x at h
  rw [sdecRem, h]
  abel

theorem covDiv_sdecFlux_add_sdecRem_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) {x : M}
    (Tf₂ P : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 4)
    (b : Module.Basis Idx ℝ (TangentSpace I x))
    (R₀ : Idx → Idx → Idx → Idx → ℝ)
    (Rm2dot : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x) :
    covDiv0SField (I := I) g₁ (sdecFlux (I := I) g₁ g₂ Tf₂ P) x +
        sdecRem (I := I) g₁ g₂ P b R₀ Rm2dot =
      covDiv0SField (I := I) g₁
        (sdecFlux (I := I) g₁ g₂ Tf₂ P -
          (reLower (I := I) g₂ g₁ (metricNabla0S (I := I) g₁ P) -
            metricNabla0S (I := I) g₁ P)) x +
        lowOfComp (I := I) g₁ b R₀ + gapDot (I := I) g₁ g₂ Rm2dot := by
  simp only [sdecRem_eq_sub_divergence, covDiv0SField_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply]
  abel

end DifferentialGeometry.PDE.RicciFlow
