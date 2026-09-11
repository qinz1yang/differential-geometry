import DifferentialGeometry.Analysis.Integration.Measure.Pullback
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Canonical

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem canonicalMetric_volumeMeasure
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) :
    riemannianVolumeMeasure (I := I) (M := M)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht) =
      ENNReal.ofReal
          ((1 - sigma * t) ^ ((Module.finrank Real E : Real) / 2)) •
        Measure.map
          ((canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t)).symm : M → M)
          (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hpos : 0 < 1 - sigma * t := mem_canonicalTimeDomain_iff.mp ht
  have hpower : Real.sqrt (1 - sigma * t) ^ Module.finrank Real E =
      (1 - sigma * t) ^ ((Module.finrank Real E : Real) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hpos.le]
    congr 1
    ring
  rw [canonicalMetric, riemannianVolumeMeasure_pullback,
    volume_scaleMetric, Measure.map_smul]
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg (1 - sigma * t)), hpower]

theorem canonicalMetricFamily_volumeMeasure
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) :
    riemannianVolumeMeasure (I := I) (M := M)
        (canonicalMetricFamily (I := I) g f sigma hcomplete hsol t) =
      ENNReal.ofReal
          ((1 - sigma * t) ^ ((Module.finrank Real E : Real) / 2)) •
        Measure.map
          ((canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t)).symm : M → M)
          (riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [canonicalMetricFamily_eq (I := I) g f sigma hcomplete hsol ht]
  exact canonicalMetric_volumeMeasure (I := I) g f sigma hcomplete hsol ht

end DifferentialGeometry.PDE.RicciFlow.Soliton
