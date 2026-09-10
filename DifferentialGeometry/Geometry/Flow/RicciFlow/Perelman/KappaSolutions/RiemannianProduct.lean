import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Curvature

variable [CompleteSpace E]

private local instance upstreamRiemannianProductC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem metricRm04At_product_real_of_inner_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + a * c)
    (y : M) (s : ℝ) (v : Fin 4 → TangentSpace I y) (a : Fin 4 → ℝ) :
    metricRm04At (I := I.prod 𝓘(ℝ, ℝ)) gP (y, s) (fun i => (v i, a i)) =
      metricRm04At (I := I) h y v := by
  sorry

end Curvature

section Volume

variable [T2Space M] [SigmaCompactSpace M]

private local instance upstreamRiemannianProductMeasurable : MeasurableSpace M := borel M
private local instance upstreamRiemannianProductBorel : BorelSpace M := ⟨rfl⟩

theorem riemannianVolumeMeasure_product_real_of_inner_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + a * c) :
    riemannianVolumeMeasure (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) gP =
      cast
        (congrArg (fun m : MeasurableSpace (M × ℝ) => @Measure (M × ℝ) m)
          (BorelSpace.measurable_eq (α := M × ℝ)))
        ((riemannianVolumeMeasure (I := I) (M := M) h).prod
          (volume : Measure ℝ)) := by
  sorry

end Volume

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
