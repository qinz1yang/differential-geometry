import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineMetricEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Equations.VolumeDensity


noncomputable section

namespace DifferentialGeometry

open Bundle Set
open Geometry.Curvature Geometry.Connection Geometry.Operator Integral.Measure
open Tensor.Coordinates
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]



namespace CheegerGromovCompactness.HalfLineMetricConvergenceData

variable {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ} (Φ : PointedCGHMaps X P subseq)

variable {R : letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    SmoothRiemannianMetric I P.M}
  {bf : BumpFamily Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
  (co : HalfLineMetricConvergenceData Φ R bf hsrc htgt)

theorem contDiffOn_chartDensity
    (hreg : Iio 0 ⊆ X.D.regular) (α : P.M) {x : P.M}
    (hx : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    ContDiffOn ℝ ∞ (fun s => chartDensity (I := I) (co.gInf s) α x) (Iio 0) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  have hc := chartDensity_family_contMDiffOn co.gInf α (gramSmooth Φ co hreg α)
  exact (hc.comp (contMDiffOn_id.prodMk contMDiffOn_const)
    (fun s hs => ⟨hs, hx⟩)).contDiffOn

theorem hasDerivAt_chartDensity
    (hreg : Iio 0 ⊆ X.D.regular)
    {t : ℝ} (ht : t < 0) (α : P.M) {x : P.M}
    (hx : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    HasDerivAt (fun s => chartDensity (I := I) (co.gInf s) α x)
      (-metricScalarAt (co.gInf t) x * chartDensity (co.gInf t) α x) t := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  have hd := Integral.Measure.hasDerivAt_chartDensity_of_chartGram_contMDiffOn
    isOpen_Iio (gramSmooth Φ co hreg) ht α hx
  have htrace := PDE.RicciFlow.traceTimeDerivMetric_eq_neg_two_scalar_of_ricciFlow
    co.gInf (metric_hasDerivAt Φ co hreg ht) x
  rw [htrace] at hd
  exact hd.congr_deriv (by ring)

theorem hasDerivAt_chartDensity_time_sub
    (hreg : Iio 0 ⊆ X.D.regular)
    {a t : ℝ} (ht : a < t) (α : P.M) {x : P.M}
    (hx : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    HasDerivAt (fun s => chartDensity (I := I) (co.gInf (a - s)) α x)
      (metricScalarAt (co.gInf (a - t)) x * chartDensity (co.gInf (a - t)) α x) t := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  have hd := (hasDerivAt_chartDensity Φ co hreg (sub_neg.mpr ht) α hx).comp t
    ((hasDerivAt_const t a).sub (hasDerivAt_id t))
  exact hd.congr_deriv (by ring)

end CheegerGromovCompactness.HalfLineMetricConvergenceData

end DifferentialGeometry
