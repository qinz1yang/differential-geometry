import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineMetricEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.JointRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ} {Φ : PointedCGHMaps (I := I) X P subseq}

theorem HalfLineMetricConvergenceData.isSolutionOn_of_carrier_subset
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ}
    {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hreg : Iio 0 ⊆ X.D.regular) {D : RealTimeInterval}
    (hD : D.carrier ⊆ Iio 0) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    IsSolutionOn ({ base := { metric := co.gInf } } :
      SolutionOn (I := I) (M := P.M) D) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let D₀ : RealTimeInterval := RealTimeInterval.infiniteOpen 0 (-1) (by norm_num)
  have hS : IsSolutionOn ({ base := { metric := co.gInf } } :
      SolutionOn (I := I) (M := P.M) D₀) := by
    apply isSolutionOn_of_joint_metric D₀ (uniqueDiffOn_Iio 0) co.gInf
      (co.metricCLMSection_smooth (Φ := Φ) hreg)
    intro t ht x v w
    exact (co.metric_hasDerivAt Φ hreg ht x v w).hasDerivWithinAt
  exact isSolutionOn_timeRestrict hS hD (fun t ht => hD (D.regular_subset ht))

end DifferentialGeometry.CheegerGromovCompactness
