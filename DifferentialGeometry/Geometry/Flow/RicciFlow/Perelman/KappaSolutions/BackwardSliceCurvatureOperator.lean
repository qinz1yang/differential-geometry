import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCurvatureOperator
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval}

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem backwardSliceLimit_curvatureOperator_nonnegative
    (F : PointedFlowData.{u, uE, uH} I D) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {L : PointedRiemannianManifold.{u, uE, uH} I} {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i) :
    ∀ x : L.M, metricAlgebraicCurvatureTensorAt L.metric x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  let _ : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 2 F.M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 3 F.M := IsManifold.of_le (n := ∞) (by decide)
  apply curvatureOperator_nonnegative_of_canonical_metricCGConvergence C hcanonical
  intro K _hK
  refine Eventually.of_forall fun i y _hy _hsource => ?_
  change metricAlgebraicCurvatureTensorAt
    (scaleMetric (tau (phi i))⁻¹ (inv_pos.mpr (htau (phi i)))
      (F.S.base.metric (-tau (phi i)))) (Phi.map i y) ∈ _
  rw [metricAlgebraicCurvatureTensorAt_scaleMetric]
  apply algebraicCurvatureOperatorNonnegativeCone.smul_mem _ (inv_pos.mpr (htau (phi i))).le
  apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
  intro n c v w
  have htime : -tau (phi i) ∈ D.carrier := by
    rw [hF.carrier_eq]
    exact neg_nonpos.mpr (htau (phi i)).le
  have hh := hF.nonnegativeCurvatureOperator _ htime (Phi.map i y) n c v w
  simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
    tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
