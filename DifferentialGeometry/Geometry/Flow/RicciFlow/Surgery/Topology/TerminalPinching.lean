import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalTimeExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CurvatureOperator

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.curvatureOperatorLowerBoundAt_of_phiAlmostNonnegative
    (L : G.TerminalLimitMetric) {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
    (hpinch : Perelman.PhiAlmostNonnegative G.flow (Ico a s) Phi)
    (x : G.terminalRegularOpen) :
    curvatureOperatorLowerBoundAt L.metric x (metricAlgebraicCurvatureTensorAt L.metric x)
      (Phi (metricScalarAt L.metric x)) := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt L.metric x (by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace])
  apply (curvatureOperatorLowerBoundAt_iff_neg_leastCurvatureOperatorEigenvalueAt_le
    basis horth).mpr
  apply le_of_tendsto_of_tendsto
    ((L.tendsto_leastCurvatureOperatorEigenvalueAt x).neg)
    ((hPhi.tendsto _).comp (L.tendsto_metricScalarAt x))
  have hp := (Perelman.phiAlmostNonnegative_iff_neg_le_leastCurvatureOperatorEigenvalueAt
    G.flow (Ico a s) Phi (by simp [ThreeSpace])).mp hpinch
  filter_upwards [Ioo_mem_nhdsLT G.lt] with t ht
  have htP := hp t ⟨ht.1.le, ht.2⟩ x.val
  change -Phi (metricScalarAt (G.flow.base.metric t) x.val) ≤
    leastCurvatureOperatorEigenvalueAt (G.flow.base.metric t) x.val
      (metricAlgebraicCurvatureTensorAt (G.flow.base.metric t) x.val) at htP
  change -leastCurvatureOperatorEigenvalueAt (G.flow.base.metric t) x.val
    (metricAlgebraicCurvatureTensorAt (G.flow.base.metric t) x.val) ≤
      Phi (metricScalarAt (G.flow.base.metric t) x.val)
  linarith

theorem TerminalLimitMetric.extendedMetric_curvatureOperatorLowerBoundAt_of_phiAlmostNonnegative
    (L : G.TerminalLimitMetric) {Phi : ℝ → ℝ} (hPhi : Continuous Phi)
    (hpinch : Perelman.PhiAlmostNonnegative G.flow (Ico a s) Phi)
    {t : ℝ} (ht : t ∈ Icc a s) (x : G.terminalRegularOpen) :
    curvatureOperatorLowerBoundAt (L.extendedMetric t) x
      (metricAlgebraicCurvatureTensorAt (L.extendedMetric t) x)
      (Phi (metricScalarAt (L.extendedMetric t) x)) := by
  rcases lt_or_eq_of_le ht.2 with hts | rfl
  · rw [L.extendedMetric_before hts, ← DifferentialGeometry.localPullMetric_subtype_val,
      metricScalarAt_localPull, curvatureOperatorLowerBoundAt_localPullMetric_iff]
    exact hpinch t ⟨ht.1, hts⟩ x.val
  · rw [L.extendedMetric_terminal]
    exact L.curvatureOperatorLowerBoundAt_of_phiAlmostNonnegative hPhi hpinch x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
