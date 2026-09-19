import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Geometry.Coordinates.Frame.ClosedBall
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open DifferentialGeometry.Topology DifferentialGeometry.Topology.Handle
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure

variable {m : ℕ}
local notation "EuN" => EuclideanSpace ℝ (Fin (m + 1))
local instance : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m
local instance : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) := closedCellIsManifold m

theorem gramOnEuclid_closedCell_pullback
    (g : SmoothRiemannianMetric (𝓡 (m + 1)) EuN)
    {α : ClosedCell (m + 1)} (hα : ‖α.val‖ < 1)
    {y : EuN}
    (hy : y ∈ (extChartAt (𝓡∂ (m + 1)) α).target)
    (i j : Fin (Module.finrank ℝ EuN)) :
    gramOnEuclid (g.pullback (I := 𝓡∂ (m + 1)) (Subtype.val : ClosedCell (m + 1) → EuN)
      (closedCellInclusion_contMDiff m) (injective_mfderiv_closedCell_inclusion (m := m))) α i j (toEuclidean y) =
      g.inner (closedCellShiftSucc m (-1) y)
        (chartModelBasis EuN i) (chartModelBasis EuN j) := by
  let x := (extChartAt (𝓡∂ (m + 1)) α).symm y
  have hxval : x.val = closedCellShiftSucc m (-1) y :=
    extChartAt_closedCell_symm_val hα hy
  have hx : ‖x.val‖ < 1 := by
    rw [hxval]
    rwa [extChartAt_closedCell_target hα] at hy
  unfold gramOnEuclid
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [chartGramMatrix_apply, SmoothRiemannianMetric.pullback_inner]
  change g.inner x.val (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) Subtype.val x
    (chartBasisVecFiber (I := 𝓡∂ (m + 1)) α i x))
    (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) Subtype.val x
      (chartBasisVecFiber (I := 𝓡∂ (m + 1)) α j x)) = _
  rw [mfderiv_closedCell_inclusion_of_norm_lt_one hx]
  change g.inner x.val (chartBasisVecFiber (I := 𝓡∂ (m + 1)) α i x)
    (chartBasisVecFiber (I := 𝓡∂ (m + 1)) α j x) = _
  rw [chartBasisVecFiber_closedCell_of_norm_lt_one hα hx,
    chartBasisVecFiber_closedCell_of_norm_lt_one hα hx, hxval]

theorem densityOnEuclid_closedCell_pullback
    (g : SmoothRiemannianMetric (𝓡 (m + 1)) EuN)
    {α : ClosedCell (m + 1)} (hα : ‖α.val‖ < 1)
    {y : EuN} (hy : y ∈ (extChartAt (𝓡∂ (m + 1)) α).target) :
    densityOnEuclid (g.pullback (I := 𝓡∂ (m + 1)) (Subtype.val : ClosedCell (m + 1) → EuN)
      (closedCellInclusion_contMDiff m) (injective_mfderiv_closedCell_inclusion (m := m))) α
        (toEuclidean y) =
      Real.sqrt (Matrix.det (Matrix.of fun i j => g.inner (closedCellShiftSucc m (-1) y)
        (chartModelBasis EuN i) (chartModelBasis EuN j))) := by
  rw [densityOnEuclid, chartDensity]
  apply congrArg Real.sqrt
  apply congrArg Matrix.det
  ext i j
  exact gramOnEuclid_closedCell_pullback g hα hy i j

theorem invGramOnEuclid_closedCell_pullback
    (g : SmoothRiemannianMetric (𝓡 (m + 1)) EuN)
    {α : ClosedCell (m + 1)} (hα : ‖α.val‖ < 1)
    {y : EuN} (hy : y ∈ (extChartAt (𝓡∂ (m + 1)) α).target)
    (i j : Fin (Module.finrank ℝ EuN)) :
    invGramOnEuclid (g.pullback (I := 𝓡∂ (m + 1)) (Subtype.val : ClosedCell (m + 1) → EuN)
      (closedCellInclusion_contMDiff m) (injective_mfderiv_closedCell_inclusion (m := m))) α i j
        (toEuclidean y) =
      (Matrix.of fun k l => g.inner (closedCellShiftSucc m (-1) y)
        (chartModelBasis EuN k) (chartModelBasis EuN l))⁻¹ i j := by
  have hgram : (Matrix.of fun k l => gramOnEuclid
      (g.pullback (I := 𝓡∂ (m + 1)) (Subtype.val : ClosedCell (m + 1) → EuN)
        (closedCellInclusion_contMDiff m) (injective_mfderiv_closedCell_inclusion (m := m))) α k l
          (toEuclidean y)) =
      Matrix.of (fun k l => g.inner (closedCellShiftSucc m (-1) y)
        (chartModelBasis EuN k) (chartModelBasis EuN l)) := by
    ext k l
    exact gramOnEuclid_closedCell_pullback g hα hy k l
  exact congrArg (fun B : Matrix (Fin (Module.finrank ℝ EuN)) (Fin (Module.finrank ℝ EuN)) ℝ =>
    B⁻¹ i j) hgram

theorem weightedInvGramOnEuclid_closedCell_pullback
    (g : SmoothRiemannianMetric (𝓡 (m + 1)) EuN)
    {α : ClosedCell (m + 1)} (hα : ‖α.val‖ < 1)
    {y : EuN} (hy : y ∈ (extChartAt (𝓡∂ (m + 1)) α).target)
    (i j : Fin (Module.finrank ℝ EuN)) :
    weightedInvGramOnEuclid
      (g.pullback (I := 𝓡∂ (m + 1)) (Subtype.val : ClosedCell (m + 1) → EuN)
        (closedCellInclusion_contMDiff m) (injective_mfderiv_closedCell_inclusion (m := m))) α i j
          (toEuclidean y) =
      let B := Matrix.of fun k l => g.inner (closedCellShiftSucc m (-1) y)
        (chartModelBasis EuN k) (chartModelBasis EuN l)
      Real.sqrt B.det * B⁻¹ i j := by
  rw [weightedInvGramOnEuclid, densityOnEuclid_closedCell_pullback g hα hy,
    invGramOnEuclid_closedCell_pullback g hα hy]

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
