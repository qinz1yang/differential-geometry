import DifferentialGeometry.Analysis.Elliptic.MetricExtension.ClosedCellCoefficients
import DifferentialGeometry.Analysis.Elliptic.MetricExtension.GramDensity

noncomputable section

open Manifold Set
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Handle
open DifferentialGeometry.Topology.Manifold

private local instance (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

private local instance (m : ℕ) :
    IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  closedCellIsManifold m

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin (m + 1))
local notation "W" => EuclideanSpace ℝ (Fin (Module.finrank ℝ V))

private local instance : T2Space V := inferInstance

theorem densityOnEuclid_closedCellPullbackMetricFamily
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (t : ℝ) (α : ClosedCell (m + 1)) {y : W}
    (hα : ‖α.val‖ < 1)
    (hy : y ∈ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target) :
    densityOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α y =
      Real.sqrt (Matrix.of (fun k l => pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1))).det := by
  have hgram :
      (Matrix.of (fun k l => gramOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α k l y)) =
      (Matrix.of (fun k l => pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1))) := by
    funext k l
    exact gramOnEuclid_closedCellPullbackMetricFamily D g Φ c hr hsource t α hα hy k l
  rw [densityOnEuclid_eq_sqrt_det, hgram]

theorem invGramOnEuclid_closedCellPullbackMetricFamily
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (t : ℝ) (α : ClosedCell (m + 1)) {y : W}
    (hα : ‖α.val‖ < 1)
    (hy : y ∈ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target)
    (i j : Fin (Module.finrank ℝ V)) :
    invGramOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α i j y =
      (Matrix.of (fun k l => pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1)))⁻¹ i j := by
  have hgram :
      (Matrix.of (fun k l => gramOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α k l y)) =
      (Matrix.of (fun k l => pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1))) := by
    funext k l
    exact gramOnEuclid_closedCellPullbackMetricFamily D g Φ c hr hsource t α hα hy k l
  rw [invGramOnEuclid_eq_matrix_inv, hgram]

theorem weightedInvGramOnEuclid_closedCellPullbackMetricFamily
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (t : ℝ) (α : ClosedCell (m + 1)) {y : W}
    (hα : ‖α.val‖ < 1)
    (hy : y ∈ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target)
    (i j : Fin (Module.finrank ℝ V)) :
    weightedInvGramOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α i j y =
      Real.sqrt (Matrix.of (fun k l => pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1))).det *
        (Matrix.of (fun k l => pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1)))⁻¹ i j := by
  have hgram :
      (Matrix.of (fun k l => gramOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α k l y)) =
      (Matrix.of (fun k l => pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single l 1))) := by
    funext k l
    exact gramOnEuclid_closedCellPullbackMetricFamily D g Φ c hr hsource t α hα hy k l
  rw [weightedInvGramOnEuclid_eq_sqrt_det_mul_inv, hgram]

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
