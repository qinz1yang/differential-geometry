import DifferentialGeometry.Analysis.Elliptic.MetricExtension.PullbackGram
import DifferentialGeometry.Topology.Handle.ClosedCell.InteriorCoordinates
import DifferentialGeometry.Geometry.Metric.Family.ClosedCellPullback

noncomputable section

open Filter Manifold Set
open scoped ContDiff Manifold Topology

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

theorem gramOnEuclid_closedCellPullbackMetricFamily
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (t : ℝ) (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1) {y : W}
    (hy : y ∈ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target)
    (i j : Fin (Module.finrank ℝ V)) :
    gramOnEuclid
        ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t) α i j y =
      pullbackMetricCoefficients (g t)
        (fun z => Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  let A : W → M := fun z => closedCellChartMap Φ c r
    ((extChartAt (𝓡∂ (m + 1)) α).symm ((toEuclidean (E := V)).symm z))
  let B : W → M := fun z =>
    Φ (c + r • closedCellShiftSucc m (-1) ((toEuclidean (E := V)).symm z))
  have heq : A =ᶠ[𝓝 y] B := by
    have hO : IsOpen (toEuclidean (E := V) ''
        interior (extChartAt (𝓡∂ (m + 1)) α).target) :=
      (toEuclidean (E := V)).toHomeomorph.isOpenMap _ isOpen_interior
    filter_upwards [hO.mem_nhds hy] with z hz
    have htarget : (toEuclidean (E := V)).symm z ∈
        (extChartAt (𝓡∂ (m + 1)) α).target :=
      toEuclidean_symm_mem_target ((image_mono interior_subset) hz)
    dsimp only [A, B, closedCellChartMap]
    rw [closedCell_extChartAt_symm_val_of_norm_lt_one α hα _ htarget]
  have hvalue := heq.eq_of_nhds
  have hderiv := heq.mfderiv_eq (I := 𝓘(ℝ, W)) (I' := I)
  have hgram := gramOnEuclid_pullback (g t) (closedCellChartMap Φ c r)
    (contMDiff_closedCellChartMap Φ c hr.le hsource)
    (injective_mfderiv_closedCellChartMap Φ c hr hsource) α hy i j
  change gramOnEuclid ((g t).pullback (closedCellChartMap Φ c r)
    (contMDiff_closedCellChartMap Φ c hr.le hsource)
    (injective_mfderiv_closedCellChartMap Φ c hr hsource)) α i j y = _
  rw [hgram]
  change pullbackMetricCoefficients (g t) A y _ _ = pullbackMetricCoefficients (g t) B y _ _
  simp only [pullbackMetricCoefficients_apply]
  rw [hderiv, hvalue]

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
