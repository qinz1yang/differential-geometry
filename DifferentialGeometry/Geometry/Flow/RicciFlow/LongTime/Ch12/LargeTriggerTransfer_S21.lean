import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InteriorScaleMain
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleRestriction
import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusBounds

/-!
# CH12-S21 / T3, group T: the T2 transfer with the hypothesis `r < D` instead of `r ≤ 9`
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open GC.Endpoint GC.Topology Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12.LateCutFamily

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  {F : GC.Interface.RawSurgery P g} {K : ℕ} {slices : ℕ → RegularSlice F.observation}

theorem cutPiece_normalized_transfer_hd_S21 (L : GC.LongTime.LateCutFamily F K slices) (j : ℕ)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (i : Fin (L.decomposition j C).components.count)
    (p : ((L.decomposition j C).component i).Carrier)
    (r : ℝ) (hr : 0 < r)
    (hd : ENNReal.ofReal r <
      distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p) :
    (ENNReal.ofReal r < curvatureRadius (L.metric j C i) p →
      ∀ q ∈ riemannianBallOf (slices j).normalizedMetric
        (cutPieceMap (L.decomposition j C) i p).val r,
        SectionalBoundedBelowAt (slices j).normalizedMetric q (-(r ^ 2)⁻¹)) ∧
    ballVolume (L.metric j C i) p r =
      ballVolume (slices j).normalizedMetric (cutPieceMap (L.decomposition j C) i p).val r ∧
    (∀ k : ℕ, ∀ q ∈ riemannianBallOf (L.metric j C i) p r,
      ∃ q' ∈ riemannianBallOf (slices j).normalizedMetric
        (cutPieceMap (L.decomposition j C) i p).val r,
        curvatureDerivativeNorm (L.metric j C i) k q =
          curvatureDerivativeNorm (slices j).normalizedMetric k q') := by
  set U := (slices j).stage.toClosedOrientedManifold.componentOpen C with hUdef
  have hU : IsClosed (U : Set (slices j).stage.toClosedOrientedManifold.Carrier) :=
    ClosedOrientedManifold.isClosed_componentSet (slices j).stage.toClosedOrientedManifold C
  set x := cutPieceMap (L.decomposition j C) i p with hx
  obtain ⟨hball, hscale, hvol, hnorm⟩ :=
    GC.LongTime.LateCutFamily.cutPiece_ball_tests L j C i p hd
  have hRc : curvatureRadius ((slices j).componentMetric C) x =
      curvatureRadius (slices j).normalizedMetric x.val :=
    curvatureRadius_restrictOpen_of_isClosed (slices j).normalizedMetric U hU x
  have hedist : ∀ y : U, riemannianEDistOf ((slices j).componentMetric C) x y =
      riemannianEDistOf (slices j).normalizedMetric x.val y.val := fun y =>
    riemannianEDistOf_restrictOpen_of_isClosed (slices j).normalizedMetric U hU x y
  refine ⟨fun hlt q hq => ?_, ?_, fun k q hq => ?_⟩
  · refine sectionalBoundedBelowAt_of_lt_curvatureRadius _ ?_ hq
    rw [← hRc]
    exact hscale.mp hlt
  · rw [hvol]
    exact Integral.Measure.riemannianVolumeMeasure_ball_restrictOpen_of_isClosed (slices j).normalizedMetric U hU x r
  · have hqc : cutPieceMap (L.decomposition j C) i q ∈
        riemannianBallOf ((slices j).componentMetric C) x r := by
      rw [← hball]; exact mem_image_of_mem _ hq
    refine ⟨(cutPieceMap (L.decomposition j C) i q).val, ?_, ?_⟩
    · have h1 := hedist (cutPieceMap (L.decomposition j C) i q)
      have h2 : riemannianEDistOf ((slices j).componentMetric C) x
          (cutPieceMap (L.decomposition j C) i q) < ENNReal.ofReal r := hqc
      rw [h1] at h2
      exact h2
    · rw [hnorm k q hq]
      exact curvatureDerivativeNorm_restrictOpen (slices j).normalizedMetric U k _

/-- The curvature radius of the piece equals that of the normalized slice at the image point. -/
theorem cutPiece_normalized_radius_S21 (L : GC.LongTime.LateCutFamily F K slices) (j : ℕ)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (i : Fin (L.decomposition j C).components.count)
    (p : ((L.decomposition j C).component i).Carrier)
    (hlt : curvatureRadius (L.metric j C i) p <
      distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p) :
    curvatureRadius (slices j).normalizedMetric (cutPieceMap (L.decomposition j C) i p).val =
      curvatureRadius (L.metric j C i) p := by
  have hU : IsClosed (((slices j).stage.toClosedOrientedManifold.componentOpen C :
      TopologicalSpace.Opens _) : Set (slices j).stage.toClosedOrientedManifold.Carrier) :=
    ClosedOrientedManifold.isClosed_componentSet (slices j).stage.toClosedOrientedManifold C
  rw [← GC.LongTime.LateCutFamily.cutPiece_curvatureRadius_eq_of_lt L j C i p hlt]
  exact (curvatureRadius_restrictOpen_of_isClosed (slices j).normalizedMetric _ hU _).symm

end GC.LongTime.Ch12.LateCutFamily
