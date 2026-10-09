import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapSurface
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.Product.Completeness
import DifferentialGeometry.Geometry.Metric.CompletenessPullback
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import DifferentialGeometry.Topology.Manifold.LinearRechart
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz

/-! Actual scaled capped plane, real product and E3 metric transport with global slab bounds. -/

set_option autoImplicit false

noncomputable section
open Manifold DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open scoped Manifold ContDiff InnerProductSpace Topology
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry.Collapse.EdgeCapProduct

theorem surfaceMetric_le_euclidean (x v : E2) :
    surfaceMetric.inner x v v ≤ ‖v‖ ^ 2 := by
  rw [surfaceMetric_inner]
  have h := DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_inner_le
    (planeMap x) (planeMap v)
  have hn : ‖planeMap v‖ = ‖v‖ := planeEmbedding.norm_map v
  simpa only [hn] using h

theorem surfaceEDist_le_euclidean (x y : E2) :
    riemannianEDistOf surfaceMetric x y ≤
      riemannianEDistOf (euclideanMetric (E := E2)) x y := by
  apply edistOf_mono
  intro z v
  change surfaceMetric.inner z v v ≤ @inner ℝ E2 inferInstance v v
  exact (surfaceMetric_le_euclidean z v).trans_eq
    (real_inner_self_eq_norm_sq (F := E2) (show E2 from v)).symm

def scaledCapMetric (ε : ℝ) (hε : 0 < ε) : SmoothRiemannianMetric (𝓡 2) E2 :=
  scaleMetric (ε ^ 2) (pow_pos hε 2) surfaceMetric

theorem scaledCapComplete (ε : ℝ) (hε : 0 < ε) :
    RiemannianMetricComplete (scaledCapMetric ε hε) :=
  surfaceComplete.scaleMetric (ε ^ 2) (pow_pos hε 2)

theorem scaledCapRm (ε : ℝ) (hε : 0 < ε) (x : E2) (u v : TangentSpace (𝓡 2) x) :
    0 ≤ metricRm04StandardAt (scaledCapMetric ε hε) x u v v u := by
  rw [scaledCapMetric, metricRmStandard_scale]
  exact mul_nonneg (sq_nonneg ε) (surfaceRm_nonneg x u v)

def capProductMetric (ε : ℝ) (hε : 0 < ε) :
    SmoothRiemannianMetric (𝓘(ℝ, ℝ).prod (𝓡 2)) (ℝ × E2) :=
  (euclideanMetric (E := ℝ)).prod (scaledCapMetric ε hε)

theorem capProductComplete (ε : ℝ) (hε : 0 < ε) :
    RiemannianMetricComplete (capProductMetric ε hε) :=
  (euclideanMetric_complete (E := ℝ)).prod (scaledCapComplete ε hε)

def capProductCoordinates : (ℝ × E2) ≃ₘ⟮𝓘(ℝ, ℝ).prod (𝓡 2), 𝓡 3⟯ E3 := by
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact ((LinearIsometryEquiv.prodComm ℝ ℝ E2).toContinuousLinearEquiv.trans
    (DifferentialGeometry.Topology.productModelEquiv 2)).toDiffeomorph

def capThreeMetric (ε : ℝ) (hε : 0 < ε) : SmoothRiemannianMetric (𝓡 3) E3 :=
  Diffeomorph.pullbackMetricCross (capProductMetric ε hε) capProductCoordinates.symm

theorem capThreeComplete (ε : ℝ) (hε : 0 < ε) :
    RiemannianMetricComplete (capThreeMetric ε hε) :=
  DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_pullbackMetricCross
    (capProductComplete ε hε) capProductCoordinates.symm

theorem capThree_pullback (ε : ℝ) (hε : 0 < ε) :
    Diffeomorph.pullbackMetricCross (capThreeMetric ε hε) capProductCoordinates =
      capProductMetric ε hε :=
  (Diffeomorph.pullbackMetricCross_symm_eq_iff
    (Φ := capProductCoordinates.symm)
    (g := capProductMetric ε hε) (h := capThreeMetric ε hε)).mp rfl

theorem capThree_physical_inner (ε : ℝ) (hε : 0 < ε) (p : ℝ × E2)
    (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p) :
    (capThreeMetric ε hε).inner (capProductCoordinates p)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) capProductCoordinates p v)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) capProductCoordinates p w) =
        (capProductMetric ε hε).inner p v w := by
  have h := congrArg (fun g : SmoothRiemannianMetric (𝓘(ℝ, ℝ).prod (𝓡 2)) (ℝ × E2) =>
    g.inner p v w) (capThree_pullback ε hε)
  simpa only [Diffeomorph.pullbackMetricCross_inner] using h

theorem capProductRm (ε : ℝ) (hε : 0 < ε) (p : ℝ × E2)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p) :
    0 ≤ metricRm04StandardAt (capProductMetric ε hε) p u v v u := by
  rw [capProductMetric, metricRm04StandardAt_apply,
    metricRm04At_productMetric_apply, euclideanMetric_metricRm04At_eq_zero]
  change 0 ≤ 0 + metricRm04StandardAt (scaledCapMetric ε hε) p.2 u.2 v.2 v.2 u.2
  simpa only [zero_add] using scaledCapRm ε hε p.2 u.2 v.2

theorem capThreeSectional (ε : ℝ) (hε : 0 < ε) (x : E3) :
    SectionalBoundedBelowAt (capThreeMetric ε hε) x 0 := by
  intro u v
  rw [zero_mul]
  change 0 ≤ metricRm04StandardAt
    (Diffeomorph.pullbackMetricCross (capProductMetric ε hε) capProductCoordinates.symm)
    x u v v u
  rw [metricRm04Standard_pullbackCross]
  exact capProductRm ε hε _ _ _

theorem capThree_physical_product (ε : ℝ) (hε : 0 < ε) (p : ℝ × E2)
    (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p) :
    (capThreeMetric ε hε).inner (capProductCoordinates p)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) capProductCoordinates p v)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) capProductCoordinates p w) =
        v.1 * w.1 + (scaledCapMetric ε hε).inner p.2 v.2 w.2 := by
  rw [capThree_physical_inner, capProductMetric, SmoothRiemannianMetric.prod_inner]
  change w.1 * v.1 + _ = v.1 * w.1 + _
  rw [mul_comm w.1 v.1]

theorem capThreeOrientation : Nonempty (ManifoldOrientation (𝓡 3) E3 3) :=
  DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_of_simply_connected (by simp)

theorem scaledCapEDist_le (ε : ℝ) (hε : 0 < ε) (x y : E2) :
    riemannianEDistOf (scaledCapMetric ε hε) x y ≤ ENNReal.ofReal (ε * dist x y) := by
  have hsqrt : Real.sqrt (ε ^ 2) = ε := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hε]
  calc
    riemannianEDistOf (scaledCapMetric ε hε) x y =
        ENNReal.ofReal ε * riemannianEDistOf surfaceMetric x y := by
      rw [scaledCapMetric, edistOf_scale, hsqrt]
    _ ≤ ENNReal.ofReal ε * riemannianEDistOf (euclideanMetric (E := E2)) x y :=
      mul_le_mul_right (surfaceEDist_le_euclidean x y) _
    _ = ENNReal.ofReal (ε * dist x y) := by
      rw [show euclideanMetric (E := E2) = standardEuclideanMetric E2 from rfl,
        riemannianEDistOf_standardEuclideanMetric, edist_dist, ← ENNReal.ofReal_mul hε.le]

theorem smoothRadius_edist_le (x y : E2) :
    edist (smoothRadius x) (smoothRadius y) ≤ riemannianEDistOf surfaceMetric x y := by
  have h := edist_map_le_of_metric_mfderiv_bound surfaceMetric (C := (1 : NNReal))
    (by norm_num) (smoothRadius_contDiff.contMDiff.of_le (by decide))
    (fun z v => by
      rw [mfderiv_eq_fderiv]
      change ‖fderiv ℝ smoothRadius z v‖ ≤ (1 : ℝ) * Real.sqrt (surfaceMetric.inner z v v)
      simpa only [one_mul] using smoothRadius_speed_bound z v) x y
  simpa only [ENNReal.coe_one, one_mul] using h

def capHeight (ε : ℝ) (x : E2) : ℝ := ε * smoothRadius x

theorem capHeight_norm_le (ε : ℝ) (hε : 0 < ε) (x : E2) :
    ε * ‖x‖ ≤ capHeight ε x :=
  mul_le_mul_of_nonneg_left (norm_le_smoothRadius x) hε.le

theorem capHeight_edist_le (ε : ℝ) (hε : 0 < ε) (x y : E2) :
    edist (capHeight ε x) (capHeight ε y) ≤
      riemannianEDistOf (scaledCapMetric ε hε) x y := by
  have he : edist (capHeight ε x) (capHeight ε y) =
      ENNReal.ofReal ε * edist (smoothRadius x) (smoothRadius y) := by
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq]
    simp only [capHeight]
    rw [← mul_sub, abs_mul, abs_of_pos hε, ENNReal.ofReal_mul hε.le]
  calc
    _ = ENNReal.ofReal ε * edist (smoothRadius x) (smoothRadius y) := he
    _ ≤ ENNReal.ofReal ε * riemannianEDistOf surfaceMetric x y :=
      mul_le_mul_right (smoothRadius_edist_le x y) _
    _ = riemannianEDistOf (scaledCapMetric ε hε) x y := by
      rw [scaledCapMetric, edistOf_scale, Real.sqrt_sq_eq_abs, abs_of_pos hε]

theorem capProductEDist_zero_le (ε : ℝ) (hε : 0 < ε) (p : ℝ × E2) :
    riemannianEDistOf (capProductMetric ε hε) (0, 0) p ≤
      ENNReal.ofReal (|p.1| + ε * ‖p.2‖) := by
  have hl : riemannianEDistOf (euclideanMetric (E := ℝ)) 0 p.1 =
      ENNReal.ofReal |p.1| := by
    rw [show euclideanMetric (E := ℝ) = standardEuclideanMetric ℝ from rfl,
      riemannianEDistOf_standardEuclideanMetric, edist_dist, dist_zero_left, Real.norm_eq_abs]
  have hs := scaledCapEDist_le ε hε 0 p.2
  simp only [dist_zero_left] at hs
  have ht := riemannianEDistOf_triangle (capProductMetric ε hε) (0, 0) (p.1, 0) p
  rw [capProductMetric, riemannianEDistOf_prod_left, riemannianEDistOf_prod_right, hl] at ht
  calc
    _ ≤ ENNReal.ofReal |p.1| + riemannianEDistOf (scaledCapMetric ε hε) 0 p.2 := ht
    _ ≤ ENNReal.ofReal |p.1| + ENNReal.ofReal (ε * ‖p.2‖) := add_le_add le_rfl hs
    _ = _ := (ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg hε.le (norm_nonneg _))).symm

theorem capProductEDist_slab (ε : ℝ) (hε : 0 < ε) (Δ : ℝ) (p : ℝ × E2)
    (ht : |p.1| ≤ 4 * Δ) (hF : capHeight ε p.2 ≤ 4 * Δ) :
    riemannianEDistOf (capProductMetric ε hε) (0, 0) p ≤ ENNReal.ofReal (8 * Δ) := by
  apply (capProductEDist_zero_le ε hε p).trans
  apply ENNReal.ofReal_le_ofReal
  have hr := (capHeight_norm_le ε hε p.2).trans hF
  linarith

theorem capHeight_contDiff (ε : ℝ) : ContDiff ℝ ∞ (capHeight ε) :=
  contDiff_const.mul smoothRadius_contDiff

theorem capHeight_zero (ε : ℝ) : capHeight ε 0 = ε := by
  simp [capHeight, smoothRadius]

def capThreeCoord (x : E3) : ℝ := (capProductCoordinates.symm x).1

def capThreeHeight (ε : ℝ) (x : E3) : ℝ :=
  capHeight ε (capProductCoordinates.symm x).2

theorem capThreeEDist_slab (ε : ℝ) (hε : 0 < ε) (Δ : ℝ) (x : E3)
    (ht : |capThreeCoord x| ≤ 4 * Δ) (hF : capThreeHeight ε x ≤ 4 * Δ) :
    riemannianEDistOf (capThreeMetric ε hε) (capProductCoordinates (0, 0)) x ≤
      ENNReal.ofReal (8 * Δ) := by
  rw [capThreeMetric,
    DifferentialGeometry.riemannianEDistOf_pullbackMetricCross,
    Diffeomorph.symm_apply_apply]
  exact capProductEDist_slab ε hε Δ (capProductCoordinates.symm x) ht hF

end DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
