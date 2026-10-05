import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeChart
import DifferentialGeometry.Geometry.Collapse.Inhabitants.SmallFlatCircle
import DifferentialGeometry.Geometry.Collapse.Inhabitants.EuclideanProductCoordinates
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Geometry.Metric.Product.Completeness
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Collapse.SelectedZeroModelInputs
import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean
import DifferentialGeometry.Geometry.Comparison.LineSplitting
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import DifferentialGeometry.Geometry.Comparison.Splitting.AffineFunctionNormalForm

/-!
The intrinsic product of the Euclidean plane and a small flat circle carries physical
plane coordinates and a nonempty positive halfspace collar.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse
open GC.MetricGeometry Set Metric DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace DifferentialGeometry.Geometry.Collapse

local notation "M" => EuclideanSpace ℝ (Fin 2) × AddCircle (1 : ℝ)
local notation "IP" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

def edgePlaneCircleMetric : SmoothRiemannianMetric IP M :=
  (euclideanMetric (E := EuclideanSpace ℝ (Fin 2))).prod smallFlatCircleMetric

local instance edgePlaneCircleIntrinsicMetric : MetricSpace M :=
  inducedMetricSpace edgePlaneCircleMetric
local instance edgePlaneCircleIntrinsicUniform : UniformSpace M :=
  edgePlaneCircleIntrinsicMetric.toUniformSpace
local instance edgePlaneCircleIntrinsicEMetric : PseudoEMetricSpace M :=
  edgePlaneCircleIntrinsicMetric.toPseudoEMetricSpace
local instance edgePlaneCircleIntrinsicPseudoMetric : PseudoMetricSpace M :=
  edgePlaneCircleIntrinsicMetric.toPseudoMetricSpace
local instance edgePlaneCircleIntrinsicBundle : RiemannianBundle (fun p : M => TangentSpace IP p) :=
  ⟨edgePlaneCircleMetric.toRiemannianMetric⟩
local instance edgePlaneCircleIntrinsicRiemannian : IsRiemannianManifold IP M :=
  inducedMetricSpace_isRiemannianManifold edgePlaneCircleMetric
local instance edgePlaneCircleIntrinsicContinuous :
    IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2) × ℝ) (fun p : M => TangentSpace IP p) :=
  isContinuousRiemannianBundle_of_smoothRiemannianMetric edgePlaneCircleMetric
local instance edgePlaneCircleIntrinsicComplete : CompleteSpace M :=
  ((euclideanMetric_complete (E := EuclideanSpace ℝ (Fin 2))).prod
    (RiemannianMetricComplete.of_compact smallFlatCircleMetric)).complete
local instance edgePlaneCircleNativeDimension :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) :=
  ⟨by simp⟩

theorem edgePlaneCircleMetricNorm : IsMetricNorm edgePlaneCircleMetric :=
  isMetricNorm_of_smoothRiemannianMetric edgePlaneCircleMetric

def edgePlaneCircleHalfspace : Set M := {p | p.1 1 ≤ 0}
def edgePlaneCircleRho : M → ℝ := fun _p => 1
def edgePlaneCircleHeight : M → ℝ := fun p => max (p.1 1) 0


private theorem edgePlaneCircle_euclideanDistance (x y : EuclideanSpace ℝ (Fin 2)) :
    riemannianEDistOf (euclideanMetric (E := EuclideanSpace ℝ (Fin 2))) x y =
      ENNReal.ofReal (dist x y) := by
  rw [show euclideanMetric (E := EuclideanSpace ℝ (Fin 2)) =
    standardEuclideanMetric (EuclideanSpace ℝ (Fin 2)) from rfl,
    riemannianEDistOf_standardEuclideanMetric, edist_dist]

private theorem edgePlaneCircle_plane_le (x y : M) : dist x.1 y.1 ≤ dist x y := by
  have hd := riemannianEDistOf_fst_le_prod
    (euclideanMetric (E := EuclideanSpace ℝ (Fin 2))) smallFlatCircleMetric x y
  rw [edgePlaneCircle_euclideanDistance] at hd
  change ENNReal.ofReal (dist x.1 y.1) ≤ riemannianEDistOf edgePlaneCircleMetric x y at hd
  rw [inducedMetricSpace_hmetric edgePlaneCircleMetric] at hd
  exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hd

private theorem edgePlaneCircle_sameCircle (x y : EuclideanSpace ℝ (Fin 2))
    (t : AddCircle (1 : ℝ)) : dist (x, t) (y, t) = dist x y := by
  change (riemannianEDistOf edgePlaneCircleMetric (x, t) (y, t)).toReal = dist x y
  rw [edgePlaneCircleMetric, riemannianEDistOf_prod_left,
    edgePlaneCircle_euclideanDistance, ENNReal.toReal_ofReal dist_nonneg]

private theorem edgePlaneCircle_samePlane (x : EuclideanSpace ℝ (Fin 2))
    (t u : AddCircle (1 : ℝ)) : dist (x, t) (x, u) ≤ 1 / 10000 := by
  change (riemannianEDistOf edgePlaneCircleMetric (x, t) (x, u)).toReal ≤ _
  rw [edgePlaneCircleMetric, riemannianEDistOf_prod_right]
  exact (ENNReal.toReal_mono (by norm_num) (smallFlatCircle_distance t u)).trans_eq
    (ENNReal.toReal_ofReal (by norm_num))

private theorem edgePlaneCircle_dist_upper (x y : M) :
    dist x y ≤ dist x.1 y.1 + 1 / 10000 := by
  calc
    dist x y ≤ dist x (y.1, x.2) + dist (y.1, x.2) y := dist_triangle _ _ _
    _ ≤ dist x.1 y.1 + 1 / 10000 := by
      rw [edgePlaneCircle_sameCircle]
      exact add_le_add_right (edgePlaneCircle_samePlane y.1 x.2 y.2) _

private theorem edgePlaneCircle_coordinate_le (x y : M) (j : Fin 2) :
    |x.1 j - y.1 j| ≤ dist x y := by
  have h := PiLp.norm_apply_le (x.1 - y.1) j
  change |x.1 j - y.1 j| ≤ ‖x.1 - y.1‖ at h
  exact h.trans (by simpa only [dist_eq_norm] using edgePlaneCircle_plane_le x y)

private theorem edgePlaneCircle_sectional (x : M) :
    SectionalBoundedBelowAt edgePlaneCircleMetric x 0 := by
  intro v w
  rw [zero_mul]
  have hprod : metricRm04StandardAt edgePlaneCircleMetric x v w w v =
      metricRm04StandardAt (euclideanMetric (E := EuclideanSpace ℝ (Fin 2)))
        x.1 v.1 w.1 w.1 v.1 +
      metricRm04StandardAt smallFlatCircleMetric x.2 v.2 w.2 w.2 v.2 :=
    metricRm04At_productMetric_apply
      (euclideanMetric (E := EuclideanSpace ℝ (Fin 2))) smallFlatCircleMetric
      x (vec4 v w w v)
  have he : metricRm04StandardAt (euclideanMetric (E := EuclideanSpace ℝ (Fin 2)))
      x.1 v.1 w.1 w.1 v.1 = 0 :=
    congrArg (fun R => R (vec4 v.1 w.1 w.1 v.1))
      (euclideanMetric_metricRm04At_eq_zero x.1)
  have hflat := hprod.trans
    (congrArg₂ (fun a b : ℝ => a + b) he (smallFlatCircle_flat x.2 v.2 w.2))
  exact hflat.symm ▸ (by norm_num : (0 : ℝ) ≤ 0 + 0)

private def edgePlaneCircleLine (s : ℝ) : M := (PiLp.single 2 0 s, 0)

private theorem edgePlaneCircleLine_isometry : Isometry edgePlaneCircleLine := by
  apply Isometry.of_dist_eq
  intro s t
  rw [edgePlaneCircleLine, edgePlaneCircleLine, edgePlaneCircle_sameCircle,
    dist_eq_norm, ← PiLp.single_sub, PiLp.norm_single, Real.dist_eq, Real.norm_eq_abs]

private theorem edgePlaneCircle_lineCoordinate (x : M) :
    Comparison.Toponogov.lineCoordinate edgePlaneCircleLine x = x.1 0 := by
  obtain ⟨_hproper, hcomp, _hsegments⟩ := model_lcp04_clauses_of_sectional_nonneg
    edgePlaneCircleMetric edgePlaneCircleMetricNorm edgePlaneCircle_sectional
  let a := x.1 0
  let b := Comparison.Toponogov.lineCoordinate edgePlaneCircleLine x
  let c := dist x (edgePlaneCircleLine 0) ^ 2
  have hh (t : ℝ) : 2 * (b - a) * t ≤ c - a ^ 2 := by
    have hl := edgePlaneCircle_coordinate_le x (edgePlaneCircleLine t) 0
    change |x.1 0 - t| ≤ dist x (edgePlaneCircleLine t) at hl
    have hs := Comparison.Toponogov.sq_dist_isometry_line
      hcomp edgePlaneCircleLine_isometry x t
    have hsq := sq_le_sq₀ (abs_nonneg (x.1 0 - t)) dist_nonneg |>.2 hl
    rw [sq_abs] at hsq
    dsimp [a, b, c]
    nlinarith
  by_contra hne
  have hn : 2 * (b - a) ≠ 0 := by
    dsimp [a, b]
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hne)
  have hb := hh ((c - a ^ 2 + 1) / (2 * (b - a)))
  rw [mul_div_cancel₀ _ hn] at hb
  linarith

theorem edgePlaneCircleHalfspace_isClosed : IsClosed edgePlaneCircleHalfspace := by
  exact isClosed_le ((EuclideanSpace.proj (1 : Fin 2)).continuous.comp continuous_fst)
    continuous_const

theorem edgePlaneCircleHeight_infDist (x : M) :
    edgePlaneCircleHeight x = infDist x edgePlaneCircleHalfspace := by
  by_cases hx : x.1 1 ≤ 0
  · rw [infDist_zero_of_mem (show x ∈ edgePlaneCircleHalfspace from hx)]
    change max (x.1 1) 0 = 0
    exact max_eq_right hx
  · have hy : 0 < x.1 1 := lt_of_not_ge hx
    rw [edgePlaneCircleHeight, max_eq_left hy.le]
    apply le_antisymm
    · apply (le_infDist ⟨(0, 0), by simp [edgePlaneCircleHalfspace]⟩).2
      intro y hyA
      have hd := edgePlaneCircle_coordinate_le x y 1
      have hb : x.1 1 - y.1 1 ≤ |x.1 1 - y.1 1| := le_abs_self _
      change y.1 1 ≤ 0 at hyA
      linarith
    · let y : M := (x.1 - PiLp.single 2 1 (x.1 1), x.2)
      have hmem : y ∈ edgePlaneCircleHalfspace := by
        change x.1 1 - (PiLp.single 2 (1 : Fin 2) (x.1 1) : EuclideanSpace ℝ (Fin 2)) 1 ≤ 0
        simp
      have hd : dist x y = x.1 1 := by
        rw [edgePlaneCircle_sameCircle]
        simp only [dist_eq_norm, sub_sub_cancel, PiLp.norm_single, Real.norm_eq_abs,
          abs_of_pos hy]
      exact (infDist_le_dist_of_mem hmem).trans_eq hd

private instance edgePlaneCircleProper : ProperSpace M :=
  (model_lcp04_clauses_of_sectional_nonneg edgePlaneCircleMetric
    edgePlaneCircleMetricNorm edgePlaneCircle_sectional).1

private def edgePlaneCircleSplitting :
    M ≃ᵢ WithLp 2 (ℝ × {x : M //
      Comparison.Toponogov.lineCoordinate edgePlaneCircleLine x = 0}) :=
  Comparison.Toponogov.lineSplitting
    (model_lcp04_clauses_of_sectional_nonneg edgePlaneCircleMetric
      edgePlaneCircleMetricNorm edgePlaneCircle_sectional).2.1
    edgePlaneCircleLine_isometry
    (model_lcp04_clauses_of_sectional_nonneg edgePlaneCircleMetric
      edgePlaneCircleMetricNorm edgePlaneCircle_sectional).2.2

private theorem edgePlaneCircleSplitting_fst (x : M) :
    (edgePlaneCircleSplitting x).fst = x.1 0 := edgePlaneCircle_lineCoordinate x

private def edgePlaneCircleQ (x : M) : WithLp 2 (ℝ × ℝ) :=
  planeReferenceIsometry.symm x.1

private theorem edgePlaneCircleQ_fst (x : M) : (edgePlaneCircleQ x).fst = x.1 0 := by
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0)
    (planeReferenceIsometry.apply_symm_apply x.1)
  simpa only [edgePlaneCircleQ, planeReferenceIsometry_apply_zero] using h

private theorem edgePlaneCircle_coordinate_lipschitz (j : Fin 2) :
    LipschitzWith 1 (fun x : M => x.1 j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    edgePlaneCircle_coordinate_le x y j

private theorem edgePlaneCircle_coordinate_smooth (j : Fin 2) :
    ContMDiff IP 𝓘(ℝ, ℝ) ∞ (fun x : M => x.1 j) := by
  let ℓ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj j
  have hℓ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ ℓ := ℓ.contDiff.contMDiff
  exact hℓ.comp (show ContMDiff IP (𝓡 2) ∞
    (Prod.fst : M → EuclideanSpace ℝ (Fin 2)) from contMDiff_fst)

private def edgePlaneCircleJ : M → EuclideanSpace ℝ (Fin 2) :=
  edgeReferenceCoordinates ![fun x => x.1 0,
    fun x => edgePlaneCircleHeight x / edgePlaneCircleRho x]

private theorem edgePlaneCircleJ_eq {x : M} (hx : 0 < x.1 1) :
    edgePlaneCircleJ x = x.1 := by
  apply PiLp.ext
  intro j
  fin_cases j <;>
    simp [edgePlaneCircleJ, edgeReferenceCoordinates, edgePlaneCircleHeight,
      edgePlaneCircleRho, max_eq_left hx.le]

private theorem edgePlaneCircle_positive_buffer {x y : M}
    (hx : 10000000 ≤ edgePlaneCircleHeight x)
    (hy : dist y x < 10000) : 0 < y.1 1 := by
  have hxpos : 0 < x.1 1 := by
    by_contra h
    have hz : x.1 1 ≤ 0 := le_of_not_gt h
    rw [edgePlaneCircleHeight, max_eq_right hz] at hx
    norm_num at hx
  rw [edgePlaneCircleHeight, max_eq_left hxpos.le] at hx
  have hd := edgePlaneCircle_coordinate_le y x 1
  have ha := neg_abs_le (y.1 1 - x.1 1)
  linarith

private theorem edgePlaneCircleJ_eventually {x : M} (hx : 0 < x.1 1) :
    edgePlaneCircleJ =ᶠ[𝓝 x] Prod.fst := by
  have h := (edgePlaneCircle_coordinate_lipschitz 1).continuous.continuousAt
    |>.eventually (Ioi_mem_nhds hx)
  exact h.mono fun y hy => edgePlaneCircleJ_eq hy

private theorem edgePlaneCircleJ_derivative {x : M} (hx : 0 < x.1 1) :
    mfderiv IP (𝓡 2) edgePlaneCircleJ x =
      ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ := by
  rw [(edgePlaneCircleJ_eventually hx).mfderiv_eq, mfderiv_fst]
  ext v
  rfl

private theorem edgePlaneCircleJ_smooth {x : M}
    (hx : 10000000 ≤ edgePlaneCircleHeight x) :
    ContMDiffOn IP (𝓡 2) ∞ edgePlaneCircleJ (ball x 300) := by
  apply contMDiff_fst.contMDiffOn.congr
  intro y hy
  exact (edgePlaneCircleJ_eq (edgePlaneCircle_positive_buffer hx
    (lt_trans hy (by norm_num))))

private theorem edgePlaneCircle_indicator_buffer {x y : M}
    (hx : x ∈ ball (0 : M) 10000000000) (hy : dist y x < 10000) :
    y ∈ ball (0 : M) 20000000000 := by
  have ht := dist_triangle y x 0
  change dist x 0 < 10000000000 at hx
  change dist y 0 < 20000000000
  linarith

private theorem edgePlaneCircle_planeComparison {x y : M}
    (hx : x ∈ ball (0 : M) 10000000000) (hy : dist y x < 10000) :
    planeComparisonMap edgePlaneCircleQ 0 x 100000000 1 y =
      planeReferenceIsometry.symm (y.1 - x.1) := by
  have hm : y ∈ ball (0 : M) (200 * 100000000) := by
    norm_num
    exact edgePlaneCircle_indicator_buffer hx hy
  rw [planeComparisonMap_of_mem hm, inv_one,
    one_smul]
  exact (planeReferenceIsometry.symm.map_sub y.1 x.1).symm

private def edgePlaneCirclePlaneKL (x : M) (hx : x ∈ ball (0 : M) 10000000000) :
    @KleinerLottApprox M (WithLp 2 (ℝ × ℝ))
      ((edgePlaneCircleIntrinsicMetric.rescale (1 : ℝ)⁻¹ (by norm_num))) inferInstance
      x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) (1 / 100) := by
  refine @KleinerLottApprox.mk M (WithLp 2 (ℝ × ℝ))
    ((edgePlaneCircleIntrinsicMetric.rescale (1 : ℝ)⁻¹ (by norm_num))) inferInstance
    x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) (1 / 100)
    (by norm_num) (by norm_num)
    (planeComparisonMap edgePlaneCircleQ 0 x 100000000 1) ?_ ?_ ?_
  · rw [edgePlaneCircle_planeComparison hx (by simp)]
    rw [sub_self, map_zero]
    rfl
  · intro y hy z hz
    have hy' : dist y x < 100 := by
      change (1 : ℝ)⁻¹ * dist y x < (1 / 100 : ℝ)⁻¹ at hy
      norm_num at hy
      exact hy
    have hz' : dist z x < 100 := by
      change (1 : ℝ)⁻¹ * dist z x < (1 / 100 : ℝ)⁻¹ at hz
      norm_num at hz
      exact hz
    change |dist (planeComparisonMap edgePlaneCircleQ 0 x 100000000 1 y)
      (planeComparisonMap edgePlaneCircleQ 0 x 100000000 1 z) -
        (1 : ℝ)⁻¹ * dist y z| ≤ 1 / 100
    rw [edgePlaneCircle_planeComparison hx (by linarith),
      edgePlaneCircle_planeComparison hx (by linarith),
      planeReferenceIsometry.symm.isometry.dist_eq]
    simp only [inv_one, one_mul, dist_sub_right]
    exact abs_le.mpr ⟨by linarith [edgePlaneCircle_dist_upper y z],
      by linarith [edgePlaneCircle_plane_le y z]⟩
  · intro v hv
    let y : M := (x.1 + planeReferenceIsometry v, x.2)
    have hd : dist y x = ‖v‖ := by
      rw [edgePlaneCircle_sameCircle]
      simp only [dist_eq_norm, add_sub_cancel_left, planeReferenceIsometry.norm_map]
    have hy : dist y x < 100 := by
      change dist v 0 < (1 / 100 : ℝ)⁻¹ - 1 / 100 at hv
      rw [dist_zero_right] at hv
      rw [hd]
      norm_num at hv
      linarith
    have he : planeComparisonMap edgePlaneCircleQ 0 x 100000000 1 y = v := by
      rw [edgePlaneCircle_planeComparison hx (by linarith)]
      change planeReferenceIsometry.symm
        ((x.1 + planeReferenceIsometry v) - x.1) = v
      rw [add_sub_cancel_left, planeReferenceIsometry.symm_apply_apply]
    have hm : v ∈ (planeComparisonMap edgePlaneCircleQ 0 x 100000000 1) ''
        @ball M
          ((edgePlaneCircleIntrinsicMetric.rescale (1 : ℝ)⁻¹ (by norm_num))).toPseudoMetricSpace
          x (1 / 100 : ℝ)⁻¹ := by
      refine ⟨y, ?_, he⟩
      change (1 : ℝ)⁻¹ * dist y x < (1 / 100 : ℝ)⁻¹
      norm_num
      exact hy
    rw [infDist_zero_of_mem hm]
    norm_num

private theorem edgePlaneCircle_coordinate_derivative (j : Fin 2) (x : M)
    (v : TangentSpace IP x) :
    mvfderiv (I := IP) (fun y : M => y.1 j) x v = v.1 j := by
  let ℓ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj j
  change mfderiv IP 𝓘(ℝ, ℝ) (ℓ ∘ Prod.fst) x v = v.1 j
  rw [mfderiv_comp_apply x ℓ.differentiableAt.mdifferentiableAt mdifferentiableAt_fst,
    mfderiv_fst, mfderiv_eq_fderiv, ℓ.fderiv]
  rfl

private theorem edgePlaneCircle_coordinate_geodesic (j : Fin 2) (x : M)
    (v : TangentSpace IP x) (t : ℝ) :
    (Exponential.intrinsicGeodesic edgePlaneCircleMetric edgePlaneCircleMetricNorm
      x v t).1 j = x.1 j + t * v.1 j := by
  have hH (p : M) : Operator.hessFun edgePlaneCircleMetric
      (fun y : M => y.1 j) p = 0 :=
    hessFun_euclideanProduct_coordinate smallFlatCircleMetric (EuclideanSpace.proj j) p
  have h := DifferentialGeometry.Geometry.Topology.affineFunction_comp_intrinsicGeodesic
    edgePlaneCircleMetric edgePlaneCircleMetricNorm (edgePlaneCircle_coordinate_smooth j)
    hH x v t
  rw [edgePlaneCircle_coordinate_derivative] at h
  exact h

private theorem edgePlaneCircle_plane_geodesic (x : M) (v : TangentSpace IP x) (t : ℝ) :
    (Exponential.intrinsicGeodesic edgePlaneCircleMetric edgePlaneCircleMetricNorm
      x v t).1 = x.1 + t • v.1 := by
  apply PiLp.ext
  intro j
  exact edgePlaneCircle_coordinate_geodesic j x v t

private theorem edgePlaneCircle_disk (x : M) (hx : x ∈ ball (0 : M) 300000000) :
    x ∈ edgeDiskDomain (0 : M) 100000000 (fun y => y.val.1 0)
      edgePlaneCircleHeight edgePlaneCircleRho := by
  have h0 := edgePlaneCircle_coordinate_le x (0 : M) 0
  have h1 := edgePlaneCircle_coordinate_le x (0 : M) 1
  norm_num at h0 h1
  change dist x 0 < 300000000 at hx
  have hh : edgePlaneCircleHeight x ≤ dist x 0 :=
    max_le (le_abs_self _ |>.trans h1) dist_nonneg
  refine ⟨(by change dist x 0 < 100 * 100000000; linarith), ?_, ?_⟩
  · change |x.1 0| < 4 * 100000000
    linarith
  · change edgePlaneCircleHeight x / 1 ≤ 4 * 100000000
    rw [div_one]
    linarith

private theorem edgePlaneCircle_cutoff (x : M) (hx : x ∈ ball (0 : M) 300000000) :
    ((Subtype.val : ball (0 : M) (100 * 100000000) → M).extend
      (fun y => DifferentialGeometry.Analysis.edgeCoordinateProfile
          (y.val.1 0 / 100000000) *
        DifferentialGeometry.Analysis.edgeHeightProfile
          (edgePlaneCircleHeight y.val / (100000000 * edgePlaneCircleRho y.val))) 0) x = 1 := by
  change dist x 0 < 300000000 at hx
  have hxD : x ∈ ball (0 : M) (100 * 100000000) := by
    change dist x 0 < 100 * 100000000
    linarith
  have he := Function.Injective.extend_apply
    (Subtype.val_injective : Function.Injective
      (Subtype.val : ball (0 : M) (100 * 100000000) → M))
    (fun y => DifferentialGeometry.Analysis.edgeCoordinateProfile
        (y.val.1 0 / 100000000) *
      DifferentialGeometry.Analysis.edgeHeightProfile
        (edgePlaneCircleHeight y.val / (100000000 * edgePlaneCircleRho y.val))) 0 ⟨x, hxD⟩
  change _ = 1
  rw [he]
  have h0 := edgePlaneCircle_coordinate_le x (0 : M) 0
  have h1 := edgePlaneCircle_coordinate_le x (0 : M) 1
  norm_num at h0 h1
  change dist x 0 < 300000000 at hx
  have hh : edgePlaneCircleHeight x ≤ dist x 0 :=
    max_le (le_abs_self _ |>.trans h1) dist_nonneg
  have hp := DifferentialGeometry.Analysis.edgeProfiles_plateaus
    (x := x.1 0 / 100000000) |>.1
  rw [hp (by constructor <;> nlinarith [neg_abs_le (x.1 0), le_abs_self (x.1 0)]),
    edgePlaneCircleRho]
  change 1 * DifferentialGeometry.Analysis.descendingIntervalProfile 8 9
    (edgePlaneCircleHeight x / (100000000 * 1)) = 1
  rw [DifferentialGeometry.Analysis.descendingIntervalProfile_one (by norm_num)
    (by nlinarith)]
  exact one_mul 1

private theorem edgePlaneCircle_collar (x : M)
    (hx : x ∈ ball (0 : M) 10000000000)
    (hl : 10000000 ≤ edgePlaneCircleHeight x) :
    ContMDiffOn IP (𝓡 2) ∞ edgePlaneCircleJ (ball x 300) ∧
      (∀ y ∈ ball x 100, Function.Surjective (mvfderiv (I := IP) edgePlaneCircleJ y)) ∧
      (∀ y ∈ ball x 100, ∀ z ∈ ball x 100,
        ‖edgePlaneCircleJ y - edgePlaneCircleJ z‖ ≤ (1 + 1 / 100) * dist y z) ∧
      (∀ y ∈ ball x 100, infDist (edgePlaneCircleJ y) (ball (edgePlaneCircleJ x) 100) < 1) ∧
      (∀ v ∈ ball (edgePlaneCircleJ x) 100, ∃ y ∈ ball x 100,
        ‖edgePlaneCircleJ y - v‖ < 1) ∧
      ∀ y ∈ ball x 100, ∀ z ∈ ball x 10000, 1 < dist y z →
        ∀ v : TangentSpace IP y, edgePlaneCircleMetric.inner y v v = 1 →
        Exponential.intrinsicGeodesic edgePlaneCircleMetric edgePlaneCircleMetricNorm
          y v (dist y z) = z →
        ‖mvfderiv (I := IP) edgePlaneCircleJ y v - (dist y z)⁻¹ •
          (planeReferenceIsometry (planeComparisonMap edgePlaneCircleQ 0 x 100000000 1 z) -
            planeReferenceIsometry (planeComparisonMap edgePlaneCircleQ 0 x 100000000 1 y))‖
          < 1 / 100 := by
  have hxpos : 0 < x.1 1 := edgePlaneCircle_positive_buffer hl (by simp)
  have hypos (y : M) (hy : y ∈ ball x 100) : 0 < y.1 1 :=
    edgePlaneCircle_positive_buffer hl (lt_trans hy (by norm_num))
  refine ⟨edgePlaneCircleJ_smooth hl, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    change Function.Surjective (mfderiv IP (𝓡 2) edgePlaneCircleJ y)
    rw [edgePlaneCircleJ_derivative (hypos y hy)]
    intro v
    exact ⟨(v, 0), rfl⟩
  · intro y hy z hz
    rw [edgePlaneCircleJ_eq (hypos y hy), edgePlaneCircleJ_eq (hypos z hz)]
    have hd := edgePlaneCircle_plane_le y z
    rw [dist_eq_norm] at hd
    nlinarith [dist_nonneg (x := y) (y := z)]
  · intro y hy
    have hm : edgePlaneCircleJ y ∈ ball (edgePlaneCircleJ x) 100 := by
      rw [edgePlaneCircleJ_eq (hypos y hy), edgePlaneCircleJ_eq hxpos]
      exact (edgePlaneCircle_plane_le y x).trans_lt hy
    rw [infDist_zero_of_mem hm]
    norm_num
  · intro v hv
    rw [edgePlaneCircleJ_eq hxpos] at hv
    let y : M := (v, x.2)
    have hy : y ∈ ball x 100 := by
      change dist (v, x.2) (x.1, x.2) < 100
      rw [edgePlaneCircle_sameCircle]
      exact hv
    refine ⟨y, hy, ?_⟩
    rw [edgePlaneCircleJ_eq (hypos y hy)]
    change ‖v - v‖ < 1
    norm_num
  · intro y hy z hz hd v _hv hgeo
    have hp := edgePlaneCircle_plane_geodesic y v (dist y z)
    rw [hgeo] at hp
    have hdJ : mvfderiv (I := IP) edgePlaneCircleJ y v = v.1 := by
      change mfderiv IP (𝓡 2) edgePlaneCircleJ y v = v.1
      rw [edgePlaneCircleJ_derivative (hypos y hy)]
      rfl
    rw [hdJ, edgePlaneCircle_planeComparison hx hz,
      edgePlaneCircle_planeComparison hx (lt_trans hy (by norm_num)),
      planeReferenceIsometry.apply_symm_apply, planeReferenceIsometry.apply_symm_apply]
    rw [sub_sub_sub_cancel_right]
    change ‖v.1 - (dist y z)⁻¹ • (z.1 - y.1)‖ < 1 / 100
    rw [hp, add_sub_cancel_left, inv_smul_smul₀ (by linarith : dist y z ≠ 0)]
    norm_num

private def edgePlaneCircleLineOrigin :
    {x : M // Comparison.Toponogov.lineCoordinate edgePlaneCircleLine x = 0} :=
  ⟨0, edgePlaneCircle_lineCoordinate 0⟩

private theorem edgePlaneCircleSplitting_origin :
    edgePlaneCircleSplitting (0 : M) =
      WithLp.toLp 2 ((0 : ℝ), edgePlaneCircleLineOrigin) := by
  have h := Comparison.Toponogov.lineSplitting_apply_line
    (model_lcp04_clauses_of_sectional_nonneg edgePlaneCircleMetric
      edgePlaneCircleMetricNorm edgePlaneCircle_sectional).2.1
    edgePlaneCircleLine_isometry
    (model_lcp04_clauses_of_sectional_nonneg edgePlaneCircleMetric
      edgePlaneCircleMetricNorm edgePlaneCircle_sectional).2.2 0
  have hzero : edgePlaneCircleLine 0 = (0 : M) := by
    apply Prod.ext
    · apply PiLp.ext
      intro j
      simp [edgePlaneCircleLine, PiLp.single_apply]
    · rfl
  simpa only [hzero, edgePlaneCircleSplitting, edgePlaneCircleLineOrigin] using h

noncomputable def edgePlaneCircleChart :
    EdgeChart edgePlaneCircleMetric edgePlaneCircleMetricNorm 100000000
      (1 / 100) (1 / 100) (1 / 2) (1 / 100) (1 / 100)
      edgePlaneCircleHalfspace edgePlaneCircleRho edgePlaneCircleHeight where
  center := 0
  rho_center := rfl
  center_mem := by simp [edgePlaneCircleHalfspace]
  Y := {x : M // Comparison.Toponogov.lineCoordinate edgePlaneCircleLine x = 0}
  instY := inferInstance
  q := edgePlaneCircleLineOrigin
  split := edgePlaneCircleSplitting.toKleinerLottApprox edgePlaneCircleSplitting_origin
    (by norm_num) (by norm_num)
  Qn := edgePlaneCircleQ
  Qn_fst z := (edgePlaneCircleQ_fst z).trans (edgePlaneCircleSplitting_fst z).symm
  coord := fun p => p.1 0
  domain := univ
  isOpen_domain := isOpen_univ
  closedBall_subset_domain := subset_univ _
  contMDiffOn_coord := (edgePlaneCircle_coordinate_smooth 0).contMDiffOn
  coord_center := rfl
  lipschitz := (edgePlaneCircle_coordinate_lipschitz 0).weaken (by norm_num)
  value x _hx := by
    change |x.1 0 - (edgePlaneCircleSplitting x).fst| < (1 / 100 : ℝ) * 100000000
    rw [edgePlaneCircleSplitting_fst]
    norm_num
  test x _hx y _hy hd v _hv hgeo := by
    change |mvfderiv (I := IP) (fun p : M => p.1 0) x v -
      ((edgePlaneCircleSplitting y).fst - (edgePlaneCircleSplitting x).fst) / dist x y| <
        (1 / 100 : ℝ)
    rw [edgePlaneCircle_coordinate_derivative, edgePlaneCircleSplitting_fst,
      edgePlaneCircleSplitting_fst]
    have h := edgePlaneCircle_coordinate_geodesic 0 x v (dist x y)
    rw [hgeo] at h
    have he : (y.1 0 - x.1 0) / dist x y = v.1 0 := by
      apply (div_eq_iff (by linarith : dist x y ≠ 0)).2
      linarith
    rw [he]
    norm_num
  disk_subset := by
    intro x hx
    exact edgePlaneCircle_disk x (by norm_num at hx ⊢; exact hx)
  cutoff_eq_one := by
    intro x hx
    exact edgePlaneCircle_cutoff x (by norm_num at hx ⊢; exact hx)
  collar x hx _hcoord hl _hh := by
    have hx' : x ∈ ball (0 : M) 10000000000 := by norm_num at hx ⊢; exact hx
    have hl' : 10000000 ≤ edgePlaneCircleHeight x := by
      change (100000000 : ℝ) / 10 ≤ edgePlaneCircleHeight x / 1 at hl
      norm_num at hl
      exact hl
    refine ⟨by norm_num [edgePlaneCircleRho], ?_, ?_⟩
    · exact ⟨edgePlaneCirclePlaneKL x hx', fun _y => rfl⟩
    · have h := edgePlaneCircle_collar x hx' hl'
      simpa only [edgePlaneCircleJ, edgePlaneCircleRho, mul_one, div_one, one_smul,
        show (100 : ℝ) * (1 / 100) = 1 by norm_num,
        show (100 : ℝ) / (1 / 100) = 10000 by norm_num] using h

theorem exists_edgePlaneCircleChart :
    ∃ P : EdgeChart edgePlaneCircleMetric edgePlaneCircleMetricNorm 100000000
      (1 / 100) (1 / 100) (1 / 2) (1 / 100) (1 / 100)
      edgePlaneCircleHalfspace edgePlaneCircleRho edgePlaneCircleHeight,
      P.center = 0 ∧ (∀ x, P.coord x = x.1 0) ∧
      (∀ x, P.Qn x = planeReferenceIsometry.symm x.1) ∧
      (∀ x, edgePlaneCircleHeight x = infDist x edgePlaneCircleHalfspace) ∧
      ∃ x ∈ ball P.center (100 * 100000000),
        |P.coord x| ≤ 10 * 100000000 ∧
        100000000 / 10 ≤ edgePlaneCircleHeight x / edgePlaneCircleRho x ∧
        edgePlaneCircleHeight x / edgePlaneCircleRho x ≤ 10 * 100000000 := by
  refine ⟨edgePlaneCircleChart, rfl, fun _x => rfl, fun _x => rfl,
    edgePlaneCircleHeight_infDist, ?_⟩
  let x : M := (PiLp.single 2 1 (100000000 : ℝ), 0)
  have hd : dist x (0 : M) = 100000000 := by
    change dist (PiLp.single 2 1 (100000000 : ℝ), (0 : AddCircle (1 : ℝ)))
      ((0 : EuclideanSpace ℝ (Fin 2)), 0) = 100000000
    rw [edgePlaneCircle_sameCircle, dist_zero_right, PiLp.norm_single, Real.norm_eq_abs]
    norm_num
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · change dist x 0 < 100 * 100000000
    rw [hd]
    norm_num
  · norm_num [edgePlaneCircleChart, x, PiLp.single_apply]
  · norm_num [edgePlaneCircleHeight, edgePlaneCircleRho, x, PiLp.single_apply]
  · norm_num [edgePlaneCircleHeight, edgePlaneCircleRho, x, PiLp.single_apply]

end DifferentialGeometry.Geometry.Collapse
