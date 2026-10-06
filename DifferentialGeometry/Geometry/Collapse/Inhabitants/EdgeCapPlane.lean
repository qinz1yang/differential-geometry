import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapRadial
import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapHeight
import DifferentialGeometry.Geometry.Metric.Approximation.PlaneReferenceChart
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition
set_option autoImplicit false
noncomputable section
open Bundle Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open DifferentialGeometry.Geometry.Collapse.EdgeCapDistance
open DifferentialGeometry.Geometry.Collapse.EdgeCapCarrier
open DifferentialGeometry.Geometry.Collapse.EdgeCapSplitting
open DifferentialGeometry.Geometry.Collapse.EdgeCapRadial
open DifferentialGeometry.Geometry.Collapse.EdgeCapHeight
open scoped Manifold ContDiff Topology InnerProductSpace
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] capExampleSigma capExampleMetricSpace capExampleEDist
  capExampleDist capExampleUniform capExampleEMetric capExamplePseudo capExampleBundle
  capExampleRiemannian capExampleContinuous capExampleComplete capExampleProper capExampleDimension
  capSurfaceSigma capSurfaceMetricSpace capSurfaceEDist capSurfaceDist
  capSurfaceUniform capSurfaceEMetric capSurfacePseudo
open DifferentialGeometry.PDE.RicciFlow.StandardCap
namespace DifferentialGeometry.Geometry.Collapse.EdgeCapPlane

def physicalRadius (z : E2) : ℝ := capExampleEpsilon * ‖z‖

def physicalPlane (x : E3) : WithLp 2 (ℝ × ℝ) :=
  WithLp.toLp 2 (capThreeCoord x, physicalRadius (capProductCoordinates.symm x).2)

theorem physicalRadius_distance_zero (z : E2) : dist z 0 = physicalRadius z := by
  change (riemannianEDistOf
    (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos) z 0).toReal = _
  rw [riemannianEDistOf_comm, scaledCap_edist_zero,
    ENNReal.toReal_ofReal (mul_nonneg capExampleEpsilon_pos.le (norm_nonneg z))]
  rfl

theorem physicalRadius_lipschitz (z w : E2) : |physicalRadius z - physicalRadius w| ≤ dist z w := by
  have h := abs_dist_sub_le z w (0 : E2)
  rwa [physicalRadius_distance_zero, physicalRadius_distance_zero] at h

theorem physicalPlane_physical (a : ℝ × E2) :
    physicalPlane (capProductCoordinates a) = WithLp.toLp 2 (a.1, physicalRadius a.2) := by
  simp only [physicalPlane, capThreeCoord, Diffeomorph.symm_apply_apply]

theorem realPlane_distance (a b : ℝ × ℝ) :
    dist (WithLp.toLp 2 a) (WithLp.toLp 2 b) =
      Real.sqrt ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := by
  rw [WithLp.prod_dist_eq_add (by norm_num : 0 < (2 : ENNReal).toReal)]
  norm_num [Real.sqrt_eq_rpow, Real.rpow_two, Real.dist_eq, sq_abs]

theorem physical_distance_formula (a b : ℝ × E2) :
    dist (capProductCoordinates a) (capProductCoordinates b) =
      Real.sqrt ((a.1 - b.1) ^ 2 + dist a.2 b.2 ^ 2) := by
  rw [physical_L2_distance,
    WithLp.prod_dist_eq_add (by norm_num : 0 < (2 : ENNReal).toReal)]
  norm_num [Real.sqrt_eq_rpow, Real.rpow_two, Real.dist_eq, sq_abs]

theorem physicalPlane_nonexpanding (x y : E3) :
    dist (physicalPlane x) (physicalPlane y) ≤ dist x y := by
  obtain ⟨a, rfl⟩ := capProductCoordinates.surjective x
  obtain ⟨b, rfl⟩ := capProductCoordinates.surjective y
  change dist (physicalPlane (capProductCoordinates a))
    (physicalPlane (capProductCoordinates b)) ≤
      dist (capProductCoordinates a) (capProductCoordinates b)
  rw [physicalPlane_physical, physicalPlane_physical, realPlane_distance, physical_distance_formula]
  apply Real.sqrt_le_sqrt
  have h := physicalRadius_lipschitz a.2 b.2
  have hs : (physicalRadius a.2 - physicalRadius b.2) ^ 2 ≤ dist a.2 b.2 ^ 2 := by
    nlinarith [abs_nonneg (physicalRadius a.2 - physicalRadius b.2),
      (dist_nonneg : (0 : ℝ) ≤ dist a.2 b.2),
      sq_abs (physicalRadius a.2 - physicalRadius b.2)]
  linarith


theorem physicalRadius_ray (θ : AddCircle (1 : ℝ)) (r : ℝ) (hr : 0 ≤ r) :
    physicalRadius (capRayPoint θ r) = r := by
  rw [physicalRadius, capRayPoint_norm θ r hr]
  field_simp [capExampleEpsilon_pos.ne']

def planeRay (θ : AddCircle (1 : ℝ)) (a : ℝ × ℝ) : E3 :=
  capProductCoordinates (a.1, capRayPoint θ a.2)

theorem physicalPlane_ray (θ : AddCircle (1 : ℝ)) (a : ℝ × ℝ) (ha : 0 ≤ a.2) :
    physicalPlane (planeRay θ a) = WithLp.toLp 2 a := by
  rw [planeRay, physicalPlane_physical, physicalRadius_ray θ a.2 ha]

theorem planeRay_distance (θ : AddCircle (1 : ℝ)) (a b : ℝ × ℝ)
    (ha : 0 ≤ a.2) (hb : 0 ≤ b.2) :
    dist (planeRay θ a) (planeRay θ b) = dist (WithLp.toLp 2 a) (WithLp.toLp 2 b) := by
  rw [planeRay, planeRay, physical_distance_formula,
    capRayPoint_distance θ a.2 b.2 ha hb, realPlane_distance, sq_abs]


theorem planeRay_fibre_distance (θ η : AddCircle (1 : ℝ)) (a : ℝ × ℝ)
    (hend : transitionEnd ≤ capExampleEpsilon⁻¹ * a.2) :
    dist (planeRay θ a) (planeRay η a) ≤ 1 / 10000 := by
  rw [planeRay, planeRay, physical_distance_formula]
  simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (dist_nonneg :
      (0 : ℝ) ≤ dist (capRayPoint θ a.2) (capRayPoint η a.2))]
  exact capRayPoint_fibre_distance a.2 hend θ η

theorem planeRay_distance_upper (θ η : AddCircle (1 : ℝ)) (a b : ℝ × ℝ)
    (ha : 0 ≤ a.2) (hb : 0 ≤ b.2)
    (hend : transitionEnd ≤ capExampleEpsilon⁻¹ * b.2) :
    dist (planeRay θ a) (planeRay η b) ≤
      dist (WithLp.toLp 2 a) (WithLp.toLp 2 b) + 1 / 10000 := by
  have h := dist_triangle (planeRay θ a) (planeRay θ b) (planeRay η b)
  rw [planeRay_distance θ a b ha hb] at h
  exact h.trans (add_le_add le_rfl (planeRay_fibre_distance θ η b hend))


theorem physical_positive_ray (x : E3)
    (hx : (capProductCoordinates.symm x).2 ≠ 0) :
    ∃ θ : AddCircle (1 : ℝ), ∃ a : ℝ × ℝ,
      0 < a.2 ∧ x = planeRay θ a ∧ physicalPlane x = WithLp.toLp 2 a := by
  obtain ⟨θ, r, hr, he, hp⟩ :=
    capRayPoint_positive_cover (capProductCoordinates.symm x).2 hx
  let a : ℝ × ℝ := ((capProductCoordinates.symm x).1, r)
  have hxa : x = planeRay θ a := by
    simp only [planeRay, a, hp, Prod.mk.eta, Diffeomorph.apply_symm_apply]
  exact ⟨θ, a, hr, hxa, hxa ▸ physicalPlane_ray θ a hr.le⟩

theorem physicalPlane_distortion_rays (θ η : AddCircle (1 : ℝ)) (a b : ℝ × ℝ)
    (ha : 0 ≤ a.2) (hb : 0 ≤ b.2)
    (hend : transitionEnd ≤ capExampleEpsilon⁻¹ * b.2) :
    |dist (physicalPlane (planeRay θ a)) (physicalPlane (planeRay η b)) -
      dist (planeRay θ a) (planeRay η b)| ≤ 1 / 10000 := by
  have hl := physicalPlane_nonexpanding (planeRay θ a) (planeRay η b)
  have hu := planeRay_distance_upper θ η a b ha hb hend
  rw [physicalPlane_ray θ a ha, physicalPlane_ray η b hb] at hl ⊢
  rw [abs_of_nonpos (sub_nonpos.mpr hl)]
  linarith


theorem physicalPlane_ball_cover_ray (θ : AddCircle (1 : ℝ)) (a : ℝ × ℝ)
    (ha : 0 ≤ a.2) (R : ℝ) (y : WithLp 2 (ℝ × ℝ))
    (hy : 0 ≤ (WithLp.ofLp y).2)
    (hball : dist y (physicalPlane (planeRay θ a)) < R) :
    ∃ z : E3, z ∈ Metric.ball (planeRay θ a) R ∧ physicalPlane z = y := by
  refine ⟨planeRay θ (WithLp.ofLp y), ?_, ?_⟩
  · rw [Metric.mem_ball, planeRay_distance θ (WithLp.ofLp y) a hy ha]
    simpa only [WithLp.toLp_ofLp, physicalPlane_ray θ a ha] using hball
  · rw [physicalPlane_ray θ (WithLp.ofLp y) hy, WithLp.toLp_ofLp]


theorem physicalPlane_ball_cover (θ : AddCircle (1 : ℝ)) (a : ℝ × ℝ)
    (ha : 0 ≤ a.2) (R : ℝ) (hR : R ≤ a.2) (y : WithLp 2 (ℝ × ℝ))
    (hball : dist y (physicalPlane (planeRay θ a)) < R) :
    ∃ z : E3, z ∈ Metric.ball (planeRay θ a) R ∧ physicalPlane z = y := by
  have hc := WithLp.dist_snd_le y (WithLp.toLp 2 a)
  rw [physicalPlane_ray θ a ha] at hball
  have hy : 0 ≤ (WithLp.ofLp y).2 := by
    change |(WithLp.ofLp y).2 - a.2| ≤ dist y (WithLp.toLp 2 a) at hc
    have hm := neg_abs_le ((WithLp.ofLp y).2 - a.2)
    linarith
  exact physicalPlane_ball_cover_ray θ a ha R y hy
    (by simpa only [physicalPlane_ray θ a ha] using hball)


theorem physicalPlane_distortion (x y : E3)
    (hx : (capProductCoordinates.symm x).2 ≠ 0)
    (hy : (capProductCoordinates.symm y).2 ≠ 0)
    (hend : transitionEnd ≤ capExampleEpsilon⁻¹ *
      physicalRadius (capProductCoordinates.symm y).2) :
    |dist (physicalPlane x) (physicalPlane y) - dist x y| ≤ 1 / 10000 := by
  obtain ⟨θ, a, ha, hxa, hQa⟩ := physical_positive_ray x hx
  obtain ⟨η, b, hb, hyb, hQb⟩ := physical_positive_ray y hy
  have hr : physicalRadius (capProductCoordinates.symm y).2 = b.2 := by
    rw [hyb]
    simp only [planeRay, Diffeomorph.symm_apply_apply]
    exact physicalRadius_ray η b.2 hb.le
  rw [hr] at hend
  rw [hxa, hyb]
  exact physicalPlane_distortion_rays θ η a b ha.le hb.le hend


def axisRadius (x : E3) : ℝ := physicalRadius (capProductCoordinates.symm x).2

theorem axisRadius_lipschitz (x y : E3) : |axisRadius x - axisRadius y| ≤ dist x y := by
  have h := WithLp.dist_snd_le (physicalPlane x) (physicalPlane y)
  change |axisRadius x - axisRadius y| ≤ dist (physicalPlane x) (physicalPlane y) at h
  exact h.trans (physicalPlane_nonexpanding x y)

theorem axisRadius_ne_zero {x : E3} (hx : 0 < axisRadius x) :
    (capProductCoordinates.symm x).2 ≠ 0 := by
  intro hz
  simp only [axisRadius, physicalRadius, hz, norm_zero, mul_zero] at hx
  exact (lt_irrefl 0 hx)

theorem physicalPlane_ball_distortion (x : E3) (R : ℝ)
    (hx : R + capExampleEpsilon * transitionEnd < axisRadius x)
    (y z : E3) (hy : y ∈ Metric.ball x R) (hz : z ∈ Metric.ball x R) :
    |dist (physicalPlane y) (physicalPlane z) - dist y z| ≤ 1 / 10000 := by
  have bound (w : E3) (hw : w ∈ Metric.ball x R) :
      capExampleEpsilon * transitionEnd < axisRadius w := by
    have hl := axisRadius_lipschitz x w
    have hm := le_abs_self (axisRadius x - axisRadius w)
    change dist w x < R at hw
    rw [dist_comm w x] at hw
    linarith
  have hyb := bound y hy
  have hzb := bound z hz
  have hypos : 0 < axisRadius y := lt_of_le_of_lt
    (mul_nonneg capExampleEpsilon_pos.le transitionEnd_pos.le) hyb
  have hzpos : 0 < axisRadius z := lt_of_le_of_lt
    (mul_nonneg capExampleEpsilon_pos.le transitionEnd_pos.le) hzb
  apply physicalPlane_distortion y z (axisRadius_ne_zero hypos) (axisRadius_ne_zero hzpos)
  change transitionEnd ≤ capExampleEpsilon⁻¹ * axisRadius z
  apply (le_inv_mul_iff₀ capExampleEpsilon_pos).mpr
  exact hzb.le


def centredPlane (x y : E3) : WithLp 2 (ℝ × ℝ) := physicalPlane y - physicalPlane x

theorem centredPlane_ball_cover (x : E3) (R : ℝ) (hR : 0 < R)
    (hx : R ≤ axisRadius x) (v : WithLp 2 (ℝ × ℝ)) (hv : dist v 0 < R) :
    ∃ z : E3, z ∈ Metric.ball x R ∧ centredPlane x z = v := by
  have hpos : 0 < axisRadius x := lt_of_lt_of_le hR hx
  obtain ⟨θ, a, ha, hxa, hQa⟩ := physical_positive_ray x (axisRadius_ne_zero hpos)
  have hrad : axisRadius x = a.2 := by
    rw [hxa]
    simp only [axisRadius, planeRay, Diffeomorph.symm_apply_apply]
    exact physicalRadius_ray θ a.2 ha.le
  obtain ⟨z, hz, he⟩ := physicalPlane_ball_cover θ a ha.le R (hrad ▸ hx)
    (physicalPlane x + v) (by
      rw [← hxa]
      simpa only [dist_eq_norm, add_sub_cancel_left, sub_zero] using hv)
  refine ⟨z, hxa ▸ hz, ?_⟩
  rw [centredPlane, he, add_sub_cancel_left]


noncomputable def actualPlaneKL (x : E3)
    (hx : 100 + capExampleEpsilon * transitionEnd < axisRadius x) :
    GC.MetricGeometry.KleinerLottApprox x (0 : WithLp 2 (ℝ × ℝ)) (1 / 100) := by
  refine ⟨by norm_num, by norm_num, centredPlane x, ?_, ?_, ?_⟩
  · exact sub_self _
  · intro y hy z hz
    have hy' : y ∈ Metric.ball x 100 := by norm_num at hy; exact hy
    have hz' : z ∈ Metric.ball x 100 := by norm_num at hz; exact hz
    have hd := physicalPlane_ball_distortion x 100 hx y z hy' hz'
    change |dist (physicalPlane y - physicalPlane x)
      (physicalPlane z - physicalPlane x) - dist y z| ≤ 1 / 100
    rw [dist_sub_right]
    linarith
  · intro v hv
    have hrad : 100 ≤ axisRadius x := by
      have hp := mul_pos capExampleEpsilon_pos transitionEnd_pos
      linarith
    have hv' : dist v 0 < 100 := by
      rw [dist_zero_right]
      norm_num at hv
      linarith
    obtain ⟨z, hz, he⟩ := centredPlane_ball_cover x 100 (by norm_num) hrad v hv'
    have hm : v ∈ (centredPlane x) '' Metric.ball x (1 / 100 : ℝ)⁻¹ := by
      refine ⟨z, ?_, he⟩
      norm_num
      exact hz
    rw [Metric.infDist_zero_of_mem hm]
    norm_num


theorem planeComparison_local (p x y : E3) (Δ : ℝ) (hΔ : 1 ≤ Δ)
    (hx : x ∈ Metric.ball p (100 * Δ)) (hy : y ∈ Metric.ball x 100) :
    GC.MetricGeometry.planeComparisonMap physicalPlane p x Δ 1 y = centredPlane x y := by
  have hm : y ∈ Metric.ball p (200 * Δ) := by
    have ht := dist_triangle y x p
    change dist x p < 100 * Δ at hx
    change dist y x < 100 at hy
    change dist y p < 200 * Δ
    linarith
  rw [GC.MetricGeometry.planeComparisonMap_of_mem hm, inv_one, one_smul]
  rfl

noncomputable def actualPlaneComparisonKL (p x : E3) (Δ : ℝ) (hΔ : 1 ≤ Δ)
    (hxball : x ∈ Metric.ball p (100 * Δ))
    (hx : 100 + capExampleEpsilon * transitionEnd < axisRadius x) :
    GC.MetricGeometry.KleinerLottApprox x (0 : WithLp 2 (ℝ × ℝ)) (1 / 100) := by
  let K := actualPlaneKL x hx
  refine ⟨by norm_num, by norm_num,
    GC.MetricGeometry.planeComparisonMap physicalPlane p x Δ 1, ?_, ?_, ?_⟩
  · rw [planeComparison_local p x x Δ hΔ hxball (by simp)]
    exact K.basepoint
  · intro y hy z hz
    have hy' : y ∈ Metric.ball x 100 := by norm_num at hy; exact hy
    have hz' : z ∈ Metric.ball x 100 := by norm_num at hz; exact hz
    rw [planeComparison_local p x y Δ hΔ hxball hy',
      planeComparison_local p x z Δ hΔ hxball hz']
    exact K.distortion y hy z hz
  · intro v hv
    have hrad : 100 ≤ axisRadius x := by
      have hp := mul_pos capExampleEpsilon_pos transitionEnd_pos
      linarith
    have hv' : dist v 0 < 100 := by
      rw [dist_zero_right]
      norm_num at hv
      linarith
    obtain ⟨z, hz, he⟩ := centredPlane_ball_cover x 100 (by norm_num) hrad v hv'
    have hm : v ∈ (GC.MetricGeometry.planeComparisonMap physicalPlane p x Δ 1) ''
        Metric.ball x (1 / 100 : ℝ)⁻¹ := by
      refine ⟨z, ?_, ?_⟩
      · norm_num
        exact hz
      · rw [planeComparison_local p x z Δ hΔ hxball hz]
        exact he
    rw [Metric.infDist_zero_of_mem hm]
    norm_num


theorem axisRadius_infDist (x : E3) : axisRadius x = Metric.infDist x capThreeAxis := by
  exact (capExample_axis_infDist x).symm

theorem capF_le_axisRadius (x : E3) : capExampleF x ≤ axisRadius x := by
  exact capCollarHeight_le_radius capExampleEpsilon capExampleEpsilon_pos.le
    (capProductCoordinates.symm x).2

theorem internal_collar_margin (x : E3) (hx : capExampleDelta / 10 ≤ capExampleF x) :
    100 + capExampleEpsilon * transitionEnd < axisRadius x := by
  have hl := capF_le_axisRadius x
  have hp := capExampleEpsilon_pos
  have he := transitionEnd_pos
  have hm := mul_pos hp he
  unfold capExampleDelta at hx
  nlinarith

noncomputable def capCollarPlaneKL (p x : E3)
    (hxball : x ∈ Metric.ball p (100 * capExampleDelta))
    (hx : capExampleDelta / 10 ≤ capExampleF x) :
    GC.MetricGeometry.KleinerLottApprox x (0 : WithLp 2 (ℝ × ℝ)) (1 / 100) :=
  actualPlaneComparisonKL p x capExampleDelta
    (by linarith [capExampleDelta_large]) hxball (internal_collar_margin x hx)


noncomputable def capCollarPlaneKL_native (p x : E3)
    (hxball : x ∈ Metric.ball p (100 * capExampleDelta))
    (hx : capExampleDelta / 10 ≤ capExampleF x) :
    @GC.MetricGeometry.KleinerLottApprox E3 (WithLp 2 (ℝ × ℝ))
      (capExampleMetricSpace.rescale (1 : ℝ)⁻¹ (by norm_num)) inferInstance
      x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) (1 / 100) := by
  have hm : capExampleMetricSpace.rescale (1 : ℝ)⁻¹ (by norm_num) =
      capExampleMetricSpace := by
    simpa using MetricSpace.rescale_one capExampleMetricSpace
  rw [hm]
  exact capCollarPlaneKL p x hxball hx


theorem exists_capCollarPlaneKL_native (p x : E3)
    (hxball : x ∈ Metric.ball p (100 * capExampleDelta))
    (hx : capExampleDelta / 10 ≤ capExampleF x) :
    ∃ Φ : @GC.MetricGeometry.KleinerLottApprox E3 (WithLp 2 (ℝ × ℝ))
      (capExampleMetricSpace.rescale (1 : ℝ)⁻¹ (by norm_num)) inferInstance
      x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) (1 / 100),
    ∀ y : E3, @GC.MetricGeometry.KleinerLottApprox.toFun E3 (WithLp 2 (ℝ × ℝ))
      (capExampleMetricSpace.rescale (1 : ℝ)⁻¹ (by norm_num)) inferInstance
      x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) (1 / 100) Φ y =
      GC.MetricGeometry.planeComparisonMap physicalPlane p x capExampleDelta 1 y := by
  have hm : capExampleMetricSpace.rescale (1 : ℝ)⁻¹ (by norm_num) =
      capExampleMetricSpace := by
    simpa using MetricSpace.rescale_one capExampleMetricSpace
  rw [hm]
  exact ⟨capCollarPlaneKL p x hxball hx, fun _ => rfl⟩


theorem capF_ray (θ : AddCircle (1 : ℝ)) (a : ℝ × ℝ)
    (ha : 0 ≤ a.2) (hend : 9 * capExampleEpsilon ≤ a.2) :
    capExampleF (planeRay θ a) = a.2 := by
  have hn : 9 ≤ ‖capRayPoint θ a.2‖ := by
    rw [capRayPoint_norm θ a.2 ha]
    exact (le_div_iff₀ capExampleEpsilon_pos).mpr hend
  simp only [capExampleF, planeRay, Diffeomorph.symm_apply_apply,
    capCollarHeight, capRadialProfile_linear hn]
  exact physicalRadius_ray θ a.2 ha

def realCollarPoint : E3 := planeRay 0 (0, capExampleDelta / 5)

theorem realCollarPoint_height : capExampleF realCollarPoint = capExampleDelta / 5 := by
  have hd : 0 < capExampleDelta := by linarith [capExampleDelta_large]
  exact capF_ray 0 (0, capExampleDelta / 5) (by positivity)
    (by linarith [capExampleDelta_height_error])

theorem realCollarPoint_nativeKL :
    Nonempty (@GC.MetricGeometry.KleinerLottApprox E3 (WithLp 2 (ℝ × ℝ))
      (capExampleMetricSpace.rescale (1 : ℝ)⁻¹ (by norm_num)) inferInstance
      realCollarPoint (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) (1 / 100)) := by
  have hd : 0 < capExampleDelta := by linarith [capExampleDelta_large]
  exact ⟨capCollarPlaneKL_native realCollarPoint realCollarPoint
    (Metric.mem_ball_self (by positivity)) (by rw [realCollarPoint_height]; linarith)⟩

end DifferentialGeometry.Geometry.Collapse.EdgeCapPlane
