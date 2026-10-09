import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapGeodesic
import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapRankOne
import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapTrivial
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeChart
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeDiskPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeProductModel

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set Metric
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Collapse.EdgeCapCarrier
open DifferentialGeometry.Geometry.Collapse.EdgeCapCylindrical
open DifferentialGeometry.Geometry.Collapse.EdgeCapDistance
open DifferentialGeometry.Geometry.Collapse.EdgeCapGeodesic
open DifferentialGeometry.Geometry.Collapse.EdgeCapHeight
open DifferentialGeometry.Geometry.Collapse.EdgeCapPlane
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open DifferentialGeometry.Geometry.Collapse.EdgeCapRadial
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapRankOne
open DifferentialGeometry
open DifferentialGeometry.Analysis
open GC.MetricGeometry
open scoped Manifold ContDiff Topology InnerProductSpace
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] capExampleSigma capExampleMetricSpace capExampleEDist
  capExampleDist capExampleUniform capExampleEMetric capExamplePseudo capExampleBundle
  capExampleRiemannian capExampleContinuous capExampleComplete capExampleProper capExampleDimension

namespace DifferentialGeometry.Geometry.Collapse.EdgeCapCollarInhabitant

/-- Metric and chart instances for the concrete cap surface. -/
local instance capE2ChartedSpace : ChartedSpace E2 E2 := chartedSpaceSelf E2

/-- Centre of the concrete edge chart. -/
def capChartCenter : E3 := capExampleAxis 0

theorem capChartCenter_coord : capThreeCoord capChartCenter = 0 := by
  simp [capChartCenter, capExampleAxis, capThreeCoord]

theorem capChartCenter_axis : capChartCenter ∈ capThreeAxis := by
  change capProductCoordinates.symm (capExampleAxis 0) ∈ capProductAxis
  simp [capExampleAxis, capProductAxis]

section ChartSplit

/-- Metric and chart instances for the concrete cap surface. -/
local instance capChartSurfaceMetric : MetricSpace E2 :=
  EdgeCapSplitting.capSurfaceMetricSpace
/-- Metric and chart instances for the concrete cap surface. -/
local instance capChartSurfaceEDist : EDist E2 := EdgeCapSplitting.capSurfaceEDist
/-- Metric and chart instances for the concrete cap surface. -/
local instance capChartSurfaceDist : Dist E2 := EdgeCapSplitting.capSurfaceDist
/-- Metric and chart instances for the concrete cap surface. -/
local instance capChartSurfaceUniform : UniformSpace E2 := EdgeCapSplitting.capSurfaceUniform
/-- Metric and chart instances for the concrete cap surface. -/
local instance capChartSurfaceEMetric : PseudoEMetricSpace E2 :=
  EdgeCapSplitting.capSurfaceEMetric
/-- Metric and chart instances for the concrete cap surface. -/
local instance capChartSurfacePseudo : PseudoMetricSpace E2 :=
  EdgeCapSplitting.capSurfacePseudo

/-- Product isometry centred at the collar chart centre. -/
noncomputable def capChartSplitIsometry : E3 ≃ᵢ WithLp 2 (ℝ × E2) :=
  physicalProductIsometry.trans
    ((realShift (capThreeCoord capChartCenter)).withLpProdCongr 2
      (IsometryEquiv.refl E2))

theorem capChartSplitIsometry_center :
    capChartSplitIsometry capChartCenter =
      WithLp.toLp 2 ((0 : ℝ), (capProductCoordinates.symm capChartCenter).2) := by
  apply (WithLp.equiv 2 _).injective
  change ((capProductCoordinates.symm capChartCenter).1 -
    capThreeCoord capChartCenter, (capProductCoordinates.symm capChartCenter).2) =
    (0, (capProductCoordinates.symm capChartCenter).2)
  rw [capThreeCoord, sub_self]

theorem capChartSplitIsometry_fst (x : E3) :
    (capChartSplitIsometry x).fst = capThreeCoord x := by
  have hcenter : (capProductCoordinates.symm capChartCenter).1 = 0 := by
    change capThreeCoord capChartCenter = 0
    exact capChartCenter_coord
  simp [capChartSplitIsometry, physicalProductIsometry, realShift,
    capThreeCoord, hcenter]

end ChartSplit

theorem capThreeCoord_abs_le_dist (x y : E3) :
    |capThreeCoord x - capThreeCoord y| ≤ dist x y := by
  have h := WithLp.dist_fst_le (physicalPlane x) (physicalPlane y)
  change |capThreeCoord x - capThreeCoord y| ≤
    dist (physicalPlane x) (physicalPlane y) at h
  exact h.trans (physicalPlane_nonexpanding x y)

theorem capChartCoord_lipschitz :
    LipschitzWith (Real.toNNReal (1 + 1 / 50)) capThreeCoord := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := capThreeCoord_abs_le_dist x y
  rw [Real.dist_eq]
  calc
    |capThreeCoord x - capThreeCoord y| ≤ dist x y := h
    _ ≤ ↑(Real.toNNReal (1 + 1 / 50)) * dist x y := by
      simp only [Real.coe_toNNReal (1 + 1 / 50) (by norm_num)]
      have hd : 0 ≤ dist x y := dist_nonneg
      nlinarith

/-- Pointed plane approximation at a high radius collar point. -/
noncomputable def capChartPlaneApprox {x : E3}
    (hxcenter : x ∈ ball capChartCenter (100 * capExampleDelta))
    (hxF : capExampleDelta / 10 ≤ capExampleF x) :
    KleinerLottApprox x (0 : WithLp 2 (ℝ × ℝ)) (1 / 100) := by
  let f : E3 → WithLp 2 (ℝ × ℝ) :=
    planeComparisonMap physicalPlane capChartCenter x capExampleDelta 1
  have hR : 100 ≤ axisRadius x := by
    have haxis := hxF.trans (capF_le_axisRadius x)
    have hΔ := capExampleDelta_large
    nlinarith
  refine ⟨by norm_num, by norm_num, f, ?_, ?_, ?_⟩
  · have hself := native_comparison_buffer capChartCenter x x hxcenter
      (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 10000))
    simpa [f, centredPlane] using hself
  · intro y hy z hz
    have hy100 : y ∈ ball x 100 := by simpa using hy
    have hz100 : z ∈ ball x 100 := by simpa using hz
    have hywide : y ∈ ball x 10000 :=
      ball_subset_ball (by norm_num) hy100
    have hzw : z ∈ ball x 10000 := ball_subset_ball (by norm_num) hz100
    have hfy := native_comparison_buffer capChartCenter x y hxcenter hywide
    have hfz := native_comparison_buffer capChartCenter x z hxcenter hzw
    have hmargy := collar_ball_margin x y hxF hywide
    have hmargz := collar_ball_margin x z hxF hzw
    have he := capExampleEpsilon_pos
    have ht := PDE.RicciFlow.StandardCap.transitionEnd_pos
    have hprod : 0 ≤ capExampleEpsilon *
        (PDE.RicciFlow.StandardCap.transitionEnd + 9) := by positivity
    have hzy : (capProductCoordinates.symm y).2 ≠ 0 :=
      axisRadius_ne_zero (by nlinarith [hmargy, hprod])
    have hzz : (capProductCoordinates.symm z).2 ≠ 0 :=
      axisRadius_ne_zero (by nlinarith [hmargz, hprod])
    have hend : PDE.RicciFlow.StandardCap.transitionEnd ≤
        capExampleEpsilon⁻¹ * axisRadius z := by
      apply (le_inv_mul_iff₀ capExampleEpsilon_pos).mpr
      nlinarith [hmargz, hprod, mul_pos he ht]
    have hdist := physicalPlane_distortion y z hzy hzz hend
    have htranslate :
        dist (centredPlane x y) (centredPlane x z) =
          dist (physicalPlane y) (physicalPlane z) := by
      simp [centredPlane, dist_eq_norm]
    change |dist (planeComparisonMap physicalPlane capChartCenter x capExampleDelta 1 y)
      (planeComparisonMap physicalPlane capChartCenter x capExampleDelta 1 z) -
      dist y z| ≤ 1 / 100
    rw [hfy, hfz, htranslate]
    have hsmall : (1 / 10000 : ℝ) ≤ 1 / 100 := by norm_num
    exact hdist.trans hsmall
  · intro v hv
    have hv100 : dist v 0 < 100 := by
      have h := hv
      norm_num at h ⊢
      linarith
    obtain ⟨y, hy, hcover⟩ := centredPlane_ball_cover x 100
      (by norm_num) hR v hv100
    have hywide : y ∈ ball x 10000 :=
      ball_subset_ball (by norm_num) hy
    have hmap := native_comparison_buffer capChartCenter x y hxcenter hywide
    have heq : f y = v := by
      change planeComparisonMap physicalPlane capChartCenter x capExampleDelta 1 y = v
      rw [hmap]
      exact hcover
    have hm : v ∈ f '' ball x 100 := ⟨y, hy, heq⟩
    have hball : ball x ((1 / 100 : ℝ)⁻¹) = ball x 100 := by
      congr 1
      norm_num
    rw [hball]
    rw [Metric.infDist_zero_of_mem hm]
    norm_num

/-- Lifted carrier for the cap surface chart. -/
abbrev CapChartY := ULift E2

noncomputable instance capChartYMetric : MetricSpace CapChartY := by
  letI : MetricSpace E2 := EdgeCapSplitting.capSurfaceMetricSpace
  letI : PseudoEMetricSpace E2 := EdgeCapSplitting.capSurfaceEMetric
  letI : PseudoMetricSpace E2 := EdgeCapSplitting.capSurfacePseudo
  infer_instance

section LiftedChartSplit

/-- Metric instances used by the lifted cap chart. -/
local instance capLiftSourceMetric : MetricSpace E2 :=
  EdgeCapSplitting.capSurfaceMetricSpace
/-- Metric instances used by the lifted cap chart. -/
local instance capLiftSourceEDist : EDist E2 := EdgeCapSplitting.capSurfaceEDist
/-- Metric instances used by the lifted cap chart. -/
local instance capLiftSourceDist : Dist E2 := EdgeCapSplitting.capSurfaceDist
/-- Metric instances used by the lifted cap chart. -/
local instance capLiftSourceUniform : UniformSpace E2 := EdgeCapSplitting.capSurfaceUniform
/-- Metric instances used by the lifted cap chart. -/
local instance capLiftSourceEMetric : PseudoEMetricSpace E2 :=
  EdgeCapSplitting.capSurfaceEMetric
/-- Metric instances used by the lifted cap chart. -/
local instance capLiftSourcePseudo : PseudoMetricSpace E2 :=
  EdgeCapSplitting.capSurfacePseudo
/-- Metric instances used by the lifted cap chart. -/
local instance capLiftTargetMetric : MetricSpace CapChartY := capChartYMetric

/-- Auxiliary construction for the concrete edge collar inhabitant. -/
noncomputable def capChartLiftIsometry : E2 ≃ᵢ CapChartY where
  toEquiv := Equiv.ulift.symm
  isometry_toFun := by
    intro x y
    simp

/-- Splits the lifted cap chart at its collar centre. -/
noncomputable def capChartLiftSplitIsometry :
    E3 ≃ᵢ WithLp 2 (ℝ × CapChartY) :=
  physicalProductIsometry.trans
    ((realShift (capThreeCoord capChartCenter)).withLpProdCongr 2
      capChartLiftIsometry)

theorem capChartLiftSplitIsometry_center :
    capChartLiftSplitIsometry capChartCenter =
      WithLp.toLp 2 ((0 : ℝ), ULift.up (capProductCoordinates.symm capChartCenter).2) := by
  apply (WithLp.equiv 2 _).injective
  change ((capProductCoordinates.symm capChartCenter).1 -
    capThreeCoord capChartCenter,
      ULift.up (capProductCoordinates.symm capChartCenter).2) =
    (0, ULift.up (capProductCoordinates.symm capChartCenter).2)
  rw [capThreeCoord, sub_self]

theorem capChartLiftSplitIsometry_fst (x : E3) :
    (capChartLiftSplitIsometry x).fst = capThreeCoord x := by
  have hcenter : (capProductCoordinates.symm capChartCenter).1 = 0 := by
    change capThreeCoord capChartCenter = 0
    exact capChartCenter_coord
  simp [capChartLiftSplitIsometry, physicalProductIsometry, realShift,
    capThreeCoord, hcenter]

end LiftedChartSplit

/-- Scale parameter for the cap chart transition. -/
def capChartB : ℝ := 1 / (200 * capExampleDelta)

theorem capChartB_pos : 0 < capChartB := by
  have hΔ : 0 < capExampleDelta := by
    have h := capExampleDelta_large
    linarith
  unfold capChartB
  positivity

theorem capChartB_lt_one : capChartB < 1 := by
  have hΔ : 0 < capExampleDelta := by
    have h := capExampleDelta_large
    linarith
  unfold capChartB
  apply (div_lt_one (by positivity)).2
  nlinarith [capExampleDelta_large]

/-- Split chart approximation on the cap collar. -/
noncomputable def capChartSplitApprox :
    KleinerLottApprox capChartCenter
      (WithLp.toLp 2 ((0 : ℝ), ULift.up (capProductCoordinates.symm capChartCenter).2))
      capChartB :=
  capChartLiftSplitIsometry.toKleinerLottApprox capChartLiftSplitIsometry_center
    capChartB_pos capChartB_lt_one

theorem capChart_radius_lipschitz_smallball {x : E3}
    (hx : x ∈ ball capChartCenter (3 * capExampleDelta)) :
    |capThreeCoord x| < 3 * capExampleDelta := by
  have hcoord := capThreeCoord_abs_le_dist x capChartCenter
  rw [capChartCenter_coord, sub_zero] at hcoord
  exact hcoord.trans_lt hx

theorem capChart_height_smallball {x : E3}
    (hx : x ∈ ball capChartCenter (3 * capExampleDelta)) :
    capExampleF x < 4 * capExampleDelta := by
  have herror := capExampleF_error x
  have hinf : infDist x capThreeAxis ≤ dist x capChartCenter :=
    infDist_le_dist_of_mem (x := x) capChartCenter_axis
  have hheight := capExampleDelta_height_error
  change dist x capChartCenter < 3 * capExampleDelta at hx
  have herror' : capExampleF x ≤ infDist x capThreeAxis +
      9 * capExampleEpsilon := by
    have h := (abs_le.mp herror).2
    linarith
  calc
    capExampleF x ≤ infDist x capThreeAxis + 9 * capExampleEpsilon := herror'
    _ ≤ dist x capChartCenter + 9 * capExampleEpsilon :=
      by simpa [add_comm] using add_le_add_right hinf (9 * capExampleEpsilon)
    _ < 3 * capExampleDelta + capExampleDelta / 100 := by
      exact add_lt_add hx hheight
    _ < 4 * capExampleDelta := by
      have hΔ := capExampleDelta_large
      nlinarith [capExampleDelta_height_error]

theorem capChart_disk_subset :
    ball capChartCenter (3 * capExampleDelta) ⊆
      edgeDiskDomain capChartCenter capExampleDelta
        (fun x => capThreeCoord x.val) capExampleF (fun _ => 1) := by
  intro x hx
  have h100 : x ∈ ball capChartCenter (100 * capExampleDelta) :=
    ball_subset_ball (by nlinarith [capExampleDelta_large]) hx
  have hcoord := capChart_radius_lipschitz_smallball hx
  have hheight := capChart_height_smallball hx
  change ∃ hx100 : x ∈ ball capChartCenter (100 * capExampleDelta),
    |capThreeCoord x| < 4 * capExampleDelta ∧
      capExampleF x / (fun _ => 1) x ≤ 4 * capExampleDelta
  refine ⟨h100, ?_, ?_⟩
  · exact hcoord.trans (by have hΔ := capExampleDelta_large; nlinarith)
  · simpa using le_of_lt hheight

theorem capChart_cutoff_eq_one :
  EqOn ((Subtype.val : ball capChartCenter (100 * capExampleDelta) → E3).extend
      (fun x => edgeCoordinateProfile (capThreeCoord x.val / capExampleDelta) *
        edgeHeightProfile (capExampleF x.val /
          (capExampleDelta * (fun _ => (1 : ℝ)) x.val))) 0) 1
      (ball capChartCenter (3 * capExampleDelta)) := by
  intro x hx
  have hΔ : 0 < capExampleDelta := by
    have h := capExampleDelta_large
    linarith
  have h100 : x ∈ ball capChartCenter (100 * capExampleDelta) :=
    ball_subset_ball (by nlinarith [capExampleDelta_large]) hx
  have hcoord := capChart_radius_lipschitz_smallball hx
  have hheight := capChart_height_smallball hx
  have hscaled : |capThreeCoord x / capExampleDelta| < 3 := by
    rw [abs_div, abs_of_pos hΔ]
    apply (div_lt_iff₀ hΔ).2
    exact hcoord
  have hcoord_profile :
      edgeCoordinateProfile (capThreeCoord x / capExampleDelta) = 1 := by
    apply edgeProfiles_plateaus.1
    rw [Set.mem_Icc]
    constructor <;> linarith [abs_lt.mp hscaled]
  have hheight_profile :
      edgeHeightProfile (capExampleF x / capExampleDelta) = 1 := by
    rw [edgeHeightProfile, descendingIntervalProfile_one (by norm_num)]
    apply (div_le_iff₀ hΔ).2
    have h := capExampleDelta_large
    nlinarith
  have hext : ((Subtype.val : ball capChartCenter (100 * capExampleDelta) → E3).extend
      (fun y => edgeCoordinateProfile (capThreeCoord y.val / capExampleDelta) *
        edgeHeightProfile (capExampleF y.val /
          (capExampleDelta * (fun _ => (1 : ℝ)) y.val))) 0) x =
      edgeCoordinateProfile (capThreeCoord x / capExampleDelta) *
        edgeHeightProfile (capExampleF x / capExampleDelta) := by
    have hpoint : ((⟨x, h100⟩ : ball capChartCenter
        (100 * capExampleDelta)) : E3) = x := rfl
    rw [← hpoint, Subtype.val_injective.extend_apply]
    simp
  change _ = 1
  rw [hext, hcoord_profile, hheight_profile]
  norm_num

/-- Native two dimensional chart map on the collar. -/
def capChartJ (x : E3) : E2 :=
  edgeReferenceCoordinates ![capThreeCoord, capExampleF] x

theorem capChartJ_eq_actualJ : capChartJ = actualJ := by
  funext x
  rfl

private def rayParametersCLM : E2 →L[ℝ] ℝ × ℝ :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).toContinuousLinearMap.comp
    planeReferenceIsometry.symm.toContinuousLinearMap

/-- Linear parameters for the fixed angle radial ray. -/
def rayParameters (z : E2) : ℝ × ℝ := rayParametersCLM z

private def rayCoordinatesCLM (θ : AddCircle (1 : ℝ)) : E2 →L[ℝ] ℝ × E2 :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (capExampleEpsilon⁻¹ • (capAngle θ).val))).comp rayParametersCLM

/-- Ray with a fixed circle angle in product coordinates. -/
def fixedAngleRay (θ : AddCircle (1 : ℝ)) (z : E2) : E3 :=
  capProductCoordinates (rayCoordinatesCLM θ z)

theorem fixedAngleRay_eq_planeRay (θ : AddCircle (1 : ℝ)) (z : E2) :
    fixedAngleRay θ z = planeRay θ (rayParameters z) := by
  have hsmul (r : ℝ) : r • (capExampleEpsilon⁻¹ • (capAngle θ).val) =
      (r / capExampleEpsilon) • (capAngle θ).val := by
    rw [smul_smul, div_eq_mul_inv]
  change capProductCoordinates
      ((rayParameters z).1,
        (rayParameters z).2 • (capExampleEpsilon⁻¹ • (capAngle θ).val)) =
    planeRay θ (rayParameters z)
  rw [planeRay, EdgeCapRadial.capRayPoint]
  exact congrArg capProductCoordinates (Prod.ext rfl (hsmul _))

theorem fixedAngleRay_contMDiff (θ : AddCircle (1 : ℝ)) :
    ContMDiff (𝓘(ℝ, E2)) (𝓡 3) ∞ (fixedAngleRay θ) := by
  have hlin : ContMDiff (𝓘(ℝ, E2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (rayCoordinatesCLM θ) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (rayCoordinatesCLM θ).contDiff.contMDiff
  change ContMDiff (𝓘(ℝ, E2)) (𝓡 3) ∞
    (fun z => capProductCoordinates (rayCoordinatesCLM θ z))
  exact capProductCoordinates.contMDiff.comp hlin

theorem rayParameter_toLp (z : E2) :
    WithLp.toLp 2 (rayParameters z) = planeReferenceIsometry.symm z := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).injective
  simp [rayParameters, rayParametersCLM]

theorem rayParameter_after_plane (a : ℝ × ℝ) :
    rayParameters (planeReferenceIsometry (WithLp.toLp 2 a)) = a := by
  simp [rayParameters, rayParametersCLM]

theorem rayParameter_roundtrip (z : E2) :
    planeReferenceIsometry (WithLp.toLp 2 (rayParameters z)) = z := by
  rw [rayParameter_toLp, planeReferenceIsometry.apply_symm_apply]

theorem fixedAngleRay_axisRadius (θ : AddCircle (1 : ℝ)) (z : E2)
    (hr : 0 ≤ (rayParameters z).2) :
    axisRadius (fixedAngleRay θ z) = (rayParameters z).2 := by
  rw [fixedAngleRay_eq_planeRay]
  simp only [axisRadius, planeRay, Diffeomorph.symm_apply_apply, physicalRadius]
  rw [capRayPoint_norm θ _ hr]
  field_simp [capExampleEpsilon_pos.ne']

theorem actualJ_fixedAngleRay_of_far (θ : AddCircle (1 : ℝ)) (z : E2)
    (hfar : 9 * capExampleEpsilon ≤ (rayParameters z).2) :
    actualJ (fixedAngleRay θ z) = z := by
  have hε9 : 0 < 9 * capExampleEpsilon :=
    mul_pos (by norm_num) capExampleEpsilon_pos
  have hrad : axisRadius (fixedAngleRay θ z) = (rayParameters z).2 :=
    fixedAngleRay_axisRadius θ z (le_of_lt (lt_of_lt_of_le hε9 hfar))
  calc
    actualJ (fixedAngleRay θ z) =
        planeReferenceIsometry (physicalPlane (fixedAngleRay θ z)) :=
      actualJ_physicalPlane _ (by rw [hrad]; exact hfar)
    _ = planeReferenceIsometry (WithLp.toLp 2 (rayParameters z)) := by
      rw [fixedAngleRay_eq_planeRay,
        physicalPlane_ray θ _ (le_of_lt (lt_of_lt_of_le hε9 hfar))]
    _ = z := rayParameter_roundtrip z

theorem actualJ_fixedAngleRay_eventually (θ : AddCircle (1 : ℝ)) (z₀ : E2)
    (hfar : 9 * capExampleEpsilon < (rayParameters z₀).2) :
    (fun z => actualJ (fixedAngleRay θ z)) =ᶠ[𝓝 z₀] fun z => z := by
  have hcont : Continuous fun z : E2 => (rayParameters z).2 := by
    exact continuous_snd.comp rayParametersCLM.continuous
  have hopen : IsOpen {z : E2 | 9 * capExampleEpsilon < (rayParameters z).2} :=
    isOpen_lt continuous_const hcont
  filter_upwards [hopen.mem_nhds hfar] with z hz
  exact actualJ_fixedAngleRay_of_far θ z (le_of_lt hz)

theorem actualJ_mfderiv_surjective_of_far {x : E3}
    (hfar : 9 * capExampleEpsilon < axisRadius x) :
    Function.Surjective (mfderiv (𝓡 3) (𝓘(ℝ, E2)) actualJ x) := by
  have hε9 : 0 < 9 * capExampleEpsilon :=
    mul_pos (by norm_num) capExampleEpsilon_pos
  have hradius : 0 < axisRadius x := by
    exact hε9.trans hfar
  obtain ⟨θ, a, ha, hxa, hphys⟩ :=
    physical_positive_ray x (axisRadius_ne_zero hradius)
  have hrad : axisRadius x = a.2 := by
    rw [hxa, axisRadius, planeRay]
    simp only [Diffeomorph.symm_apply_apply, physicalRadius]
    rw [capRayPoint_norm θ a.2 ha.le]
    field_simp [capExampleEpsilon_pos.ne']
  have ha9 : 9 * capExampleEpsilon < a.2 := by rw [← hrad]; exact hfar
  have hJexact : actualJ x = planeReferenceIsometry (WithLp.toLp 2 a) := by
    rw [actualJ_physicalPlane x (le_of_lt hfar), hphys]
  let z₀ : E2 := actualJ x
  have hz₀ : rayParameters z₀ = a := by
    change rayParameters (actualJ x) = a
    rw [hJexact]
    exact rayParameter_after_plane a
  have hpoint : fixedAngleRay θ z₀ = x := by
    rw [fixedAngleRay_eq_planeRay, hz₀]
    exact hxa.symm
  have hlocal := actualJ_fixedAngleRay_eventually θ z₀ (by rw [hz₀]; exact ha9)
  have hid := (hasMFDerivAt_id (I := 𝓘(ℝ, E2)) z₀).congr_of_eventuallyEq_abuse hlocal
  have hDlocal :
      mfderiv (𝓘(ℝ, E2)) (𝓘(ℝ, E2))
        (fun z => actualJ (fixedAngleRay θ z)) z₀ =
        ContinuousLinearMap.id ℝ (TangentSpace (𝓡 2) z₀) := hid.mfderiv
  have hchain :
      mfderiv (𝓘(ℝ, E2)) (𝓘(ℝ, E2))
        (fun z => actualJ (fixedAngleRay θ z)) z₀ =
        (mfderiv (𝓡 3) (𝓘(ℝ, E2)) actualJ x).comp
        (mfderiv (𝓘(ℝ, E2)) (𝓡 3) (fixedAngleRay θ) z₀) := by
    change mfderiv (𝓘(ℝ, E2)) (𝓘(ℝ, E2))
      (actualJ ∘ fixedAngleRay θ) z₀ = _
    rw [mfderiv_comp z₀ (actualJ_smooth.mdifferentiableAt (by simp))
      ((fixedAngleRay_contMDiff θ).mdifferentiableAt (by simp)), hpoint]
  have hderivcomp :
      (mfderiv (𝓡 3) (𝓘(ℝ, E2)) actualJ x).comp
        (mfderiv (𝓘(ℝ, E2)) (𝓡 3) (fixedAngleRay θ) z₀) =
        ContinuousLinearMap.id ℝ (TangentSpace (𝓡 2) z₀) := by
    rw [← hchain]
    exact hDlocal
  intro v
  refine ⟨mfderiv (𝓘(ℝ, E2)) (𝓡 3) (fixedAngleRay θ) z₀ v, ?_⟩
  have hv := congrArg
    (fun L : TangentSpace (𝓡 2) z₀ →L[ℝ] TangentSpace (𝓡 2) z₀ => L v)
    hderivcomp
  change (mfderiv (𝓡 3) (𝓘(ℝ, E2)) actualJ x)
    ((mfderiv (𝓘(ℝ, E2)) (𝓡 3) (fixedAngleRay θ) z₀) v) = v at hv
  exact hv

theorem capExample_far_100_margin :
    100 + 9 * capExampleEpsilon < capExampleDelta / 10 := by
  have hΔ := capExampleDelta_large
  have he := capExampleDelta_height_error
  nlinarith

theorem axisRadius_gt_nine_on_100_ball {x y : E3}
    (hx : capExampleDelta / 10 ≤ capExampleF x)
    (hy : y ∈ ball x 100) : 9 * capExampleEpsilon < axisRadius y := by
  have hxR : capExampleDelta / 10 ≤ axisRadius x := hx.trans (capF_le_axisRadius x)
  have hxy : dist x y < 100 := by simpa [dist_comm] using hy
  have hLip := axisRadius_lipschitz x y
  have hlow : axisRadius x - dist x y ≤ axisRadius y := by
    have h := (abs_le.mp hLip).2
    linarith
  linarith [capExample_far_100_margin]

theorem actualJ_eq_plane_on_band {x : E3}
    (hx : capExampleDelta / 10 ≤ capExampleF x) :
    actualJ x = planeReferenceIsometry (physicalPlane x) := by
  apply actualJ_physicalPlane
  have he := capExampleDelta_height_error
  have hR := capF_le_axisRadius x
  have hrad : 9 * capExampleEpsilon ≤ capExampleDelta / 10 := by
    nlinarith [capExampleDelta_large]
  exact (hrad.trans hx).trans hR

theorem actualJ_dist_le_on_band {x y : E3}
    (hx : capExampleDelta / 10 ≤ capExampleF x)
    (hy : y ∈ ball x 100) : dist (actualJ y) (actualJ x) ≤ dist y x := by
  have hyR := axisRadius_gt_nine_on_100_ball hx hy
  rw [actualJ_physicalPlane y hyR.le, actualJ_eq_plane_on_band hx,
    planeReferenceIsometry.dist_map]
  exact physicalPlane_nonexpanding y x

theorem actualJ_exact_ball_cover {x : E3}
    (hx : capExampleDelta / 10 ≤ capExampleF x) {v : E2}
    (hv : v ∈ ball (actualJ x) 100) :
    ∃ y ∈ ball x 100, actualJ y = v := by
  let q : WithLp 2 (ℝ × ℝ) := planeReferenceIsometry.symm (v - actualJ x)
  have hv' : dist v (actualJ x) < 100 := by simpa using hv
  have hq : dist q 0 < 100 := by
    change dist (planeReferenceIsometry.symm (v - actualJ x)) 0 < 100
    rw [dist_zero_right, planeReferenceIsometry.symm.norm_map]
    rw [dist_eq_norm] at hv'
    exact hv'
  obtain ⟨y, hy, hcenter⟩ := centredPlane_ball_cover x 100 (by norm_num)
    (by
      have h := capF_le_axisRadius x
      have hΔ := capExampleDelta_large
      linarith [hx]) q hq
  have hyR := axisRadius_gt_nine_on_100_ball hx hy
  have hdiff : actualJ y - actualJ x =
      planeReferenceIsometry (centredPlane x y) := by
    rw [actualJ_physicalPlane y hyR.le, actualJ_eq_plane_on_band hx,
      centredPlane, map_sub]
  have htranslated : actualJ y - actualJ x = v - actualJ x := by
    rw [hdiff, hcenter]
    simp [q]
  have hEq := congrArg (fun z : E2 => z + actualJ x) htranslated
  refine ⟨y, hy, ?_⟩
  simpa using hEq

theorem actualJ_infDist_small_on_band {x y : E3}
    (hx : capExampleDelta / 10 ≤ capExampleF x)
    (hy : y ∈ ball x 100) {γ : ℝ} (hγ : 0 < γ) :
    infDist (actualJ y) (ball (actualJ x) 100) < 100 * γ := by
  have hdist := actualJ_dist_le_on_band hx hy
  have hball : actualJ y ∈ ball (actualJ x) 100 := by
    apply mem_ball.mpr
    exact hdist.trans_lt (by simpa using hy)
  rw [Metric.infDist_zero_of_mem hball]
  exact mul_pos (by norm_num) hγ

theorem actualJ_dense_on_band {x : E3}
    (hx : capExampleDelta / 10 ≤ capExampleF x) {v : E2}
    (hv : v ∈ ball (actualJ x) 100) {γ : ℝ} (hγ : 0 < γ) :
    ∃ y ∈ ball x 100, ‖actualJ y - v‖ < 100 * γ := by
  obtain ⟨y, hy, hY⟩ := actualJ_exact_ball_cover hx hv
  refine ⟨y, hy, ?_⟩
  rw [hY, sub_self, norm_zero]
  exact mul_pos (by norm_num) hγ

theorem capChartJ_lipschitz_local {x : E3}
    (hxF : capExampleDelta / 10 ≤ capExampleF x) {y z : E3}
    (hy : y ∈ ball x 100) (hz : z ∈ ball x 100) :
    ‖capChartJ y - capChartJ z‖ ≤ dist y z := by
  rw [capChartJ_eq_actualJ]
  have hry := axisRadius_gt_nine_on_100_ball hxF hy
  have hrz := axisRadius_gt_nine_on_100_ball hxF hz
  have hnorm : ‖actualJ y - actualJ z‖ = dist (actualJ y) (actualJ z) := by
    rw [dist_eq_norm]
  rw [hnorm, actualJ_physicalPlane y hry.le, actualJ_physicalPlane z hrz.le,
    planeReferenceIsometry.dist_map]
  exact physicalPlane_nonexpanding y z

/-- Concrete EdgeChart on the capped three dimensional collar. -/
noncomputable def capExampleEdgeChart :
    EdgeChart capExampleMetric capExampleMetricNorm capExampleDelta
      (1 / 50) (1 / 1000000) capChartB (1 / 50) (1 / 100)
      capThreeAxis (fun _ => 1) capExampleF := by
  refine {
    center := capChartCenter
    rho_center := rfl
    center_mem := capChartCenter_axis
    Y := CapChartY
    instY := capChartYMetric
    q := ULift.up (capProductCoordinates.symm capChartCenter).2
    split := capChartSplitApprox
    Qn := physicalPlane
    Qn_fst := ?_
    coord := capThreeCoord
    domain := univ
    isOpen_domain := isOpen_univ
    closedBall_subset_domain := subset_univ _
    contMDiffOn_coord := capExample_coord_smooth.contMDiffOn
    coord_center := capChartCenter_coord
    lipschitz := capChartCoord_lipschitz
    value := ?_
    test := ?_
    disk_subset := capChart_disk_subset
    cutoff_eq_one := capChart_cutoff_eq_one
    collar := ?_
  }
  · intro z
    change (physicalPlane z).fst = (capChartSplitApprox.toFun z).fst
    change (physicalPlane z).fst = (capChartLiftSplitIsometry z).fst
    rw [capChartLiftSplitIsometry_fst]
    simp [physicalPlane]
  · intro x hx
    have hsplit : capChartSplitApprox.toFun x = capChartLiftSplitIsometry x := rfl
    rw [hsplit, capChartLiftSplitIsometry_fst]
    simp
    have hΔ := capExampleDelta_large
    nlinarith
  · intro x hx x' hx' hfar W hW hgeo
    have hsec := actual_coord_geodesic_secant x x' W hW (by
      have hΔ := capExampleDelta_large
      linarith) hgeo
    have hsplitX : (capChartSplitApprox.toFun x).fst = capThreeCoord x := by
      rw [show capChartSplitApprox.toFun x = capChartLiftSplitIsometry x by rfl]
      exact capChartLiftSplitIsometry_fst x
    have hsplitX' : (capChartSplitApprox.toFun x').fst = capThreeCoord x' := by
      rw [show capChartSplitApprox.toFun x' = capChartLiftSplitIsometry x' by rfl]
      exact capChartLiftSplitIsometry_fst x'
    rw [hsec, hsplitX, hsplitX']
    simp
  · intro x hx hcoord hlow hhigh
    have hlowF : capExampleDelta / 10 ≤ capExampleF x := by
      simpa using hlow
    refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_⟩
    · have hrescale :
        capExampleMetricSpace.rescale (1 : ℝ)⁻¹ (by norm_num) =
          capExampleMetricSpace := by simp
      rw [hrescale]
      refine ⟨capChartPlaneApprox hx hlowF, ?_⟩
      intro y
      rfl
    · let J := edgeReferenceCoordinates ![capThreeCoord,
        fun z => capExampleF z / ((fun _ => (1 : ℝ)) z)]
      have hJactual : J = actualJ := by
        funext y
        simp [J, actualJ, actualComponent, edgeReferenceCoordinates]
      have hJchart : J = capChartJ := by
        funext y
        simp [J, capChartJ, edgeReferenceCoordinates]
      have hlow' : capExampleDelta / 10 ≤ capExampleF x := hlowF
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · change ContMDiffOn (𝓡 3) (𝓘(ℝ, E2)) ∞ J (ball x (300 * 1))
        rw [hJactual]
        exact actualJ_smooth.contMDiffOn
      · intro y hy
        have hy100 : y ∈ ball x 100 := by simpa using hy
        have hfar := axisRadius_gt_nine_on_100_ball hlow' hy100
        change Function.Surjective (mfderiv (𝓡 3) (𝓘(ℝ, E2)) J y)
        rw [hJactual]
        exact actualJ_mfderiv_surjective_of_far hfar
      · intro y hy z hz
        have hy100 : y ∈ ball x 100 := by simpa using hy
        have hz100 : z ∈ ball x 100 := by simpa using hz
        change ‖J y - J z‖ ≤ (1 + 1 / 50) * (dist y z / 1)
        rw [hJchart]
        have hLip := capChartJ_lipschitz_local hlow' hy100 hz100
        calc
          ‖capChartJ y - capChartJ z‖ ≤ dist y z := hLip
          _ ≤ (1 + 1 / 50) * (dist y z / 1) := by
            have hd : 0 ≤ dist y z := dist_nonneg
            norm_num
            nlinarith
      · intro y hy
        have hy100 : y ∈ ball x 100 := by simpa using hy
        have hball' : capChartJ y ∈ ball (capChartJ x) 100 := by
          rw [Metric.mem_ball]
          have hLip := capChartJ_lipschitz_local hlow' hy100
            (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 100))
          have hdist : dist (capChartJ y) (capChartJ x) ≤ dist y x := by
            rw [dist_eq_norm]
            exact hLip
          exact hdist.trans_lt (by simpa using hy100)
        have hball : J y ∈ ball (J x) 100 := by
          simpa only [hJchart] using hball'
        rw [Metric.infDist_zero_of_mem hball]
        norm_num
      · intro v hv
        have hv' : v ∈ ball (actualJ x) 100 := by
          change v ∈ ball (J x) 100 at hv
          rw [hJactual] at hv
          exact hv
        obtain ⟨y, hy, heq⟩ := actualJ_exact_ball_cover hlow' hv'
        refine ⟨y, ?_, ?_⟩
        · simpa using hy
        · change ‖J y - v‖ < 100 * (1 / 50)
          rw [hJactual, heq, sub_self, norm_zero]
          norm_num
      · intro y hy z hz hsep W hW hgeo
        have hy100 : y ∈ ball x 100 := by simpa using hy
        have hrad100 : dist z x < 100 * 50 := by simpa using hz
        have hrad : dist z x < 5000 := by nlinarith
        have hz10000 : z ∈ ball x 10000 :=
          lt_of_lt_of_le hrad (by norm_num)
        have hnative := actual_native_geodesic_test capChartCenter x y z hx
          hlowF hy100 hz10000 (by simpa using hsep) W hW hgeo
        change ‖1 • mvfderiv (I := 𝓡 3) J y W -
          (dist y z / 1)⁻¹ •
            (planeReferenceIsometry
                (planeComparisonMap physicalPlane capChartCenter x capExampleDelta 1 z) -
              planeReferenceIsometry
                (planeComparisonMap physicalPlane capChartCenter x capExampleDelta 1 y))‖ <
          1 / 50
        rw [hJactual]
        have hγ : (1 / 100 : ℝ) < 1 / 50 := by norm_num
        have hnative' : ‖mvfderiv (I := 𝓡 3) actualJ y W -
            (dist y z)⁻¹ •
              (planeReferenceIsometry
                  (planeComparisonMap physicalPlane capChartCenter x capExampleDelta 1 z) -
                planeReferenceIsometry
                  (planeComparisonMap physicalPlane capChartCenter x capExampleDelta 1 y))‖ <
            1 / 100 := by
          simpa using hnative
        simpa using hnative'.trans hγ

theorem capExampleEdgeChart_center_eq :
    capExampleEdgeChart.center = capChartCenter := rfl

theorem capExampleEdgeChart_coord_eq :
    capExampleEdgeChart.coord = capThreeCoord := rfl

theorem capExampleEdgeChart_coord_on_slab :
    (fun y : DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceSlab =>
      capExampleEdgeChart.coord (y : E3)) =
        DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceCoord := by
  funext y
  rfl

theorem capExampleEdgeChart_boundary_on_slab :
    (fun y : DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceSlab =>
      4 * capExampleDelta -
        edgeRowHeight capExampleDelta capExampleF (fun _ => 1) (y : E3)) =
      DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary := by
  funext y
  rfl

/-- Cutoff supported inside the chart radius. -/
noncomputable def capChartCutoff : E3 → ℝ :=
  (Subtype.val : ball capChartCenter (100 * capExampleDelta) → E3).extend
    (fun x => edgeCoordinateProfile (capThreeCoord x.val / capExampleDelta) *
      edgeHeightProfile (capExampleF x.val / capExampleDelta)) 0

theorem capChart_center_distance (x : E3) :
    dist x capChartCenter = Real.sqrt (capThreeCoord x ^ 2 + axisRadius x ^ 2) := by
  obtain ⟨a, rfl⟩ := capProductCoordinates.surjective x
  change dist (capProductCoordinates a) (capProductCoordinates (0, 0)) = _
  rw [physical_distance_formula]
  simp [capThreeCoord, axisRadius, physicalRadius_distance_zero]

theorem capChart_cutoff_nonzero_bound {x : E3}
    (hζ : capChartCutoff x ≠ 0) :
    dist x capChartCenter < 129 / 10 * capExampleDelta := by
  have hΔ : 0 < capExampleDelta := by
    have h := capExampleDelta_large
    linarith
  by_cases hball : x ∈ ball capChartCenter (100 * capExampleDelta)
  · have hpoint : ((⟨x, hball⟩ : ball capChartCenter
        (100 * capExampleDelta)) : E3) = x := rfl
    have hprofiles :
        edgeCoordinateProfile (capThreeCoord x / capExampleDelta) *
          edgeHeightProfile (capExampleF x / capExampleDelta) ≠ 0 := by
      unfold capChartCutoff at hζ
      rw [← hpoint, Subtype.val_injective.extend_apply] at hζ
      simpa using hζ
    have hcoord1 :
        edgeCoordinateProfile (capThreeCoord x / capExampleDelta) ≠ 0 :=
      left_ne_zero_of_mul hprofiles
    have hcoord_lo : -(9 : ℝ) < capThreeCoord x / capExampleDelta := by
      by_contra h
      have hle : capThreeCoord x / capExampleDelta ≤ -9 := le_of_not_gt h
      have hz := intervalPlateauProfile_zero_left (a := -(9 : ℝ)) (b := -8)
        (c := 8) (d := 9) (by norm_num) hle
      exact hcoord1 (by simpa [edgeCoordinateProfile] using hz)
    have hcoord_hi : capThreeCoord x / capExampleDelta < 9 := by
      by_contra h
      have hge : 9 ≤ capThreeCoord x / capExampleDelta := le_of_not_gt h
      have hz := intervalPlateauProfile_zero_right (a := -(9 : ℝ)) (b := -8)
        (c := 8) (d := 9) (by norm_num) hge
      exact hcoord1 (by simpa [edgeCoordinateProfile] using hz)
    have hcoord : |capThreeCoord x| < 9 * capExampleDelta := by
      apply abs_lt.mpr
      constructor
      · have h := (lt_div_iff₀ hΔ).mp hcoord_lo
        nlinarith
      · have h := (div_lt_iff₀ hΔ).mp hcoord_hi
        nlinarith
    have hFprofile : edgeHeightProfile (capExampleF x / capExampleDelta) ≠ 0 :=
      right_ne_zero_of_mul hprofiles
    have hFdiv : capExampleF x / capExampleDelta < 9 := by
      by_contra h
      have hge : 9 ≤ capExampleF x / capExampleDelta := le_of_not_gt h
      have hz := descendingIntervalProfile_zero (by norm_num : (8 : ℝ) < 9) hge
      exact hFprofile (by simpa [edgeHeightProfile] using hz)
    have hF : capExampleF x < 9 * capExampleDelta :=
      (div_lt_iff₀ hΔ).mp hFdiv
    have hrad : axisRadius x < (901 / 100 : ℝ) * capExampleDelta := by
      rw [axisRadius_infDist]
      have herr := (abs_le.mp (capExampleF_error x)).1
      have hmargin := capExampleDelta_height_error
      nlinarith
    have hcoord_sq : capThreeCoord x ^ 2 < (9 * capExampleDelta) ^ 2 := by
      rw [← sq_abs]
      exact (sq_lt_sq₀ (abs_nonneg _) (by positivity)).2 hcoord
    have hrad_sq : axisRadius x ^ 2 < ((901 / 100 : ℝ) * capExampleDelta) ^ 2 := by
      have hrad_nonneg : 0 ≤ axisRadius x := by
        unfold axisRadius physicalRadius
        exact mul_nonneg capExampleEpsilon_pos.le (norm_nonneg _)
      exact (sq_lt_sq₀ hrad_nonneg (by positivity)).2 hrad
    have hsum : capThreeCoord x ^ 2 + axisRadius x ^ 2 <
        (129 / 10 * capExampleDelta) ^ 2 := by
      have hnum : (9 : ℝ) ^ 2 + (901 / 100) ^ 2 < (129 / 10) ^ 2 := by
        norm_num
      nlinarith [sq_pos_of_pos hΔ]
    rw [capChart_center_distance]
    exact (Real.sqrt_lt' (by positivity)).mpr hsum
  · have hnot : ¬ ∃ y : ball capChartCenter (100 * capExampleDelta),
        (y : E3) = x := by
      rintro ⟨y, rfl⟩
      exact hball y.property
    unfold capChartCutoff at hζ
    rw [Function.extend_apply' _ _ _ hnot] at hζ
    simp at hζ

theorem capChart_cutoff_tsupport_subset :
    tsupport capChartCutoff ⊆ closedBall capChartCenter
      (129 / 10 * capExampleDelta) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hζ : capChartCutoff x ≠ 0 := by simpa using hx
  exact mem_closedBall.mpr (capChart_cutoff_nonzero_bound hζ).le

theorem capSlabChart_eq_packetChart :
    DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceNativeChart =
      DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph
        (M := DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceSlab)
      euclideanThreeProdHomeomorph := rfl

/-- Finite order ambient Riemannian metric for the product model. -/
noncomputable def capProductMetricG :
    Bundle.ContMDiffRiemannianMetric (𝓘(ℝ, E3)) 4 E3
      (TangentSpace (𝓘(ℝ, E3)) : E3 → Type _) := by
  refine {
    inner := capExampleMetric.inner
    symm := capExampleMetric.symm
    pos := capExampleMetric.pos
    isVonNBounded := capExampleMetric.isVonNBounded
    contMDiff := ?_
  }
  exact capExampleMetric.contMDiff.of_le (by norm_num)

/-- Surface instance used by the concrete edge product model. -/
local instance capProductSurfaceMetricSpace : MetricSpace E2 :=
  EdgeCapSplitting.capSurfaceMetricSpace
local instance capProductSurfaceSigma : SigmaCompactSpace E2 := by infer_instance
/-- Surface instance used by the concrete edge product model. -/
local instance capProductSurfaceEDist : EDist E2 :=
  EdgeCapSplitting.capSurfaceEDist
/-- Surface instance used by the concrete edge product model. -/
local instance capProductSurfaceDist : Dist E2 := EdgeCapSplitting.capSurfaceDist
/-- Surface instance used by the concrete edge product model. -/
local instance capProductSurfaceUniform : UniformSpace E2 :=
  EdgeCapSplitting.capSurfaceUniform
/-- Surface instance used by the concrete edge product model. -/
local instance capProductSurfaceEMetric : PseudoEMetricSpace E2 :=
  EdgeCapSplitting.capSurfaceEMetric
/-- Surface instance used by the concrete edge product model. -/
local instance capProductSurfacePseudo : PseudoMetricSpace E2 :=
  EdgeCapSplitting.capSurfacePseudo
/-- Surface instance used by the concrete edge product model. -/
local instance capProductSurfaceBundle :
    RiemannianBundle (TangentSpace (𝓡 2) : E2 → Type _) :=
  ⟨(scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).toRiemannianMetric⟩
local instance capProductSurfaceRiemannian : IsRiemannianManifold (𝓡 2) E2 :=
  inducedMetricSpace_isRiemannianManifold
    (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos)
local instance capProductSurfaceComplete : CompleteSpace E2 :=
  (scaledCapComplete capExampleEpsilon capExampleEpsilon_pos).complete
/-- Finite order scaled cap metric on the surface factor. -/
noncomputable def capProductMetricKappa :
    Bundle.ContMDiffRiemannianMetric (𝓡 2) 4 E2
      (TangentSpace (𝓡 2) : E2 → Type _) := by
  refine {
    inner := (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).inner
    symm := (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).symm
    pos := (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).pos
    isVonNBounded :=
      (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).isVonNBounded
    contMDiff := ?_
  }
  exact (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).contMDiff.of_le
    (by norm_num)

/-- Product coordinate diffeomorphism for the collar model. -/
noncomputable def capProductTheta :
    Diffeomorph ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓘(ℝ, E3)) (ℝ × E2) E3 5 := by
  refine {
    toEquiv := capProductCoordinates.toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_
  }
  · exact capProductCoordinates.contMDiff_toFun.of_le (by norm_num)
  · exact capProductCoordinates.contMDiff_invFun.of_le (by norm_num)

/-- Identity partial diffeomorphism used by the product model. -/
noncomputable def capProductEmbedding :
    PartialDiffeomorph (𝓘(ℝ, E3)) (𝓘(ℝ, E3)) E3 E3 5 :=
  DifferentialGeometry.PartialDiffeomorph.ofLE
    (Diffeomorph.refl (𝓘(ℝ, E3)) E3 ∞).toPartialDiffeomorph
    (m := 5) (n := ∞) (by norm_num)

theorem capProductSurface_distance_zero (z : E2) :
    dist z (0 : E2) = capExampleEpsilon * ‖z‖ := by
  have he : edist (0 : E2) z = ENNReal.ofReal (capExampleEpsilon * ‖z‖) := by
    change riemannianEDistOf
      (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos) 0 z = _
    exact scaledCap_edist_zero capExampleEpsilon capExampleEpsilon_pos z
  have hr := congrArg ENNReal.toReal he
  rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at hr
  rw [ENNReal.toReal_ofReal
    (mul_nonneg capExampleEpsilon_pos.le (norm_nonneg z))] at hr
  simpa only [dist_comm] using hr

/-- Concrete finite order EdgeProductModel for the capped collar. -/
noncomputable def capExampleEdgeProductModel :
    EdgeProductModel capExampleEdgeChart 5 := by
  classical
  refine {
    N := E3
    instMetricN := capExampleMetricSpace
    instChartedN := chartedSpaceSelf E3
    instManifoldN := by infer_instance
    instProperN := capExampleProper
    instConnectedN := by infer_instance
    instBundleN := capExampleBundle
    instRiemannianN := capExampleRiemannian
    G := capProductMetricG
    enorm := ?_
    sectional_nonneg := ?_
    S := E2
    instMetricS := capProductSurfaceMetricSpace
    instChartedS := chartedSpaceSelf E2
    instManifoldS := by infer_instance
    instBundleS := capProductSurfaceBundle
    instRiemannianS := capProductSurfaceRiemannian
    κ := capProductMetricKappa
    enormS := ?_
    sectional_nonnegS := ?_
    orientationS := Classical.choice EdgeCapSurface.surfaceOrientation
    Θ := capProductTheta
    dist_Θ := ?_
    product_metric := ?_
    j := capProductEmbedding
    s₀ := 0
    base_mem := by
      change capProductTheta (0, 0) ∈ (Set.univ : Set E3)
      exact Set.mem_univ _
    j_base := ?_
    slab := ?_
  }
  · exact capExampleMetricNorm
  · intro x v w
    change 0 ≤ capExampleMetric.sectionalCurvature x v w
    rw [Bundle.ContMDiffRiemannianMetric.sectionalCurvature_eq_smooth,
      DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div]
    apply div_nonneg
    · have hsec := capExample_sectional x
      have hnum := hsec v w
      simpa only [zero_mul] using hnum
    · have hcs := DifferentialGeometry.Geometry.Riemannian.gInner_sq_le_mul
        capExampleMetric x v w
      exact sub_nonneg.mpr hcs
  · exact EdgeCapSplitting.capSurfaceMetricNorm
  · intro x v w
    change 0 ≤ (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).sectionalCurvature
      x v w
    rw [Bundle.ContMDiffRiemannianMetric.sectionalCurvature_eq_smooth,
      DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div]
    apply div_nonneg
    · exact EdgeCapProduct.scaledCapRm capExampleEpsilon capExampleEpsilon_pos x v w
    · have hcs := DifferentialGeometry.Geometry.Riemannian.gInner_sq_le_mul
        (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos) x v w
      exact sub_nonneg.mpr hcs
  · intro a b
    change dist (capProductCoordinates a) (capProductCoordinates b) =
      dist (WithLp.toLp 2 a) (WithLp.toLp 2 b)
    have h := physicalProductIsometry.dist_eq
      (capProductCoordinates a) (capProductCoordinates b)
    simpa [physicalProductIsometry, Diffeomorph.symm_apply_apply] using h.symm
  · intro p v w
    exact capThree_physical_product capExampleEpsilon capExampleEpsilon_pos p v w
  · rw [capExampleEdgeChart_center_eq]
    change capProductCoordinates (0, 0) = capExampleAxis 0
    rfl
  · intro y hy hc hH
    let p : ℝ × E2 := capProductCoordinates.symm y
    have hcoord : |p.1| < 5 * capExampleDelta := by
      change |capThreeCoord y| < 5 * capExampleDelta
      have hc' : |capThreeCoord y| ≤ 4 * capExampleDelta := by
        simpa [capExampleEdgeChart] using hc
      linarith [EdgeCapSlab.delta_pos]
    have hF : capExampleF y ≤ 4 * capExampleDelta := by
      have h := (edgeRowHeight_le_iff EdgeCapSlab.delta_pos).mp hH
      simpa using h
    have hdist : Metric.infDist y capThreeAxis ≤
        capExampleF y + 9 * capExampleEpsilon := by
      have he := capExampleF_error y
      have hdiff := (abs_le.mp he).1
      linarith
    have hsurface : dist p.2 (0 : E2) < 5 * capExampleDelta := by
      calc
        dist p.2 (0 : E2) = capExampleEpsilon * ‖p.2‖ :=
          capProductSurface_distance_zero p.2
        _ = Metric.infDist y capThreeAxis := by
          simpa [p] using (capExample_axis_infDist y).symm
        _ ≤ capExampleF y + 9 * capExampleEpsilon := hdist
        _ ≤ 4 * capExampleDelta + 9 * capExampleEpsilon := by
          exact add_le_add hF le_rfl
        _ < 5 * capExampleDelta := by
          linarith [capExampleDelta_height_error, EdgeCapSlab.delta_pos]
    refine ⟨p, hcoord, hsurface, ?_, ?_⟩
    · change capProductTheta p ∈ (Set.univ : Set E3)
      exact Set.mem_univ _
    · change capProductCoordinates (capProductCoordinates.symm y) = y
      exact capProductCoordinates.apply_symm_apply y

/-- Concrete EdgeDiskPacket with regular fibre and boundary suppliers. -/
noncomputable def capExampleEdgeDiskPacket :
    @EdgeDiskPacket E3 capExampleMetricSpace (chartedSpaceSelf E3)
      (by
        let _ : ChartedSpace E3 E3 := chartedSpaceSelf E3
        infer_instance)
      capExampleSigma capExampleBundle capExampleRiemannian capExampleComplete
      capExampleContinuous capExampleMetric capExampleMetricNorm capExampleDelta
      (1 / 50) (1 / 1000000) capChartB (1 / 50) (1 / 100)
      capThreeAxis (fun _ => 1) capExampleF := by
  refine {
    toEdgeChart := capExampleEdgeChart
    slabOpen := DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceSlab
    slabOpen_subset := by
      simpa [capExampleEdgeChart, capChartCenter] using
        DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceSlab_subset_ball
    slab_subset := ?_
    contMDiff_coord_slab := ?_
    contMDiff_height_slab := ?_
    regular_fibre := ?_
    regular_boundary := ?_
    diskModel := ?_
    boundary_level := ?_
    trivial := ?_
    tsupport_cutoff_subset := ?_
  }
  · intro y hy hcoordbound hheight
    have hcoord' : |capThreeCoord y| ≤ 4 * capExampleDelta := by
      simpa [capExampleEdgeChart] using hcoordbound
    exact DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.whole_closed_slab_subset
      hcoord' hheight
  · let _ := DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceNativeChart
    let _ := DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceNativeManifold
    change ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ)
      ∞ DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceCoord
    exact DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceCoord_smooth
  · let _ := DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceNativeChart
    let _ := DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceNativeManifold
    change ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ)
      ∞ DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary
    exact DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary_smooth
  · intro y hcoord0 hheight
    let _ := DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceNativeChart
    let _ := DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceNativeManifold
    change Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ)
      DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceCoord y)
    exact DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceCoord_regular y
  · intro y hcoord0 hboundary
    let _ := DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceNativeChart
    let _ := DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceNativeManifold
    have hpacket :
        DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary y = 0 := by
      simpa [DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary] using hboundary
    change Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
      (fun q => (DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceCoord q,
        DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary q)) y)
    exact DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary_regular y hpacket
  · classical
    exact Classical.choice
      DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.actualFibre_disk
  · have hBound (y : DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceSlab) :
        0 ≤ DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary y ↔
          edgeRowHeight capExampleDelta capExampleF (fun _ => 1) y ≤
            4 * capExampleDelta := by
      dsimp [DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary]
      constructor <;> intro h <;> linarith
    have hLevel (y : DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceSlab) :
        DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary y = 0 ↔
          edgeRowHeight capExampleDelta capExampleF (fun _ => 1) y =
            4 * capExampleDelta := by
      dsimp [DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary]
      constructor <;> intro h <;> linarith
    constructor
    · intro y hy
      have hp :
          DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary
              (y : DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceSlab) = 0 :=
        (DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.actualFibre_boundary
          (x := y)).mp hy
      dsimp [DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary] at hp
      linarith
    · intro y hy
      apply DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.actualFibre_boundary.mpr
      dsimp [DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary]
      linarith
  · intro a b ha h0 hb
    have hBound (y : DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceSlab) :
        0 ≤ DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary y ↔
          edgeRowHeight capExampleDelta capExampleF (fun _ => 1) y ≤
            4 * capExampleDelta := by
      dsimp [DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary]
      constructor <;> intro h <;> linarith
    have hLower (y : DifferentialGeometry.Geometry.Collapse.EdgeCapSlab.sourceSlab)
        (r' : ℝ) :
        -r' ≤ DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary y ↔
          edgeRowHeight capExampleDelta capExampleF (fun _ => 1) y ≤
            4 * capExampleDelta + r' := by
      dsimp [DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.packetBoundary]
      constructor <;> intro h <;> linarith
    exact DifferentialGeometry.Geometry.Collapse.EdgeCapTrivial.actual_native_R2 a b ha h0 hb
  · have hcut :
        (Subtype.val : ball capExampleEdgeChart.center
            (100 * capExampleDelta) → E3).extend
          (fun y => edgeCoordinateProfile
              (capExampleEdgeChart.coord y.val / capExampleDelta) *
            edgeHeightProfile (capExampleF y.val /
              (capExampleDelta * (fun _ => (1 : ℝ)) y.val))) 0 =
      capChartCutoff := by
      funext x
      rw [capExampleEdgeChart_center_eq, capExampleEdgeChart_coord_eq]
      simp only [capChartCutoff, mul_one]
    rw [hcut, capExampleEdgeChart_center_eq]
    exact capChart_cutoff_tsupport_subset

end DifferentialGeometry.Geometry.Collapse.EdgeCapCollarInhabitant
