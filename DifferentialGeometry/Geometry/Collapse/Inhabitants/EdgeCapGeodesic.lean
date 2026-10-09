import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapHessian
import DifferentialGeometry.Geometry.Collapse.EdgeReferenceChartApplications
import DifferentialGeometry.Geometry.Comparison.Hessian.AlongGeodesic
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.CalibratedCoray
import Mathlib.Analysis.Calculus.MeanValue
set_option autoImplicit false
noncomputable section
open Bundle Set Function Manifold Metric Filter
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open DifferentialGeometry.Geometry.Collapse.EdgeCapCarrier
open DifferentialGeometry.Geometry.Collapse.EdgeCapHeight
open DifferentialGeometry.Geometry.Collapse.EdgeCapPlane
open DifferentialGeometry.Geometry.Collapse.EdgeCapHessian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open DifferentialGeometry.Analysis.Calculus
open GC.MetricGeometry
open scoped Manifold ContDiff Topology InnerProductSpace
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
namespace DifferentialGeometry.Geometry.Collapse.EdgeCapGeodesic

attribute [local instance] capExampleSigma capExampleMetricSpace capExampleEDist
  capExampleDist capExampleUniform capExampleEMetric capExamplePseudo capExampleBundle
  capExampleRiemannian capExampleContinuous capExampleComplete capExampleProper capExampleDimension
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology

def actualComponent (i : Fin 2) : E3 → ℝ := ![capThreeCoord, capExampleF] i

theorem actualComponent_smooth (i : Fin 2) : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (actualComponent i) := by
  fin_cases i
  · exact capExample_coord_smooth
  · exact capExampleF_smooth

theorem actualComponent_hessian (i : Fin 2) (x : E3)
    (hx : capExampleEpsilon * (transitionEnd + 9) < axisRadius x)
    (u v : TangentSpace (𝓡 3) x) : hessFun capExampleMetric (actualComponent i) x u v = 0 := by
  fin_cases i
  · have h := congrArg (fun B => B u v) (capExample_coord_hess x)
    exact h
  · exact actual_E3_height_hessian x hx u v

theorem actual_geodesic_end (x : E3) (u : TangentSpace (𝓡 3) x)
    (hu : capExampleMetric.inner x u u = 1) (T : ℝ) (hT : 0 ≤ T)
    (hx : T + 2 + capExampleEpsilon * (transitionEnd + 9) < axisRadius x)
    (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) (T + 1)) :
    capExampleEpsilon * (transitionEnd + 9) <
      axisRadius (intrinsicGeodesic capExampleMetric capExampleMetricNorm x u t) := by
  have hd := (lipschitzWith_one_intrinsicGeodesic capExampleMetric
    capExampleMetricNorm x u hu).dist_le_mul t 0
  simp only [NNReal.coe_one, one_mul, intrinsicGeodesic_zero,
    Real.dist_eq, sub_zero] at hd
  have hat : |t| < T + 1 := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
  have hl := axisRadius_lipschitz x
    (intrinsicGeodesic capExampleMetric capExampleMetricNorm x u t)
  rw [dist_comm x] at hl
  have hm := le_abs_self (axisRadius x -
    axisRadius (intrinsicGeodesic capExampleMetric capExampleMetricNorm x u t))
  linarith

theorem actual_geodesic_deriv2_zero (i : Fin 2) (x : E3) (u : TangentSpace (𝓡 3) x)
    (hu : capExampleMetric.inner x u u = 1) (T : ℝ) (hT : 0 ≤ T)
    (hx : i = 0 ∨ T + 2 + capExampleEpsilon * (transitionEnd + 9) < axisRadius x)
    (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) (T + 1)) :
    deriv (deriv (actualComponent i ∘
      intrinsicGeodesic capExampleMetric capExampleMetricNorm x u)) t = 0 := by
  have hg := intrinsicGeodesic_contMDiff capExampleMetric capExampleMetricNorm x u
  have hh := DifferentialGeometry.Geometry.Riemannian.deriv2_comp_geo
    capExampleMetric (actualComponent_smooth i) hg
    (intrinsicGeodesic_isGeodesic capExampleMetric capExampleMetricNorm x u) t
  change deriv (deriv (actualComponent i ∘
    intrinsicGeodesic capExampleMetric capExampleMetricNorm x u)) t = _ at hh
  rcases hx with hi | hx
  · subst i
    change deriv (deriv (capThreeCoord ∘
      intrinsicGeodesic capExampleMetric capExampleMetricNorm x u)) t = _ at hh
    change deriv (deriv (capThreeCoord ∘
      intrinsicGeodesic capExampleMetric capExampleMetricNorm x u)) t = 0
    simp only [actualComponent, Matrix.cons_val_zero] at hh
    rw [capExample_coord_hess] at hh
    erw [LinearMap.zero_apply] at hh
    exact hh
  · rw [actualComponent_hessian i _ (actual_geodesic_end x u hu T hT hx t ht)] at hh
    exact hh


theorem actualComponent_geodesic_affine (i : Fin 2) (x : E3)
    (u : TangentSpace (𝓡 3) x) (hu : capExampleMetric.inner x u u = 1)
    (T : ℝ) (hT : 0 ≤ T)
    (hx : i = 0 ∨ T + 2 + capExampleEpsilon * (transitionEnd + 9) < axisRadius x) :
    actualComponent i (intrinsicGeodesic capExampleMetric capExampleMetricNorm x u T) =
      actualComponent i x + T * mvfderiv (I := 𝓡 3) (actualComponent i) x u := by
  let c := intrinsicGeodesic capExampleMetric capExampleMetricNorm x u
  let F := actualComponent i ∘ c
  let d := mvfderiv (I := 𝓡 3) (actualComponent i) x u
  let G : ℝ → ℝ := fun t => actualComponent i x + t * d
  have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ c :=
    intrinsicGeodesic_contMDiff capExampleMetric capExampleMetricNorm x u
  have hc0 : c 0 = x := intrinsicGeodesic_zero capExampleMetric capExampleMetricNorm x u
  have hF : ContDiff ℝ ∞ F :=
    ((actualComponent_smooth i).comp hc).contDiff
  have hD : Differentiable ℝ (deriv F) :=
    (contDiff_infty_iff_deriv.mp hF).2.differentiable (by simp)
  have hline := DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along
    (𝓡 3) (actualComponent i) c 0 ((actualComponent_smooth i).mdifferentiableAt (by simp))
    (hc.contMDiffAt.mdifferentiableAt (by simp))
  change HasDerivAt F (mvfderiv (I := 𝓡 3) (actualComponent i) (c 0)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c 0 (realTangentOne 0))) 0 at hline
  have hv : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c 0 (realTangentOne 0) = u := by
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c 0 (1 : ℝ) = u
    exact intrinsicGeodesic_mfderiv_zero capExampleMetric capExampleMetricNorm x u
  rw [hv, hc0] at hline
  have hd0 : deriv F 0 = d := hline.deriv
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) (T + 1) := ⟨by norm_num, by linarith⟩
  have hder : ∀ t ∈ Ioo (-1 : ℝ) (T + 1), deriv F t = deriv F 0 := by
    intro t ht
    apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-1 : ℝ) (T + 1)).isPreconnected
      hD.differentiableOn ?_ ht h0
    intro s hs
    exact actual_geodesic_deriv2_zero i x u hu T hT hx s hs
  have hGd (t : ℝ) : HasDerivAt G d t := by
    convert! ((hasDerivAt_id t).mul_const d).const_add (actualComponent i x) using 1
    simp only [one_mul]
  have hG : Differentiable ℝ G := fun t => (hGd t).differentiableAt
  have hEq : EqOn F G (Ioo (-1 : ℝ) (T + 1)) :=
    isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-1 : ℝ) (T + 1)).isPreconnected
      (contDiff_infty_iff_deriv.mp hF).1.differentiableOn hG.differentiableOn
      (fun t ht => by rw [hder t ht, hd0, (hGd t).deriv]) h0
      (by simp only [F, G, Function.comp_apply, hc0, zero_mul, add_zero])
  exact hEq ⟨by linarith, by linarith⟩


theorem actualComponent_geodesic_secant (i : Fin 2) (x z : E3)
    (u : TangentSpace (𝓡 3) x) (hu : capExampleMetric.inner x u u = 1)
    (hd : 0 < dist x z)
    (hx : dist x z + 2 + capExampleEpsilon * (transitionEnd + 9) < axisRadius x)
    (hgeo : intrinsicGeodesic capExampleMetric capExampleMetricNorm x u (dist x z) = z) :
    mvfderiv (I := 𝓡 3) (actualComponent i) x u =
      (actualComponent i z - actualComponent i x) / dist x z := by
  have h := actualComponent_geodesic_affine i x u hu (dist x z) hd.le (Or.inr hx)
  rw [hgeo] at h
  apply (eq_div_iff hd.ne').mpr
  nlinarith


def actualJ : E3 → E2 := edgeReferenceCoordinates actualComponent

theorem actualJ_smooth : ContMDiff (𝓡 3) 𝓘(ℝ, E2) ∞ actualJ := by
  rw [← contMDiffOn_univ]
  exact edgeReferenceCoordinates_smooth (fun i => (actualComponent_smooth i).contMDiffOn)

theorem capF_eq_axisRadius (x : E3) (hx : 9 * capExampleEpsilon ≤ axisRadius x) :
    capExampleF x = axisRadius x := by
  have hn : 9 ≤ ‖(capProductCoordinates.symm x).2‖ := by
    apply (mul_le_mul_iff_left₀ capExampleEpsilon_pos).mp
    simpa only [axisRadius, physicalRadius, mul_comm] using hx
  change capCollarHeight capExampleEpsilon (capProductCoordinates.symm x).2 =
    physicalRadius (capProductCoordinates.symm x).2
  rw [capCollarHeight, capRadialProfile_linear hn]
  rfl

theorem actualJ_physicalPlane (x : E3) (hx : 9 * capExampleEpsilon ≤ axisRadius x) :
    actualJ x = planeReferenceIsometry (physicalPlane x) := by
  ext i
  fin_cases i
  · change actualJ x 0 = planeReferenceIsometry (physicalPlane x) 0
    rw [planeReferenceIsometry_apply_zero]
    rfl
  · change actualJ x 1 = planeReferenceIsometry (physicalPlane x) 1
    rw [planeReferenceIsometry_apply_one]
    exact capF_eq_axisRadius x hx

theorem actualJ_geodesic_secant (x z : E3)
    (u : TangentSpace (𝓡 3) x) (hu : capExampleMetric.inner x u u = 1)
    (hd : 0 < dist x z)
    (hx : dist x z + 2 + capExampleEpsilon * (transitionEnd + 9) < axisRadius x)
    (hgeo : intrinsicGeodesic capExampleMetric capExampleMetricNorm x u (dist x z) = z) :
    mvfderiv (I := 𝓡 3) actualJ x u = (dist x z)⁻¹ • (actualJ z - actualJ x) := by
  ext i
  change mvfderiv (I := 𝓡 3) (edgeReferenceCoordinates actualComponent) x u i =
    (dist x z)⁻¹ * (actualComponent i z - actualComponent i x)
  rw [edgeReferenceCoordinates_derivative (fun j => (actualComponent_smooth j).contMDiffAt)]
  rw [actualComponent_geodesic_secant i x z u hu hd hx hgeo, div_eq_mul_inv, mul_comm]


theorem actual_coord_geodesic_secant (x z : E3)
    (u : TangentSpace (𝓡 3) x) (hu : capExampleMetric.inner x u u = 1)
    (hd : 0 < dist x z)
    (hgeo : intrinsicGeodesic capExampleMetric capExampleMetricNorm x u (dist x z) = z) :
    mvfderiv (I := 𝓡 3) capThreeCoord x u =
      (capThreeCoord z - capThreeCoord x) / dist x z := by
  have h := actualComponent_geodesic_affine 0 x u hu (dist x z) hd.le (Or.inl rfl)
  change capThreeCoord (intrinsicGeodesic capExampleMetric capExampleMetricNorm x u (dist x z)) =
    capThreeCoord x + dist x z * mvfderiv (I := 𝓡 3) capThreeCoord x u at h
  rw [hgeo] at h
  apply (eq_div_iff hd.ne').mpr
  nlinarith


theorem collar_ball_margin (x y : E3) (hx : capExampleDelta / 10 ≤ capExampleF x)
    (hy : y ∈ ball x 10000) :
    10102 + capExampleEpsilon * (transitionEnd + 9) < axisRadius y := by
  have hbase := hx.trans (capF_le_axisRadius x)
  unfold capExampleDelta at hbase
  have hl := axisRadius_lipschitz x y
  rw [dist_comm x y] at hl
  change dist y x < 10000 at hy
  have hm := le_abs_self (axisRadius x - axisRadius y)
  have he := capExampleEpsilon_pos
  have ht := transitionEnd_pos
  have hp := mul_pos he ht
  nlinarith

theorem native_comparison_buffer (p x y : E3)
    (hx : x ∈ ball p (100 * capExampleDelta)) (hy : y ∈ ball x 10000) :
    planeComparisonMap physicalPlane p x capExampleDelta 1 y = centredPlane x y := by
  have hm : y ∈ ball p (200 * capExampleDelta) := by
    have ht := dist_triangle y x p
    change dist x p < 100 * capExampleDelta at hx
    change dist y x < 10000 at hy
    change dist y p < 200 * capExampleDelta
    linarith [capExampleDelta_large]
  rw [planeComparisonMap_of_mem hm, inv_one, one_smul]
  rfl

theorem actual_native_geodesic_test (p x y z : E3)
    (hxball : x ∈ ball p (100 * capExampleDelta))
    (hx : capExampleDelta / 10 ≤ capExampleF x)
    (hy : y ∈ ball x 100) (hz : z ∈ ball x 10000) (hd : 1 < dist y z)
    (W : TangentSpace (𝓡 3) y) (hW : capExampleMetric.inner y W W = 1)
    (hgeo : intrinsicGeodesic capExampleMetric capExampleMetricNorm y W (dist y z) = z) :
    ‖mvfderiv (I := 𝓡 3) actualJ y W - (dist y z)⁻¹ •
      (planeReferenceIsometry (planeComparisonMap physicalPlane p x capExampleDelta 1 z) -
        planeReferenceIsometry (planeComparisonMap physicalPlane p x capExampleDelta 1 y))‖ <
      1 / 100 := by
  have hybig : y ∈ ball x 10000 := ball_subset_ball (by norm_num) hy
  have hmy := collar_ball_margin x y hx hybig
  have hmz := collar_ball_margin x z hx hz
  have hdist : dist y z < 10100 := by
    have ht := dist_triangle y x z
    change dist y x < 100 at hy
    change dist z x < 10000 at hz
    rw [dist_comm x z] at ht
    linarith
  have hmargin : dist y z + 2 + capExampleEpsilon * (transitionEnd + 9) < axisRadius y := by
    linarith
  have hthreshold : 0 < capExampleEpsilon * transitionEnd :=
    mul_pos capExampleEpsilon_pos transitionEnd_pos
  have hry : 9 * capExampleEpsilon ≤ axisRadius y := by nlinarith
  have hrz : 9 * capExampleEpsilon ≤ axisRadius z := by nlinarith
  have hdiff :
      planeReferenceIsometry (planeComparisonMap physicalPlane p x capExampleDelta 1 z) -
        planeReferenceIsometry (planeComparisonMap physicalPlane p x capExampleDelta 1 y) =
      actualJ z - actualJ y := by
    rw [native_comparison_buffer p x z hxball hz,
      native_comparison_buffer p x y hxball hybig, centredPlane, centredPlane,
      map_sub, map_sub, ← actualJ_physicalPlane z hrz, ← actualJ_physicalPlane y hry]
    abel
  rw [hdiff, actualJ_geodesic_secant y z W hW (by linarith) hmargin hgeo,
    sub_self, norm_zero]
  norm_num


def actualSampleVector : TangentSpace (𝓡 3) realCollarPoint :=
  gradFun capExampleMetric capThreeCoord realCollarPoint

theorem actualSampleVector_unit :
    capExampleMetric.inner realCollarPoint actualSampleVector actualSampleVector = 1 :=
  capExample_coord_unit realCollarPoint

theorem actualSampleVector_derivative :
    mvfderiv (I := 𝓡 3) capThreeCoord realCollarPoint actualSampleVector = 1 := by
  rw [← DifferentialGeometry.Geometry.Connection.gradFun_metricDual_mvfderiv]
  exact actualSampleVector_unit

def actualSampleEndpoint : E3 :=
  intrinsicGeodesic capExampleMetric capExampleMetricNorm realCollarPoint actualSampleVector 2

theorem actualSampleEndpoint_distance : dist realCollarPoint actualSampleEndpoint = 2 := by
  have hf := actualComponent_geodesic_affine 0 realCollarPoint actualSampleVector
    actualSampleVector_unit 2 (by norm_num) (Or.inl rfl)
  change capThreeCoord actualSampleEndpoint = capThreeCoord realCollarPoint +
    2 * mvfderiv (I := 𝓡 3) capThreeCoord realCollarPoint actualSampleVector at hf
  rw [actualSampleVector_derivative, mul_one] at hf
  have hl := (WithLp.dist_fst_le (physicalPlane realCollarPoint)
    (physicalPlane actualSampleEndpoint)).trans
      (physicalPlane_nonexpanding realCollarPoint actualSampleEndpoint)
  change |capThreeCoord realCollarPoint - capThreeCoord actualSampleEndpoint| ≤
    dist realCollarPoint actualSampleEndpoint at hl
  have hs : capThreeCoord realCollarPoint - capThreeCoord actualSampleEndpoint = -2 := by
    linarith
  rw [hs] at hl
  norm_num at hl
  have hu := (lipschitzWith_one_intrinsicGeodesic capExampleMetric capExampleMetricNorm
    realCollarPoint actualSampleVector actualSampleVector_unit).dist_le_mul 2 0
  simp only [NNReal.coe_one, one_mul, intrinsicGeodesic_zero, Real.dist_eq, sub_zero] at hu
  change dist actualSampleEndpoint realCollarPoint ≤ |(2 : ℝ)| at hu
  rw [dist_comm, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hu
  exact le_antisymm hu hl

theorem actualSampleEndpoint_equation :
    intrinsicGeodesic capExampleMetric capExampleMetricNorm realCollarPoint actualSampleVector
      (dist realCollarPoint actualSampleEndpoint) = actualSampleEndpoint := by
  rw [actualSampleEndpoint_distance]
  rfl

theorem actualSampleEndpoint_native_test :
    ‖mvfderiv (I := 𝓡 3) actualJ realCollarPoint actualSampleVector -
      (dist realCollarPoint actualSampleEndpoint)⁻¹ •
        (planeReferenceIsometry (planeComparisonMap physicalPlane realCollarPoint realCollarPoint
            capExampleDelta 1 actualSampleEndpoint) -
          planeReferenceIsometry (planeComparisonMap physicalPlane realCollarPoint realCollarPoint
            capExampleDelta 1 realCollarPoint))‖ < 1 / 100 := by
  have hδ : 0 < capExampleDelta := by linarith [capExampleDelta_large]
  exact actual_native_geodesic_test realCollarPoint realCollarPoint realCollarPoint
    actualSampleEndpoint (Metric.mem_ball_self (by positivity))
    (by rw [realCollarPoint_height]; linarith) (Metric.mem_ball_self (by norm_num))
    (by rw [Metric.mem_ball, dist_comm, actualSampleEndpoint_distance]; norm_num)
    (by rw [actualSampleEndpoint_distance]; norm_num) actualSampleVector
    actualSampleVector_unit actualSampleEndpoint_equation

end DifferentialGeometry.Geometry.Collapse.EdgeCapGeodesic
