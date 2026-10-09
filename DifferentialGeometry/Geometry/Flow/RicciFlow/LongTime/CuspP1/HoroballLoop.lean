import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HoroballMain
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HoroballWarp
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HoroballFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HoroballCusp

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1
open GC.Endpoint DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- inclusion of the plane as `{t = 0}` in `E3`. -/
def incl : E2 →L[ℝ] E3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => WithLp.toLp 2 ![u 0, u 1, 0]
      map_add' := fun u v => by ext i; fin_cases i <;> simp
      map_smul' := fun c u => by ext i; fin_cases i <;> simp }

/-- the vertical unit vector -/
def kvec : E3 := WithLp.toLp 2 ![0, 0, 1]

@[simp] theorem incl_apply_zero (u : E2) : incl u 0 = u 0 := rfl
@[simp] theorem incl_apply_one (u : E2) : incl u 1 = u 1 := rfl
@[simp] theorem incl_apply_two (u : E2) : incl u 2 = 0 := rfl
@[simp] theorem kvec_zero : kvec 0 = 0 := rfl
@[simp] theorem kvec_one : kvec 1 = 0 := rfl
@[simp] theorem kvec_two : kvec 2 = 1 := rfl

theorem planeProj_incl (u : E2) : planeProj (incl u) = u := by
  ext j; fin_cases j <;> simp [planeProj_apply]

theorem planeProj_kvec : planeProj kvec = 0 := by
  ext j; fin_cases j <;> simp [planeProj_apply]

/-- the point `(u, t)` of `E3` -/
def emb (u : E2) (t : ℝ) : E3 := incl u + t • kvec

@[simp] theorem planeProj_emb (u : E2) (t : ℝ) : planeProj (emb u t) = u := by
  simp [emb, planeProj_incl, planeProj_kvec]

@[simp] theorem emb_two (u : E2) (t : ℝ) : emb u t 2 = t := by simp [emb]

theorem continuous_emb : Continuous (fun p : E2 × ℝ => emb p.1 p.2) := by
  unfold emb; fun_prop


/-- the clamped depth as a point of the half line -/
def hp (t : ℝ) : EuclideanHalfSpace 1 := halfPoint (max t 0) (le_max_right _ _)

theorem hp_zero : hp 0 = halfZero := by
  apply Subtype.ext; simp [hp, halfZero, halfPoint]

theorem continuous_hp : Continuous hp := by
  unfold hp halfPoint
  exact Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun _ => continuous_id.max continuous_const)) _

theorem depthPt_eq (x : E3) : depthPt x = hp (x 2) := rfl

theorem cuspChart_emb (cov : E2 → Torus) (u : E2) (t : ℝ) :
    cuspChart cov (emb u t) = (cov u, hp t) := by
  simp [cuspChart, depthPt_eq]

theorem continuous_cuspChart {cov : E2 → Torus} (hcov : Continuous cov) :
    Continuous (cuspChart cov) := by
  unfold cuspChart
  refine Continuous.prodMk (hcov.comp planeProj.continuous) ?_
  exact continuous_hp.comp (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ).continuous


theorem scF_neg (R τ : ℝ) : scF R (-τ) = -scF R τ := by
  unfold scF
  rw [neg_div, Real.sinh_neg, Real.cosh_neg]
  ring

theorem scH_neg (R τ : ℝ) : scH R (-τ) = scH R τ := by
  unfold scH
  rw [neg_div, Real.cosh_neg]

theorem scH_pos_of_ge {R : ℝ} {τ : ℝ} (h : 1 ≤ scH R τ) : 0 < scH R τ := by linarith

universe u

/-- The geodesic semicircle in `E3 = ℝ² × ℝ` over the segment from `x0` to `x1`. -/
def scCurve (x0 x1 : E2) (R τ : ℝ) : E3 :=
  incl (x0 + (1 / 2 : ℝ) • (x1 - x0)) + scF R τ • incl (‖x1 - x0‖⁻¹ • (x1 - x0)) +
    scH R τ • kvec

theorem scCurve_two (x0 x1 : E2) (R τ : ℝ) : scCurve x0 x1 R τ 2 = scH R τ := by
  simp [scCurve]

theorem scCurve_neg {x0 x1 : E2} {R a : ℝ} (hFa : scF R a = ‖x1 - x0‖ / 2)
    (hHma : scH R (-a) = 1) (hℓ : x1 ≠ x0) : scCurve x0 x1 R (-a) = emb x0 1 := by
  have hℓpos : 0 < ‖x1 - x0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hℓ)
  have h1 : incl (x0 + (1 / 2 : ℝ) • (x1 - x0)) + (-(‖x1 - x0‖ / 2)) •
      incl (‖x1 - x0‖⁻¹ • (x1 - x0)) = incl x0 := by
    rw [← map_smul, ← map_add]
    congr 1
    rw [smul_smul, show -(‖x1 - x0‖ / 2) * ‖x1 - x0‖⁻¹ = -(1 / 2) by field_simp]
    module
  simp only [scCurve, emb]
  rw [scF_neg, hFa, hHma, ← h1]

theorem scCurve_pos {x0 x1 : E2} {R a : ℝ} (hFa : scF R a = ‖x1 - x0‖ / 2)
    (hHa : scH R a = 1) (hℓ : x1 ≠ x0) : scCurve x0 x1 R a = emb x1 1 := by
  have hℓpos : 0 < ‖x1 - x0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hℓ)
  have h1 : incl (x0 + (1 / 2 : ℝ) • (x1 - x0)) + (‖x1 - x0‖ / 2) •
      incl (‖x1 - x0‖⁻¹ • (x1 - x0)) = incl x1 := by
    rw [← map_smul, ← map_add]
    congr 1
    rw [smul_smul, show ‖x1 - x0‖ / 2 * ‖x1 - x0‖⁻¹ = (1 / 2) by field_simp]
    module
  simp only [scCurve, emb]
  rw [hFa, hHa, ← h1]

theorem proj_coord_inj : ∀ w : E3, (EuclideanSpace.proj 0 : E3 →L[ℝ] ℝ) w = 0 →
    (EuclideanSpace.proj 1 : E3 →L[ℝ] ℝ) w = 0 → (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ) w = 0 →
    w = 0 := by
  intro w h0 h1 h2
  ext i; fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

theorem unit_coords (v : E2) (hv : v ≠ 0) :
    (‖v‖⁻¹ * v 0) * (‖v‖⁻¹ * v 0) + (‖v‖⁻¹ * v 1) * (‖v‖⁻¹ * v 1) = 1 := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have : ‖v‖ ^ 2 = v 0 * v 0 + v 1 * v 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, sq]
  field_simp
  nlinarith [this]

/-- `warp_curve_geodesic_CPF3` in the standard coordinates of `E3`. -/
theorem warp_curve_E3_CPF3 {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] (g : SmoothRiemannianMetric (𝓡 3) M) {F : E3 → M} {U : Set E3}
    (hU : IsOpen U) (hF : ContMDiffOn 𝓘(ℝ, E3) (𝓡 3) 2 F U)
    (hmetric : ∀ x ∈ U, ∀ v w : E3, g.inner (F x) (mfderiv 𝓘(ℝ, E3) (𝓡 3) F x v)
      (mfderiv 𝓘(ℝ, E3) (𝓡 3) F x w) = v 2 * w 2 + Real.exp (-x 2) * (v 0 * w 0 + v 1 * w 1))
    (m ev : E3) (hev2 : ev 2 = 0) (hm2 : m 2 = 0) (hev : ev 0 * ev 0 + ev 1 * ev 1 = 1)
    (R : ℝ) (hR : 0 < R) (J : Set ℝ)
    (hJ : ∀ τ ∈ J, m + scF R τ • ev + scH R τ • kvec ∈ U) :
    Geodesic.IsGeodesicOn (I := 𝓡 3) g (fun τ => F (m + scF R τ • ev + scH R τ • kvec)) J := by
  refine warp_curve_geodesic_CPF3 (EuclideanSpace.proj 0) (EuclideanSpace.proj 1)
      (EuclideanSpace.proj 2) proj_coord_inj g hU hF ?_
      m ev kvec rfl rfl rfl hev2 hm2 hev
      (scF R) (scF' R) (scF'' R) (scH R) (scH' R) (scH'' R)
      (hasDerivAt_scF R) (hasDerivAt_scF' R) (hasDerivAt_scH R) (hasDerivAt_scH' R)
      (scF''_eq R) (scH''_eq hR) J hJ
  intro x hx v w
  rw [hmetric x hx v w, warpCoeff_apply]
  rfl

/-- The semicircle is mapped by the lifted cusp map to a geodesic of the hyperbolic manifold. -/
theorem scCurve_geodesic {Hm : FiniteVolumeHyperbolicModel.{u}} (C : HyperbolicCusp)
    (ψ : CuspHalfSpace → Hm.Carrier) (hψ : ContMDiff halfCollarModel (𝓡 3) ∞ ψ)
    (hiso : ∀ p (v w : TangentSpace halfCollarModel p),
      Hm.metric.inner (ψ p) (mfderiv halfCollarModel (𝓡 3) ψ p v)
        (mfderiv halfCollarModel (𝓡 3) ψ p w) = C.metric.inner p v w)
    {cov : E2 → Torus} (hcov : ContMDiff 𝓘(ℝ, E2) torusModel ∞ cov)
    (hcovm : ∀ (x v w : E2), C.torusMetric.inner (cov x) (mfderiv 𝓘(ℝ, E2) torusModel cov x v)
        (mfderiv 𝓘(ℝ, E2) torusModel cov x w) = inner ℝ v w)
    {x0 x1 : E2} (hne : x1 ≠ x0) {R : ℝ} (hR : 0 < R) {a : ℝ}
    (hHge : ∀ τ ∈ Icc (-a) a, 1 ≤ scH R τ) :
    Geodesic.IsGeodesicOn (I := 𝓡 3) Hm.metric
      (fun τ => ψ (cuspChart cov (scCurve x0 x1 R τ))) (Ioo (-a) a) := by
  have hU : IsOpen {x : E3 | 0 < x 2} :=
    isOpen_lt continuous_const (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ).continuous
  have hG : ContMDiffOn 𝓘(ℝ, E3) halfCollarModel ∞ (cuspChart cov) {x : E3 | 0 < x 2} :=
    (hcov.comp planeProj.contDiff.contMDiff).contMDiffOn.prodMk contMDiffOn_depthPt
  have hF : ContMDiffOn 𝓘(ℝ, E3) (𝓡 3) ∞ (fun x => ψ (cuspChart cov x)) {x : E3 | 0 < x 2} :=
    hψ.comp_contMDiffOn hG
  have hv0 : x1 - x0 ≠ 0 := sub_ne_zero.mpr hne
  have hJ : ∀ τ ∈ Ioo (-a) a, incl (x0 + (1 / 2 : ℝ) • (x1 - x0)) +
      scF R τ • incl (‖x1 - x0‖⁻¹ • (x1 - x0)) + scH R τ • kvec ∈ {x : E3 | 0 < x 2} := by
    intro τ hτ
    show 0 < scCurve x0 x1 R τ 2
    rw [scCurve_two]
    exact scH_pos_of_ge (hHge τ (Ioo_subset_Icc_self hτ))
  have hmet : ∀ x ∈ {x : E3 | 0 < x 2}, ∀ v w : E3,
      Hm.metric.inner ((fun y => ψ (cuspChart cov y)) x)
        (mfderiv 𝓘(ℝ, E3) (𝓡 3) (fun y => ψ (cuspChart cov y)) x v)
        (mfderiv 𝓘(ℝ, E3) (𝓡 3) (fun y => ψ (cuspChart cov y)) x w) =
      v 2 * w 2 + Real.exp (-x 2) * (v 0 * w 0 + v 1 * w 1) := by
    intro x hx v w
    rw [cuspChart_metric_CPF3 C Hm ψ hψ hiso hcov hcovm hx v w, warpCoeff_apply]
    rfl
  have hev : (incl (‖x1 - x0‖⁻¹ • (x1 - x0))) 0 * (incl (‖x1 - x0‖⁻¹ • (x1 - x0))) 0 +
      (incl (‖x1 - x0‖⁻¹ • (x1 - x0))) 1 * (incl (‖x1 - x0‖⁻¹ • (x1 - x0))) 1 = 1 := by
    simpa using unit_coords (x1 - x0) hv0
  exact warp_curve_E3_CPF3 Hm.metric hU (hF.of_le (by norm_num)) hmet _ _ rfl rfl hev R hR _ hJ

end GC.LongTime.CuspP1
