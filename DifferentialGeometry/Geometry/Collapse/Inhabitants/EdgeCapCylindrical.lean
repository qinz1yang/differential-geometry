import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapCarrier
import DifferentialGeometry.Topology.Diffeomorph.LinearIsometrySphere
import DifferentialGeometry.Topology.Ehresmann.CircleFibreTransport
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import DifferentialGeometry.Geometry.Metric.PolarCoordinates

/-! Actual angular and positive-radius cap maps with the genuine cylindrical metric. -/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open DifferentialGeometry.Geometry.Collapse.EdgeCapCarrier
open scoped Manifold ContDiff InnerProductSpace
namespace DifferentialGeometry.Geometry.Collapse.EdgeCapCylindrical

local instance capPlaneDimensionFact : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp⟩
local instance capComplexDimensionFact : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩

def capAngle : AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ Metric.sphere (0 : E2) 1 :=
  AddCircle.diffeomorphCircle.trans
    (LinearIsometryEquiv.sphereDiffeomorph (n := 1) Complex.orthonormalBasisOneI.repr)

theorem capAngle_coe (t : ℝ) :
    (capAngle (t : AddCircle (1 : ℝ))).val =
      Complex.orthonormalBasisOneI.repr (Circle.exp (2 * Real.pi * t)).val := by
  change Complex.orthonormalBasisOneI.repr
    (AddCircle.diffeomorphCircle (t : AddCircle (1 : ℝ))).val = _
  rw [DifferentialGeometry.Topology.Ehresmann.CircleFibre.diffeomorphCircle_coe]

theorem capAngle_smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ capAngle := capAngle.contMDiff

theorem capAngle_surjective (q : Metric.sphere (0 : E2) 1) :
    ∃ a : AddCircle (1 : ℝ), capAngle a = q :=
  capAngle.surjective q

theorem capAngle_cover_derivative (t : ℝ) :
    HasDerivAt (fun s : ℝ => (capAngle (s : AddCircle (1 : ℝ))).val)
      (Complex.orthonormalBasisOneI.repr
        ((Circle.exp (2 * Real.pi * t)).val * ((2 * Real.pi : ℝ) : ℂ) * Complex.I)) t := by
  have hz := (((hasDerivAt_id t).const_mul (2 * Real.pi)).ofReal_comp.mul_const Complex.I).cexp
  let A : ℂ →L[ℝ] E2 :=
    Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.toContinuousLinearMap
  have hA := A.hasFDerivAt.comp_hasDerivAt t hz
  convert hA using 1
  · funext s
    rw [capAngle_coe, Circle.coe_exp]
    rfl
  · rw [Circle.coe_exp]
    simp only [A, id_eq, mul_one, mul_assoc]
    rfl

theorem capAngle_cover_speed (t : ℝ) :
    ‖deriv (fun s : ℝ => (capAngle (s : AddCircle (1 : ℝ))).val) t‖ = 2 * Real.pi := by
  rw [(capAngle_cover_derivative t).deriv,
    Complex.orthonormalBasisOneI.repr.norm_map, norm_mul, norm_mul,
    Circle.norm_coe, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  ring

theorem capAngle_cover_round_inner (t a b : ℝ) :
    (roundMetric (E := E2) (n := 1)).inner (capAngle (t : AddCircle (1 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun s : ℝ => capAngle (s : AddCircle (1 : ℝ))) t a)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun s : ℝ => capAngle (s : AddCircle (1 : ℝ))) t b) =
        (2 * Real.pi) ^ 2 * a * b := by
  let f : ℝ → Metric.sphere (0 : E2) 1 := fun s => capAngle (s : AddCircle (1 : ℝ))
  let z := deriv (fun s : ℝ => (capAngle (s : AddCircle (1 : ℝ))).val) t
  have hf : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ f :=
    capAngle.contMDiff.comp AddCircle.contMDiff_coe
  have hcoe : ContMDiff (𝓡 1) (𝓡 2) ∞
      (Subtype.val : Metric.sphere (0 : E2) 1 → E2) := contMDiff_coe_sphere
  have hc : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun s : ℝ => (f s).val) t =
      (dIncl (n := 1) (f t)).comp (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) f t) := by
    exact mfderiv_comp t
      (hcoe.mdifferentiableAt (by decide))
      (hf.mdifferentiableAt (by decide))
  have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun s : ℝ => (f s).val) t =
      ContinuousLinearMap.toSpanSingleton ℝ z := by
    have hder := (capAngle_cover_derivative t).differentiableAt.hasDerivAt
    exact hder.hasFDerivAt.hasMFDerivAt.mfderiv
  have ha : @Eq E2 (dIncl (n := 1) (f t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) f t a)) (a • z) := by
    exact congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] E2 => L a)
      (hc.symm.trans hd)
  have hb : @Eq E2 (dIncl (n := 1) (f t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) f t b)) (b • z) := by
    exact congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] E2 => L b)
      (hc.symm.trans hd)
  change (roundMetric (E := E2) (n := 1)).inner (f t)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) f t a) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) f t b) = _
  rw [roundMetric_inner, ha, hb, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hz : ‖z‖ = 2 * Real.pi := capAngle_cover_speed t
  rw [hz]
  ring

theorem capAngle_round_pullback (q : AddCircle (1 : ℝ))
    (u v : TangentSpace 𝓘(ℝ, ℝ) q) :
    (roundMetric (E := E2) (n := 1)).inner (capAngle q)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) capAngle q u)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) capAngle q v) =
        (2 * Real.pi) ^ 2 * AddCircle.flatMetric.inner q u v := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective q
  change (t : AddCircle (1 : ℝ)) = q at ht
  subst q
  obtain ⟨a, ha⟩ := (AddCircle.bijective_mfderiv_coe t).2 u
  obtain ⟨b, hb⟩ := (AddCircle.bijective_mfderiv_coe t).2 v
  let ar : ℝ := a
  let br : ℝ := b
  rw [← ha, ← hb]
  have hd := mfderiv_comp t (capAngle.contMDiff.mdifferentiableAt (by decide))
    (AddCircle.contMDiff_coe.mdifferentiableAt (by decide))
  have H := capAngle_cover_round_inner t ar br
  change (roundMetric (E := E2) (n := 1)).inner (capAngle (t : AddCircle (1 : ℝ)))
    ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1)
      (capAngle ∘ fun s : ℝ => (s : AddCircle (1 : ℝ))) t) a)
    ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1)
      (capAngle ∘ fun s : ℝ => (s : AddCircle (1 : ℝ))) t) b) = _ at H
  rw [hd] at H
  have hl : (roundMetric (E := E2) (n := 1)).inner (capAngle (t : AddCircle (1 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) capAngle (t : AddCircle (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) t a))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) capAngle (t : AddCircle (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) t b)) =
        (2 * Real.pi) ^ 2 * (ar * br) := by
    simpa only [ContinuousLinearMap.comp_apply, mul_assoc] using H
  have hflat := AddCircle.flatMetric_inner_mfderiv_coe t ar br
  exact hl.trans (congrArg (fun r : ℝ => (2 * Real.pi) ^ 2 * r) hflat.symm)

open DifferentialGeometry.PDE.RicciFlow.StandardCap
theorem cap_plane_polar_inner {e : E2} (he : ‖e‖ = 1) {v w : E2}
    (hv : ⟪e, v⟫_ℝ = 0) (hw : ⟪e, w⟫_ℝ = 0) {r : ℝ} (hr : 0 < r) (s t : ℝ) :
    surfaceMetric.inner (r • e) (s • e + r • v) (t • e + r • w) =
      s * t + warpingFunction r ^ 2 * ⟪v, w⟫_ℝ := by
  have he0 : e ≠ 0 := norm_ne_zero_iff.mp (by rw [he]; norm_num)
  rw [surfaceMetric_inner_radial (smul_ne_zero hr.ne' he0)]
  exact radialBilinearField_polar _ he hv hw hr s t

theorem cap_plane_cylindrical_inner {e : E2} (he : ‖e‖ = 1) {v w : E2}
    (hv : ⟪e, v⟫_ℝ = 0) (hw : ⟪e, w⟫_ℝ = 0) {r : ℝ}
    (hr : transitionEnd ≤ r) (s t : ℝ) :
    surfaceMetric.inner (r • e) (s • e + r • v) (t • e + r • w) =
      s * t + 2 * ⟪v, w⟫_ℝ := by
  rw [cap_plane_polar_inner he hv hw (transitionEnd_pos.trans_le hr) s t,
    warpingFunction_eq_sqrt_two hr, Real.sq_sqrt (by norm_num)]

theorem scaled_cap_cylindrical_inner (ε : ℝ) (hε : 0 < ε)
    {e : E2} (he : ‖e‖ = 1) {v w : E2}
    (hv : ⟪e, v⟫_ℝ = 0) (hw : ⟪e, w⟫_ℝ = 0) {r : ℝ}
    (hr : transitionEnd ≤ r) (s t : ℝ) :
    (scaledCapMetric ε hε).inner (r • e)
      ((s / ε) • e + r • v) ((t / ε) • e + r • w) =
        s * t + 2 * ε ^ 2 * ⟪v, w⟫_ℝ := by
  change ε ^ 2 * surfaceMetric.inner (r • e)
    ((s / ε) • e + r • v) ((t / ε) • e + r • w) = _
  rw [cap_plane_cylindrical_inner he hv hw hr]
  field_simp [ne_of_gt hε]

def capPhysicalRadius (ε : ℝ) (hε : 0 < ε) : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ :=
  (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
    (Units.mk0 ε⁻¹ (inv_ne_zero hε.ne'))).toDiffeomorph

def capPolarPartial (ε : ℝ) (hε : 0 < ε) :
    PartialDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2)
      (AddCircle (1 : ℝ) × ℝ) E2 ∞ :=
  (capAngle.prodCongr (capPhysicalRadius ε hε)).toPartialDiffeomorph.trans
    (euclideanPolarDiffeomorph (E := E2) (n := 1))

theorem capPolarPartial_apply (ε : ℝ) (hε : 0 < ε) (q : AddCircle (1 : ℝ) × ℝ) :
    capPolarPartial ε hε q = (ε⁻¹ * q.2) • (capAngle q.1).val := rfl

theorem capPolarPartial_source (ε : ℝ) (hε : 0 < ε) {q : AddCircle (1 : ℝ) × ℝ} :
    q ∈ (capPolarPartial ε hε).source ↔ 0 < q.2 := by
  change ((q ∈ Set.univ) ∧ 0 < ε⁻¹ * q.2) ↔ 0 < q.2
  simp only [Set.mem_univ, true_and]
  exact mul_pos_iff_of_pos_left (inv_pos.mpr hε)

theorem capPhysicalRadius_mfderiv (ε : ℝ) (hε : 0 < ε) (t s : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (capPhysicalRadius ε hε) t s = ε⁻¹ * s := by
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
      (Units.mk0 ε⁻¹ (inv_ne_zero hε.ne'))).toContinuousLinearMap t s = _
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rfl

def capRadialVelocity (ε s : ℝ) : ℝ := ε⁻¹ * s

theorem capPolarPartial_mfderiv (ε : ℝ) (hε : 0 < ε) (q : AddCircle (1 : ℝ) × ℝ)
    (v : TangentSpace (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) q) :
    mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) (capPolarPartial ε hε) q v =
      capRadialVelocity ε v.2 • (capAngle q.1).val + (ε⁻¹ * q.2) •
        dIncl (n := 1) (capAngle q.1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) capAngle q.1 v.1) := by
  let D := capAngle.prodCongr (capPhysicalRadius ε hε)
  have hF : (capPolarPartial ε hε : (AddCircle (1 : ℝ) × ℝ) → E2) =
      euclideanPolarMap ∘ D := rfl
  rw [hF, mfderiv_comp q
    ((euclideanPolarMap_smooth (E := E2) (n := 1)).mdifferentiableAt (by decide))
    (D.contMDiff.mdifferentiableAt (by decide))]
  change (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) euclideanPolarMap (D q))
    (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) D q v) = _
  have hD : (D : (AddCircle (1 : ℝ) × ℝ) → (Metric.sphere (0 : E2) 1 × ℝ)) =
      Prod.map capAngle (capPhysicalRadius ε hε) := rfl
  rw [hD, mfderiv_prodMap
    (capAngle.contMDiff.mdifferentiableAt (by decide))
    ((capPhysicalRadius ε hε).contMDiff.mdifferentiableAt (by decide))]
  rw [euclideanPolarMap_mfderiv]
  simp only [Prod.map_fst, Prod.map_snd]
  change (fun a : ℝ => a • (capAngle q.1).val)
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (capPhysicalRadius ε hε) q.2 v.2) + (capPhysicalRadius ε hε q.2) •
      dIncl (n := 1) (capAngle q.1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) capAngle q.1 v.1) = _
  have hs : @Eq ℝ (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (capPhysicalRadius ε hε) q.2 v.2)
      (capRadialVelocity ε v.2) := capPhysicalRadius_mfderiv ε hε q.2 v.2
  exact (congrArg (fun a : ℝ => a • (capAngle q.1).val + (capPhysicalRadius ε hε q.2) •
    dIncl (n := 1) (capAngle q.1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) capAngle q.1 v.1)) hs).trans rfl

theorem cap_selected_angular_coefficient :
    2 * capExampleEpsilon ^ 2 * (2 * Real.pi) ^ 2 = smallFlatCircleScale ^ 2 := by
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  simp only [capExampleEpsilon, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [hp]

theorem capPolarPartial_selected_metric (q : AddCircle (1 : ℝ) × ℝ)
    (hq : transitionEnd ≤ capExampleEpsilon⁻¹ * q.2)
    (v w : TangentSpace (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) q) :
    (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).inner
      (capPolarPartial capExampleEpsilon capExampleEpsilon_pos q)
      (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2)
        (capPolarPartial capExampleEpsilon capExampleEpsilon_pos) q v)
      (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2)
        (capPolarPartial capExampleEpsilon capExampleEpsilon_pos) q w) =
      (smallFlatCircleMetric.prod (euclideanMetric (E := ℝ))).inner q v w := by
  let ε : ℝ := capExampleEpsilon
  let r : ℝ := ε⁻¹ * q.2
  let e : E2 := (capAngle q.1).val
  let av := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) capAngle q.1 v.1
  let aw := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) capAngle q.1 w.1
  let s : ℝ := v.2
  let t : ℝ := w.2
  have hV : @Eq E2 (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2)
      (capPolarPartial ε capExampleEpsilon_pos) q v)
      ((s / ε) • e + r • dIncl (n := 1) (capAngle q.1) av) := by
    have H := capPolarPartial_mfderiv ε capExampleEpsilon_pos q v
    change @Eq E2 _ _ at H
    simpa only [capRadialVelocity, s, r, av, e, div_eq_mul_inv, mul_comm] using H
  have hW : @Eq E2 (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2)
      (capPolarPartial ε capExampleEpsilon_pos) q w)
      ((t / ε) • e + r • dIncl (n := 1) (capAngle q.1) aw) := by
    have H := capPolarPartial_mfderiv ε capExampleEpsilon_pos q w
    change @Eq E2 _ _ at H
    simpa only [capRadialVelocity, t, r, aw, e, div_eq_mul_inv, mul_comm] using H
  have hpoint : capPolarPartial ε capExampleEpsilon_pos q = r • e := rfl
  have hm := congrArg₂ (fun a b : E2 =>
    (scaledCapMetric ε capExampleEpsilon_pos).inner
      (capPolarPartial ε capExampleEpsilon_pos q) a b) hV hW
  have hp := congrArg (fun x : E2 => (scaledCapMetric ε capExampleEpsilon_pos).inner x
    ((s / ε) • e + r • dIncl (n := 1) (capAngle q.1) av)
    ((t / ε) • e + r • dIncl (n := 1) (capAngle q.1) aw)) hpoint
  have hc := scaled_cap_cylindrical_inner ε capExampleEpsilon_pos
    (norm_eq_of_mem_sphere (capAngle q.1))
    (dIncl_orth (capAngle q.1) av) (dIncl_orth (capAngle q.1) aw) hq s t
  have hang : @Eq ℝ
      ⟪dIncl (n := 1) (capAngle q.1) av, dIncl (n := 1) (capAngle q.1) aw⟫_ℝ
      ((2 * Real.pi) ^ 2 * AddCircle.flatMetric.inner q.1 v.1 w.1) :=
    (roundMetric_inner (capAngle q.1) av aw).symm.trans (capAngle_round_pullback q.1 v.1 w.1)
  have hall := (hm.trans hp).trans (hc.trans
    (congrArg (fun a : ℝ => s * t + 2 * ε ^ 2 * a) hang))
  have hcoeff : 2 * ε ^ 2 * (2 * Real.pi) ^ 2 = smallFlatCircleScale ^ 2 :=
    cap_selected_angular_coefficient
  rw [SmoothRiemannianMetric.prod_inner]
  have hreal : @Eq ℝ ((euclideanMetric (E := ℝ)).inner q.2 v.2 w.2) (s * t) := by
    change ⟪s, t⟫_ℝ = s * t
    exact Real.inner_apply s t
  rw [hreal]
  change _ = smallFlatCircleScale ^ 2 * AddCircle.flatMetric.inner q.1 v.1 w.1 + s * t
  exact hall.trans (by rw [← mul_assoc, hcoeff]; ring)

end DifferentialGeometry.Geometry.Collapse.EdgeCapCylindrical
