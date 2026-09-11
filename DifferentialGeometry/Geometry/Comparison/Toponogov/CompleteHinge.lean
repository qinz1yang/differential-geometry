import DifferentialGeometry.Geometry.Comparison.Toponogov.SquaredDistanceConvexity
import DifferentialGeometry.Geometry.Comparison.Toponogov.PrescribedDistanceSupport
import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] [ConnectedSpace M]

theorem complete_hinge_sq
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (o : M) (u v : TangentSpace I o) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hmin : (riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o u a)).toReal = a) :
    (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a)
      (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal ^ 2 ≤
      a ^ 2 + b ^ 2 - 2 * a * b * g.inner o u v := by
  let sigma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm o u
  let tau : ℝ → M := intrinsicGeodesic (I := I) g hEnorm o v
  have hsigma : ContMDiff 𝓘(ℝ, ℝ) I ∞ sigma :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm o u
  have htau : ContMDiff 𝓘(ℝ, ℝ) I ∞ tau :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm o v
  have hsigma0 : sigma 0 = o := intrinsicGeodesic_zero (I := I) g hEnorm o u
  have htau0 : tau 0 = o := intrinsicGeodesic_zero (I := I) g hEnorm o v
  have hu0 : (curveVelocity (I := I) sigma 0 : E) = (u : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm o u
  have hv0 : (curveVelocity (I := I) tau 0 : E) = (v : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm o v
  have hspeed : g.inner (sigma a)
      (curveVelocity (I := I) sigma a) (curveVelocity (I := I) sigma a) = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm o u a).trans hu
  let W : TangentSpace I (sigma a) := (-a) • curveVelocity (I := I) sigma a
  let rev : ℝ → M := intrinsicGeodesic (I := I) g hEnorm (sigma a) W
  have hrev : rev = fun t => sigma ((-a) * t + a) := by
    funext t
    calc
      rev t = intrinsicGeodesic (I := I) g hEnorm (sigma a)
          (curveVelocity (I := I) sigma a) ((-a) * t) :=
        intrinsicGeo_smul_apply (I := I) g hEnorm (sigma a)
          (curveVelocity (I := I) sigma a) (-a) t
      _ = _ := (congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm o u a)
        ((-a) * t)).symm
  have htime : (-a) * 1 + a = 0 := by ring
  have hrev1 : rev 1 = o := by
    rw [hrev]
    change sigma ((-a) * 1 + a) = o
    rw [htime, hsigma0]
  have hWnorm : g.inner (sigma a) W W = a ^ 2 := by
    dsimp only [W]
    rw [gInner_smul_self (I := I) g (sigma a), hspeed, mul_one, neg_sq]
  have hWpos : 0 < g.inner (sigma a) W W := hWnorm.symm ▸ sq_pos_of_pos ha
  have hrevMin : Real.sqrt (g.inner (sigma a) W W) =
      (riemannianEDist I (sigma a) (rev 1)).toReal := by
    rw [hWnorm, Real.sqrt_sq_eq_abs, abs_of_pos ha, hrev1, riemannianEDist_comm]
    exact hmin.symm
  have hrevVel : (curveVelocity (I := I) rev 1 : E) = (-a) • (u : E) := by
    have h := curveVelocity_affine (I := I) sigma (-a) a 1
      (hsigma.contMDiffAt.mdifferentiableAt (by simp))
    rw [htime] at h
    change (curveVelocity (I := I) (fun t => sigma ((-a) * t + a)) 1 : E) =
      (-a) • (curveVelocity (I := I) sigma 0 : E) at h
    rw [hu0] at h
    rw [hrev]
    exact h
  have hsupp := smooth_distance_upper_support_of_minimizing_exp (I := I)
    g hEnorm (sigma a) W hWpos hrevMin
  change ∃ rho : M → ℝ, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ rho (rev 1) ∧
    rho (rev 1) = Real.sqrt (g.inner (sigma a) W W) ∧
    (∀ᶠ y in 𝓝 (rev 1), (riemannianEDist I (sigma a) y).toReal ≤ rho y) ∧
    gradientFun (I := I) g rho (rev 1) =
      (Real.sqrt (g.inner (sigma a) W W))⁻¹ • curveVelocity (I := I) rev 1 at hsupp
  rw [hrev1, hWnorm, Real.sqrt_sq_eq_abs, abs_of_pos ha] at hsupp
  obtain ⟨rho, hrho, hvalue, hupper, hgradR⟩ := hsupp
  have hgrad : gradientFun (I := I) g rho o = -u := by
    change (gradientFun (I := I) g rho o : E) = _ at hgradR ⊢
    rw [hrevVel, smul_smul] at hgradR
    have hc : a⁻¹ * (-a) = -1 := by field_simp
    rw [hc, neg_one_smul] at hgradR
    exact hgradR
  let w : ℝ → ℝ := fun t => rho (tau t)
  have hw0 : w 0 = a := by
    dsimp only [w]
    rw [htau0, hvalue]
  have hw : HasDerivAt w (-g.inner o u v) 0 := by
    have hrho0 : MDifferentiableAt I 𝓘(ℝ, ℝ) rho (tau 0) := by
      rw [htau0]
      exact hrho.mdifferentiableAt (by simp)
    have hd := DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along
      I rho tau 0 hrho0 (htau.contMDiffAt.mdifferentiableAt (by simp))
    refine hd.congr_deriv ?_
    change mvfderiv (I := I) rho (tau 0) (curveVelocity (I := I) tau 0) =
      -g.inner o u v
    rw [← inner_gradientFun (I := I) g rho (tau 0) (curveVelocity (I := I) tau 0)]
    rw [hv0, htau0, hgrad, map_neg, neg_apply]
  let psi : ℝ → ℝ := fun t => t ^ 2 - w t ^ 2
  let F : ℝ → ℝ := fun t => t ^ 2 - (riemannianEDist I (sigma a) (tau t)).toReal ^ 2
  have hF : ConvexOn ℝ (Icc 0 b) F :=
    convexOn_sq_sub_sq_riemannianEDist_intrinsicGeodesic (I := I)
      g hEnorm hsec (sigma a) o v hv (convex_Icc 0 b)
  have hF0 : F 0 = -a ^ 2 := by
    dsimp only [F]
    rw [htau0, riemannianEDist_comm, hmin]
    ring
  have hpsi0 : psi 0 = F 0 := by
    dsimp only [psi]
    rw [hw0, hF0]
    ring
  have hpsiD : HasDerivAt psi (2 * a * g.inner o u v) 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).pow 2).sub (hw.pow 2)) using 1
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, hw0]
    ring
  have hupper0 : ∀ᶠ y in 𝓝 (tau 0),
      (riemannianEDist I (sigma a) y).toReal ≤ rho y := htau0.symm ▸ hupper
  have hbelow : ∀ᶠ t in 𝓝[>] (0 : ℝ), psi t ≤ F t := by
    filter_upwards [nhdsWithin_le_nhds (htau.continuous.continuousAt.eventually hupper0)]
      with t ht
    have hsq := mul_self_le_mul_self ENNReal.toReal_nonneg ht
    dsimp only [psi, F, w]
    nlinarith
  have hend := convex_endpoint_lower_support hb hF hpsiD.hasDerivWithinAt hpsi0 hbelow
  rw [hF0] at hend
  dsimp only [F] at hend
  change (riemannianEDist I (sigma a) (tau b)).toReal ^ 2 ≤ _
  nlinarith

theorem complete_equal_arm_norm
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (o : M) (u v : TangentSpace I o) (a : ℝ)
    (ha : 0 < a) (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hmin : (riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o u a)).toReal = a) :
    (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a)
      (intrinsicGeodesic (I := I) g hEnorm o v a)).toReal ≤
      a * Real.sqrt (g.inner o (u - v) (u - v)) := by
  have h := complete_hinge_sq (I := I) g hEnorm hsec o u v a a ha ha hu hv hmin
  have hsub : g.inner o (u - v) (u - v) = 2 - 2 * g.inner o u v := by
    rw [ContinuousLinearMap.map_sub₂, map_sub, map_sub, hu, hv, g.symm o v u]
    ring
  have hsquare : (a * Real.sqrt (g.inner o (u - v) (u - v))) ^ 2 =
      a ^ 2 + a ^ 2 - 2 * a * a * g.inner o u v := by
    rw [mul_pow, Real.sq_sqrt (gInner_self_nonneg (I := I) g o (u - v)), hsub]
    ring
  rw [← hsquare] at h
  have hnonneg : 0 ≤ a * Real.sqrt (g.inner o (u - v) (u - v)) :=
    mul_nonneg ha.le (Real.sqrt_nonneg _)
  exact (sq_le_sq₀ ENNReal.toReal_nonneg hnonneg).1 h

theorem complete_equal_arm_angle
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (o : M) (u v : TangentSpace I o) (a : ℝ)
    (ha : 0 < a) (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hmin : (riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o u a)).toReal = a) :
    (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a)
      (intrinsicGeodesic (I := I) g hEnorm o v a)).toReal ≤
      2 * a * Real.sin (Real.arccos (g.inner o u v) / 2) := by
  have hsub : g.inner o (u - v) (u - v) = 2 - 2 * g.inner o u v := by
    rw [ContinuousLinearMap.map_sub₂, map_sub, map_sub, hu, hv, g.symm o v u]
    ring
  have hadd : g.inner o (u + v) (u + v) = 2 + 2 * g.inner o u v := by
    rw [ContinuousLinearMap.map_add₂, map_add, map_add, hu, hv, g.symm o v u]
    ring
  have hc : g.inner o u v ∈ Icc (-1) 1 := by
    have hplus := gInner_self_nonneg (I := I) g o (u + v)
    have hminus := gInner_self_nonneg (I := I) g o (u - v)
    rw [hadd] at hplus
    rw [hsub] at hminus
    constructor <;> linarith
  let theta : ℝ := Real.arccos (g.inner o u v)
  have htheta0 : 0 ≤ theta := Real.arccos_nonneg _
  have htheta_pi : theta ≤ Real.pi := Real.arccos_le_pi _
  have hsin : 0 ≤ Real.sin (theta / 2) := Real.sin_nonneg_of_mem_Icc
    ⟨div_nonneg htheta0 (by norm_num), by linarith [Real.pi_pos]⟩
  have hcos : Real.cos theta = g.inner o u v := Real.cos_arccos hc.1 hc.2
  have hdouble := Real.cos_two_mul (theta / 2)
  have htime : 2 * (theta / 2) = theta := by ring
  rw [htime] at hdouble
  have hnorm : g.inner o (u - v) (u - v) = (2 * Real.sin (theta / 2)) ^ 2 := by
    rw [hsub]
    nlinarith [Real.sin_sq_add_cos_sq (theta / 2)]
  have h := complete_equal_arm_norm (I := I) g hEnorm hsec o u v a ha hu hv hmin
  rw [hnorm, Real.sqrt_sq (mul_nonneg (by norm_num) hsin)] at h
  change (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a)
    (intrinsicGeodesic (I := I) g hEnorm o v a)).toReal ≤ 2 * a * Real.sin (theta / 2)
  nlinarith only [h]

end DifferentialGeometry.Geometry.Comparison.Toponogov

end
