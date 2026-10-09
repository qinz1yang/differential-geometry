import DifferentialGeometry.Geometry.Comparison.Toponogov.LowerCurvatureShortening
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
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem exists_first_order_distance_upper_support
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (o : M) (u v : TangentSpace I o) {a : ℝ} (ha : 0 < a)
    (hu : g.inner o u u = 1)
    (hmin : (riemannianEDist I o (intrinsicGeodesic g hEnorm o u a)).toReal = a) :
    ∃ w : ℝ → ℝ, w 0 = a ∧ HasDerivAt w (-g.inner o u v) 0 ∧
      ∀ᶠ t in 𝓝 0,
        (riemannianEDist I (intrinsicGeodesic g hEnorm o u a)
          (intrinsicGeodesic g hEnorm o v t)).toReal ≤ w t := by
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
  refine ⟨w, hw0, hw, ?_⟩
  have hupper0 : ∀ᶠ y in 𝓝 (tau 0),
      (riemannianEDist I (sigma a) y).toReal ≤ rho y := htau0.symm ▸ hupper
  exact htau.continuous.continuousAt.eventually hupper0

section
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem hyperbolic_support_cosine_limit
    {w : ℝ → ℝ} {k a c : ℝ} (hk : 0 < k) (ha : 0 < a)
    (hw0 : w 0 = a) (hw : HasDerivAt w (-c) 0) :
    Tendsto (fun t =>
      (Real.cosh (k * a) * Real.cosh (k * t) - Real.cosh (k * w t)) /
        (Real.sinh (k * a) * Real.sinh (k * t))) (𝓝[>] 0) (𝓝 c) := by
  let F : ℝ → ℝ := fun t =>
    Real.cosh (k * a) * Real.cosh (k * t) - Real.cosh (k * w t)
  let G : ℝ → ℝ := fun t => Real.sinh (k * t)
  have hF0 : F 0 = 0 := by simp [F, hw0]
  have hG0 : G 0 = 0 := by simp [G]
  have hF : HasDerivAt F (k * Real.sinh (k * a) * c) 0 := by
    convert! ((((hasDerivAt_id (0 : ℝ)).const_mul k).cosh).const_mul
      (Real.cosh (k * a))).sub ((hw.const_mul k).cosh) using 1
    simp only [id_eq, mul_zero, Real.sinh_zero, zero_mul, hw0, mul_one, zero_sub]
    ring
  have hG : HasDerivAt G k 0 := by
    simpa only [G, id_eq, mul_zero, Real.cosh_zero, one_mul, mul_one] using
      ((hasDerivAt_id (0 : ℝ)).const_mul k).sinh
  have hf := hF.tendsto_slope_zero_right
  have hg := hG.tendsto_slope_zero_right
  simp only [zero_add, hF0, hG0, sub_zero, smul_eq_mul] at hf hg
  have hlim := (hf.div hg hk.ne').div_const (Real.sinh (k * a))
  have hs : Real.sinh (k * a) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos hk ha)).ne'
  have hvalue : (k * Real.sinh (k * a) * c / k) / Real.sinh (k * a) = c := by
    field_simp
  rw [hvalue] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  dsimp only [Pi.div_apply, F, G]
  field_simp

end

theorem hyperbolicComparisonAngle_le_arccos_inner_of_sectional_lower_bound_on_minimizing_lenses
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (o : M) (u v : TangentSpace I o) {k a b : ℝ}
    (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : (riemannianEDist I o (intrinsicGeodesic g hEnorm o u a)).toReal = a)
    (hminB : (riemannianEDist I o (intrinsicGeodesic g hEnorm o v b)).toReal = b)
    (hsec : ∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) b, ∀ y : M,
      riemannianEDist I (intrinsicGeodesic g hEnorm o u s) y +
        riemannianEDist I y (intrinsicGeodesic g hEnorm o v t) =
        riemannianEDist I (intrinsicGeodesic g hEnorm o u s)
          (intrinsicGeodesic g hEnorm o v t) →
      SectionalBoundedBelowAt (I := I) g y (-k ^ 2)) :
    hyperbolicComparisonAngle k a b
      (riemannianEDist I (intrinsicGeodesic g hEnorm o u a)
        (intrinsicGeodesic g hEnorm o v b)).toReal ≤ Real.arccos (g.inner o u v) := by
  obtain ⟨w, hw0, hw, hupper⟩ :=
    exists_first_order_distance_upper_support g hEnorm o u v ha hu hminA
  have hlim := Real.continuous_arccos.continuousAt.tendsto.comp
    (hyperbolic_support_cosine_limit hk ha hw0 hw)
  apply ge_of_tendsto hlim
  filter_upwards [Ioc_mem_nhdsGT hb, nhdsWithin_le_nhds hupper] with t ht htupper
  have hshort := hyperbolicComparisonAngle_shortening_of_sectional_lower_bound_on_minimizing_lenses
    g hEnorm o u v k a a t b hk ha le_rfl ht.1 ht.2 hu hv hminA hminB hsec
  apply hshort.trans
  apply Real.arccos_le_arccos
  apply div_le_div_of_nonneg_right _
    (mul_nonneg (Real.sinh_pos_iff.mpr (mul_pos hk ha)).le
      (Real.sinh_pos_iff.mpr (mul_pos hk ht.1)).le)
  apply sub_le_sub_left
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg (mul_nonneg hk.le ENNReal.toReal_nonneg),
    abs_of_nonneg (mul_nonneg hk.le (ENNReal.toReal_nonneg.trans htupper))]
  exact mul_le_mul_of_nonneg_left htupper hk.le

end DifferentialGeometry.Geometry.Comparison.Toponogov
