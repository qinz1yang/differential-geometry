import DifferentialGeometry.Geometry.Comparison.Soul.SbrDini
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve
import DifferentialGeometry.Geometry.Comparison.Toponogov.PrescribedDistanceSupport

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
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem intrinsic_edist_toReal (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

private theorem unit_intrinsic_dist_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    {a b : ℝ} (hab : a ≤ b) :
    dist (intrinsicGeodesic g hEnorm p u a)
      (intrinsicGeodesic g hEnorm p u b) ≤ b - a := by
  have h := intrinsicGeodesic_riemannianEDist_le g hEnorm p u hab
  rw [hu, Real.sqrt_one, one_mul] at h
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [intrinsic_edist_toReal (I := I),
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using ht

private theorem affine_segment_distance_support
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (a b : ℝ) (hab : b ≠ a)
    (hmin : dist (intrinsicGeodesic g hEnorm p u a)
      (intrinsicGeodesic g hEnorm p u b) = |b - a|) :
    let sigma := intrinsicGeodesic g hEnorm p u
    ∃ rho : M → ℝ, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ rho (sigma b) ∧
      rho (sigma b) = |b - a| ∧
      (∀ᶠ y in 𝓝 (sigma b), dist (sigma a) y ≤ rho y) ∧
      gradientFun g rho (sigma b) = |b - a|⁻¹ •
        ((b - a) • curveVelocity (I := I) sigma b) := by
  dsimp only
  let sigma := intrinsicGeodesic g hEnorm p u
  let z := sigma a
  let W : TangentSpace I z := (b - a) • curveVelocity (I := I) sigma a
  let eta := intrinsicGeodesic g hEnorm z W
  have hsigma : ContMDiff 𝓘(ℝ, ℝ) I ∞ sigma :=
    intrinsicGeodesic_contMDiff g hEnorm p u
  have heta : eta = fun t => sigma ((b - a) * t + a) := by
    funext t
    calc
      eta t = intrinsicGeodesic g hEnorm z
          (curveVelocity (I := I) sigma a) ((b - a) * t) :=
        intrinsicGeo_smul_apply g hEnorm z (curveVelocity (I := I) sigma a) (b - a) t
      _ = _ := (congrFun (intrinsicGeodesic_continuation g hEnorm p u a)
        ((b - a) * t)).symm
  have htime : (b - a) * 1 + a = b := by ring
  have heta1 : eta 1 = sigma b := by
    simp only [heta, htime]
  have hspeed : g.inner z (curveVelocity (I := I) sigma a)
      (curveVelocity (I := I) sigma a) = 1 :=
    (intrinsicGeodesic_speedSq_eq g hEnorm p u a).trans hu
  have hW : g.inner z W W = (b - a) ^ 2 := by
    dsimp only [W]
    rw [gInner_smul_self, hspeed, mul_one]
  have hWpos : 0 < g.inner z W W := by
    rw [hW]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  have hWmin : Real.sqrt (g.inner z W W) =
      (riemannianEDist I z (eta 1)).toReal := by
    rw [hW, Real.sqrt_sq_eq_abs, heta1, intrinsic_edist_toReal]
    exact hmin.symm
  have hvel : (curveVelocity (I := I) eta 1 : E) =
      (b - a) • (curveVelocity (I := I) sigma b : E) := by
    have h := curveVelocity_affine (I := I) sigma (b - a) a 1
      (hsigma.contMDiffAt.mdifferentiableAt (by simp))
    rw [htime] at h
    rw [heta]
    exact h
  have hsupp := smooth_distance_upper_support_of_minimizing_exp g hEnorm z W hWpos hWmin
  change ∃ rho : M → ℝ, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ rho (eta 1) ∧
    rho (eta 1) = Real.sqrt (g.inner z W W) ∧
    (∀ᶠ y in 𝓝 (eta 1), (riemannianEDist I z y).toReal ≤ rho y) ∧
    gradientFun g rho (eta 1) = (Real.sqrt (g.inner z W W))⁻¹ •
      curveVelocity (I := I) eta 1 at hsupp
  rw [heta1, hW, Real.sqrt_sq_eq_abs] at hsupp
  obtain ⟨rho, hrho, hvalue, hupper, hgrad⟩ := hsupp
  refine ⟨rho, hrho, hvalue, ?_, ?_⟩
  · simpa only [intrinsic_edist_toReal (I := I)] using hupper
  · change (gradientFun g rho (sigma b) : E) = _ at hgrad ⊢
    rw [hvel] at hgrad
    exact hgrad

theorem exists_two_endpoint_distance_upper_supports
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (p : M) (u : TangentSpace I p) (ell : ℝ)
    (hell : 0 < ell) (hu : g.inner p u u = 1)
    (hmin : dist p (intrinsicGeodesic g hEnorm p u ell) = ell) :
    let sigma := intrinsicGeodesic g hEnorm p u
    ∃ rho tau : M → ℝ,
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ rho p ∧
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ tau (sigma ell) ∧
      rho p + tau (sigma ell) = ell ∧
      (∀ᶠ z : M × M in 𝓝 (p, sigma ell), dist z.1 z.2 ≤ rho z.1 + tau z.2) ∧
      gradientFun g rho p = -u ∧
      gradientFun g tau (sigma ell) = curveVelocity (I := I) sigma ell := by
  dsimp only
  let sigma := intrinsicGeodesic g hEnorm p u
  let m : ℝ := ell / 2
  let z := sigma m
  have hm : 0 < m := half_pos hell
  have hmell : m < ell := half_lt_self hell
  have htwo : m + m = ell := by dsimp only [m]; ring
  have hsigma0 : sigma 0 = p := intrinsicGeodesic_zero g hEnorm p u
  have hleft : dist p z ≤ m := by
    have h := unit_intrinsic_dist_le g hEnorm p u hu hm.le
    simpa only [sigma, z, intrinsicGeodesic_zero, sub_zero] using h
  have hright : dist z (sigma ell) ≤ m := by
    have h := unit_intrinsic_dist_le g hEnorm p u hu hmell.le
    change dist z (sigma ell) ≤ ell - m at h
    linarith
  have htri : ell ≤ dist p z + dist z (sigma ell) := by
    calc
      ell = dist p (sigma ell) := hmin.symm
      _ ≤ dist p z + dist z (sigma ell) := dist_triangle p z (sigma ell)
  have hleftEq : dist z p = m := by rw [dist_comm]; linarith
  have hrightEq : dist z (sigma ell) = m := by linarith
  have hleftMin : dist (sigma m) (sigma 0) = |0 - m| := by
    rw [hsigma0, abs_of_neg (by linarith : 0 - m < 0)]
    change dist z p = -(0 - m)
    rw [hleftEq]
    ring
  have hrightMin : dist (sigma m) (sigma ell) = |ell - m| := by
    rw [abs_of_pos (sub_pos.mpr hmell)]
    change dist z (sigma ell) = ell - m
    linarith [hrightEq]
  obtain ⟨rho, hrho, hrhoval, hrhoupper, hrhograd⟩ :=
    affine_segment_distance_support g hEnorm p u hu m 0 hm.ne hleftMin
  obtain ⟨tau, htau, htauval, htauupper, htaugrad⟩ :=
    affine_segment_distance_support g hEnorm p u hu m ell hmell.ne' hrightMin
  have habsLeft : |0 - m| = m := by rw [zero_sub, abs_neg, abs_of_pos hm]
  have habsRight : |ell - m| = m := by
    rw [abs_of_pos (sub_pos.mpr hmell)]
    linarith
  simp only [intrinsicGeodesic_zero, habsLeft] at hrho hrhoval hrhoupper hrhograd
  rw [habsRight] at htauval htaugrad
  have hvel0 : (curveVelocity (I := I) sigma 0 : E) = (u : E) :=
    intrinsicGeodesic_mfderiv_zero g hEnorm p u
  dsimp only [sigma] at hvel0
  refine ⟨rho, tau, hrho, htau, by rw [hrhoval, htauval]; exact htwo, ?_, ?_, ?_⟩
  · filter_upwards [continuous_fst.continuousAt.eventually hrhoupper,
      continuous_snd.continuousAt.eventually htauupper] with w hw₁ hw₂
    have hx : dist w.1 z ≤ rho w.1 := by simpa only [dist_comm] using hw₁
    exact (dist_triangle w.1 z w.2).trans (add_le_add hx hw₂)
  · change (gradientFun g rho (intrinsicGeodesic g hEnorm p u 0) : E) = _ at hrhograd
    rw [intrinsicGeodesic_zero, hvel0, smul_smul] at hrhograd
    have hcoeff : m⁻¹ * (0 - m) = -1 := by field_simp [hm.ne']; ring
    simpa only [hcoeff, neg_one_smul] using hrhograd
  · change (gradientFun g tau (sigma ell) : E) = _ at htaugrad ⊢
    rw [smul_smul] at htaugrad
    have hcoeff : m⁻¹ * (ell - m) = 1 := by
      have heq : ell - m = m := by linarith
      rw [heq, inv_mul_cancel₀ hm.ne']
    simpa only [hcoeff, one_smul] using htaugrad

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem hasDerivWithinAt_comp_right
    (g : SmoothRiemannianMetric I M)
    {rho : M → ℝ} {xi : ℝ → M} {t : ℝ}
    (X : ℝ →L[ℝ] TangentSpace I (xi t))
    (hrho : MDifferentiableAt I 𝓘(ℝ, ℝ) rho (xi t))
    (hX : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (Ici t) t X) :
    HasDerivWithinAt (fun s => rho (xi s))
      (g.inner (xi t) (gradientFun g rho (xi t)) (X 1)) (Ici t) t := by
  have hd := DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_comp_mfderivWithin
    I rho xi (Ici t) t hrho hX.mdifferentiableWithinAt
  have hXeq := hX.mfderivWithin (uniqueDiffWithinAt_Ici t).uniqueMDiffWithinAt
  apply hd.congr_deriv
  change mvfderiv (I := I) rho (xi t)
    (mfderivWithin 𝓘(ℝ, ℝ) I xi (Ici t) t (1 : ℝ)) =
      g.inner (xi t) (gradientFun g rho (xi t)) (X 1)
  rw [hXeq]
  exact (inner_gradientFun g rho (xi t) (X 1)).symm

theorem upper_right_first_variation_of_minimizing_geodesic
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (p : M) (u : TangentSpace I p) (ell : ℝ)
    (hell : 0 < ell) (hu : g.inner p u u = 1)
    (hmin : dist p (intrinsicGeodesic g hEnorm p u ell) = ell)
    (xi zeta : ℝ → M) (t : ℝ)
    (hxi : xi t = p) (hzeta : zeta t = intrinsicGeodesic g hEnorm p u ell)
    (X : ℝ →L[ℝ] TangentSpace I p)
    (Y : ℝ →L[ℝ] TangentSpace I (intrinsicGeodesic g hEnorm p u ell))
    (hX : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (Ici t) t X)
    (hY : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I zeta (Ici t) t Y) :
    ∀ r : ℝ,
      -g.inner p (X 1) u +
        g.inner (intrinsicGeodesic g hEnorm p u ell) (Y 1)
          (curveVelocity (I := I) (intrinsicGeodesic g hEnorm p u) ell) < r →
      ∀ᶠ s in 𝓝[>] t, slope (fun s => dist (xi s) (zeta s)) t s < r := by
  obtain ⟨rho, tau, hrho, htau, hcontact, hupper, hgradRho, hgradTau⟩ :=
    exists_two_endpoint_distance_upper_supports g hEnorm p u ell hell hu hmin
  let sigma := intrinsicGeodesic g hEnorm p u
  let d : ℝ := -g.inner p (X 1) u +
    g.inner (sigma ell) (Y 1) (curveVelocity (I := I) sigma ell)
  have hRho : HasDerivWithinAt (fun s => rho (xi s))
      (-g.inner p (X 1) u) (Ici t) t := by
    have hd := hasDerivWithinAt_comp_right g (xi := xi) (t := t) (rho := rho) X
      (by rw [hxi]; exact hrho.mdifferentiableAt (by simp)) hX
    apply hd.congr_deriv
    rw [hxi, hgradRho, map_neg, neg_apply, g.symm p u (X 1)]
  have hTau : HasDerivWithinAt (fun s => tau (zeta s))
      (g.inner (sigma ell) (Y 1) (curveVelocity (I := I) sigma ell)) (Ici t) t := by
    have hd := hasDerivWithinAt_comp_right g (xi := zeta) (t := t) (rho := tau) Y
      (by rw [hzeta]; exact htau.mdifferentiableAt (by simp)) hY
    apply hd.congr_deriv
    rw [hzeta, hgradTau]
    exact g.symm (sigma ell) _ _
  let phi : ℝ → ℝ := fun s => rho (xi s) + tau (zeta s)
  have hphi : HasDerivWithinAt phi d (Ici t) t := hRho.add hTau
  have hvalue : phi t = dist (xi t) (zeta t) := by
    dsimp only [phi]
    rw [hxi, hzeta, hcontact, hmin]
  have hpair : ContinuousWithinAt (fun s => (xi s, zeta s)) (Ici t) t :=
    hX.continuousWithinAt.prodMk hY.continuousWithinAt
  have hupperWithin : ∀ᶠ s in 𝓝[Ici t] t,
      dist (xi s) (zeta s) ≤ phi s := by
    have hupper' : ∀ᶠ w : M × M in 𝓝 (xi t, zeta t),
        dist w.1 w.2 ≤ rho w.1 + tau w.2 := by
      simpa only [hxi, hzeta] using hupper
    exact hpair.eventually hupper'
  intro r hr
  exact eventually_right_slope_lt_of_upper_support hphi hvalue
    ((nhdsWithin_mono t Ioi_subset_Ici_self) hupperWithin) hr

end DifferentialGeometry.Geometry.Topology
