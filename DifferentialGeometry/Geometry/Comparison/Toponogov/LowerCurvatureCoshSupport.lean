import DifferentialGeometry.Geometry.Comparison.Toponogov.LowerCurvatureDistanceSupport
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness

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

namespace DifferentialGeometry

private theorem second_deriv_cosh_comp {f : ℝ → ℝ} {x k : ℝ}
    (hf : ContDiffAt ℝ 2 f x) :
    deriv (deriv (fun t => Real.cosh (k * f t))) x =
      k ^ 2 * Real.cosh (k * f x) * (deriv f x) ^ 2 +
        k * Real.sinh (k * f x) * deriv (deriv f) x := by
  have hfDiff : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ f t :=
    (hf.eventually (by norm_num)).mono fun _ h => h.differentiableAt (by norm_num)
  have hfirst : deriv (fun t => Real.cosh (k * f t)) =ᶠ[𝓝 x]
      fun t => Real.sinh (k * f t) * (k * deriv f t) := by
    filter_upwards [hfDiff] with t ht
    exact (ht.hasDerivAt.const_mul k |>.cosh).deriv
  have hsecond : DifferentiableAt ℝ (deriv f) x :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd := (((hf.differentiableAt (by norm_num)).hasDerivAt.const_mul k).sinh).mul
    (hsecond.hasDerivAt.const_mul k)
  rw [hfirst.deriv_eq]
  convert! hd.deriv using 1; ring

private theorem modelRadialLogDeriv_neg_sq {k r : ℝ} (hk : 0 < k) :
    modelRadialLogDeriv (-k ^ 2) r = k * Real.cosh (k * r) / Real.sinh (k * r) := by
  rw [modelRadialLogDeriv_of_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hk.ne')),
    neg_neg, Real.sqrt_sq hk.le]
  ring

private theorem exists_small_fraction_modelRadialLogDeriv {K r delta : ℝ}
    (hK : K ≤ 0) (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧
      modelRadialLogDeriv K ((1 - s) * r) ≤ modelRadialLogDeriv K r + delta := by
  have hc : ContinuousAt (modelRadialLogDeriv K) r :=
    (continuous_modelRadialDeriv K).continuousAt.div
      (continuous_modelRadial K).continuousAt (modelRadial_pos hK hr).ne'
  have ht : Tendsto (fun s : ℝ => modelRadialLogDeriv K ((1 - s) * r)) (𝓝 0)
      (𝓝 (modelRadialLogDeriv K r)) := by
    apply hc.tendsto.comp
    convert! (((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 0) (𝓝 0))).mul_const r) using 1; simp
  have he := ht.eventually (gt_mem_nhds (lt_add_of_pos_right _ hdelta))
  have hi : ∀ᶠ s : ℝ in 𝓝[>] 0, s < 1 / 2 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds (by norm_num))
  have hp : ∀ᶠ s : ℝ in 𝓝[>] 0, s ∈ Ioi 0 := self_mem_nhdsWithin
  obtain ⟨s, hs, hb, hm⟩ := (hp.and (hi.and (he.filter_mono nhdsWithin_le_nhds))).exists
  exact ⟨s, hs, hb.le, hm.le⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem metric_inner_sq_le_one (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) (hu : g.inner x u u = 1) (hv : g.inner x v v = 1) :
    (g.inner x u v) ^ 2 ≤ 1 := by
  have h := gInner_self_nonneg (I := I) g x (v - (g.inner x u v) • u)
  simp only [map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul] at h
  rw [hu, hv, g.symm x v u] at h
  nlinarith

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem unit_intrinsic_dist_le_abs
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (q : M) (u : TangentSpace I q) (hu : g.inner q u u = 1) (s t : ℝ) :
    (riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm q u s)
      (intrinsicGeodesic (I := I) g hEnorm q u t)).toReal ≤ |t - s| := by
  have hbound : riemannianEDist I
      (intrinsicGeodesic (I := I) g hEnorm q u s)
      (intrinsicGeodesic (I := I) g hEnorm q u t) ≤ ENNReal.ofReal |t - s| := by
    rcases le_total s t with hst | hts
    · simpa only [hu, Real.sqrt_one, one_mul, abs_of_nonneg (sub_nonneg.mpr hst)] using
        intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm q u hst
    · rw [riemannianEDist_comm]
      simpa only [hu, Real.sqrt_one, one_mul,
        abs_of_nonpos (sub_nonpos.mpr hts), neg_sub] using
        intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm q u hts
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at h


theorem cosh_distance_upper_support_of_sectional_lower_bound_on_minimizing_lens
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) (u : TangentSpace I q) (hu : g.inner q u u = 1)
    {k : ℝ} (hk : 0 < k) (x : ℝ)
    (hfin : riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm q u x) ≠ ⊤)
    (hsec : ∀ y : M,
      riemannianEDist I p y +
        riemannianEDist I y (intrinsicGeodesic (I := I) g hEnorm q u x) =
        riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm q u x) →
      SectionalBoundedBelowAt (I := I) g y (-k ^ 2))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ psi : ℝ → ℝ,
      ContDiffAt ℝ 2 psi x ∧
      psi x = Real.cosh (k * (riemannianEDist I p
        (intrinsicGeodesic (I := I) g hEnorm q u x)).toReal) ∧
      (∀ᶠ t in 𝓝 x,
        Real.cosh (k * (riemannianEDist I p
          (intrinsicGeodesic (I := I) g hEnorm q u t)).toReal) ≤ psi t) ∧
      deriv (deriv psi) x ≤ k ^ 2 * psi x + epsilon := by
  let gamma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm q u
  have hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm q u
  have hgeo : Geometry.Riemannian.Geodesic.IsGeodesic (I := I) g gamma :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm q u
  have hspeed (t : ℝ) : g.inner (gamma t)
      (curveVelocity (I := I) gamma t) (curveVelocity (I := I) gamma t) = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm q u t).trans hu
  by_cases hpx : p = gamma x
  · refine ⟨fun t => Real.cosh (k * (t - x)), by fun_prop, ?_, ?_, ?_⟩
    · change Real.cosh (k * (x - x)) = Real.cosh (k * (riemannianEDist I p (gamma x)).toReal)
      rw [hpx, riemannianEDist_self, ENNReal.toReal_zero, sub_self]
    · apply Filter.Eventually.of_forall
      intro t
      apply Real.cosh_le_cosh.mpr
      rw [abs_mul, abs_mul, abs_of_nonneg (ENNReal.toReal_nonneg)]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg k)
      rw [hpx]
      exact unit_intrinsic_dist_le_abs g hEnorm q u hu x t
    · have hd : deriv (fun t => Real.cosh (k * (t - x))) =
          fun t => Real.sinh (k * (t - x)) * k := by
        funext t
        simpa using ((((hasDerivAt_id t).sub_const x).const_mul k).cosh).deriv
      have hdd : deriv (fun t => Real.sinh (k * (t - x)) * k) x = k ^ 2 := by
        have hh := (((((hasDerivAt_id x).sub_const x).const_mul k).sinh).mul_const k).deriv
        simpa [pow_two] using hh
      simp only [hd, hdd, sub_self, mul_zero, Real.cosh_zero, mul_one]
      exact le_add_of_nonneg_right hepsilon.le
  · let r : ℝ := (riemannianEDist I p (gamma x)).toReal
    have hr : 0 < r := ENNReal.toReal_pos
      (fun hz => hpx (riemannianEDist_eq_zero_imp_eq (I := I) p (gamma x) hz)) hfin
    have hksinh : 0 < k * Real.sinh (k * r) :=
      mul_pos hk (Real.sinh_pos_iff.mpr (mul_pos hk hr))
    let delta : ℝ := epsilon / (k * Real.sinh (k * r))
    have hdelta : 0 < delta := div_pos hepsilon hksinh
    obtain ⟨s, hs, hs_half, hsmodel⟩ :=
      exists_small_fraction_modelRadialLogDeriv (neg_nonpos.mpr (sq_nonneg k)) hr hdelta
    obtain ⟨rho, U, hU, hxU, hrho, hvalue, hupper, hgrad, hhess⟩ :=
      calabiDist_sharp_hess_support_of_sectional_lower_bound_on_minimizing_lens
        (I := I) g hEnorm (neg_nonpos.mpr (sq_nonneg k)) hsec hpx hfin s hs hs_half
    let w : ℝ → ℝ := fun t => rho (gamma t)
    have hw : ContDiffAt ℝ 2 w x := by
      have h := ((hrho (gamma x) hxU).contMDiffAt (hU.mem_nhds hxU)).comp
        x hgamma.contMDiffAt
      exact (contMDiffAt_iff_contDiffAt.mp h).of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    change w x = r at hvalue
    refine ⟨fun t => Real.cosh (k * w t), (contDiffAt_const.mul hw).cosh, ?_, ?_, ?_⟩
    · change Real.cosh (k * w x) = Real.cosh (k * r)
      rw [hvalue]
    · filter_upwards [hgamma.continuous.continuousAt.eventually hupper] with t ht
      apply Real.cosh_le_cosh.mpr
      rw [abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
        abs_of_nonneg (ENNReal.toReal_nonneg.trans ht)]
      exact mul_le_mul_of_nonneg_left ht (abs_nonneg k)
    · have hfirst : deriv w x =
          g.inner (gamma x) (gradientFun (I := I) g rho (gamma x))
            (curveVelocity (I := I) gamma x) := by
        rw [inner_gradientFun]
        have hd := DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along
          I rho gamma x
          (((hrho (gamma x) hxU).contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp))
          (hgamma.contMDiffAt.mdifferentiableAt (by simp))
        with_unfolding_all exact hd.deriv
      have hsecond : deriv (deriv w) x =
          hessFun (I := I) g rho (gamma x)
            (curveVelocity (I := I) gamma x) (curveVelocity (I := I) gamma x) :=
        deriv2_comp_geo_on (I := I) g hU hrho hgamma hgeo hxU
      have hwsq : (deriv w x) ^ 2 ≤ 1 := by
        rw [hfirst]
        exact metric_inner_sq_le_one g (gamma x) _ _ hgrad (hspeed x)
      have hb := hhess (curveVelocity (I := I) gamma x)
      rw [hspeed x, ← hfirst, ← hsecond] at hb
      have hb' : deriv (deriv w) x ≤
          (modelRadialLogDeriv (-k ^ 2) r + delta) * (1 - (deriv w x) ^ 2) :=
        hb.trans (mul_le_mul_of_nonneg_right hsmodel (sub_nonneg.mpr hwsq))
      rw [modelRadialLogDeriv_neg_sq hk] at hb'
      have hmul := mul_le_mul_of_nonneg_left hb' hksinh.le
      have hcancel : k * Real.sinh (k * r) *
          (k * Real.cosh (k * r) / Real.sinh (k * r) + delta) =
          k ^ 2 * Real.cosh (k * r) + epsilon := by
        dsimp [delta]
        field_simp [(Real.sinh_pos_iff.mpr (mul_pos hk hr)).ne', hk.ne']
      rw [← mul_assoc, hcancel] at hmul
      change deriv (deriv (fun t => Real.cosh (k * w t))) x ≤
        k ^ 2 * Real.cosh (k * w x) + epsilon
      rw [second_deriv_cosh_comp hw, hvalue]
      nlinarith [mul_nonneg hepsilon.le (sq_nonneg (deriv w x))]

end DifferentialGeometry
