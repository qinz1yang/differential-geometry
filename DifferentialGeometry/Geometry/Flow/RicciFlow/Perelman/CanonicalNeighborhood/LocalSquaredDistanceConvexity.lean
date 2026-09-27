import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalSharpDistanceSupport
import DifferentialGeometry.Geometry.Comparison.Toponogov.LowerSupportConvexity
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness

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

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

private theorem convexOn_of_approx_lower_support {D : Set ℝ} {f : ℝ → ℝ}
    (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hsupport : ∀ x ∈ interior D, ∀ epsilon : ℝ, 0 < epsilon → ∃ psi : ℝ → ℝ,
      ContDiffAt ℝ 2 psi x ∧ psi x = f x ∧
        (∀ᶠ y in 𝓝 x, psi y ≤ f y) ∧ -epsilon ≤ deriv (deriv psi) x) :
    ConvexOn ℝ D f := by
  refine LinearOrder.convexOn_of_lt hD ?_
  intro a ha b hb hab alpha beta halpha hbeta hsum
  simp only [smul_eq_mul]
  by_contra hbad
  let y : ℝ := alpha * a + beta * b
  have hgap : alpha * f a + beta * f b < f y := lt_of_not_ge hbad
  have hya : y - a = beta * (b - a) := by dsimp [y]; linear_combination a * hsum
  have hby : b - y = alpha * (b - a) := by dsimp [y]; linear_combination -b * hsum
  have hay : a < y := by nlinarith [mul_pos hbeta (sub_pos.2 hab)]
  have hyb : y < b := by nlinarith [mul_pos halpha (sub_pos.2 hab)]
  let c : ℝ := (f b - f a) / (b - a)
  let ell : ℝ → ℝ := fun t => f a + c * (t - a)
  have hca : c * (b - a) = f b - f a := by
    dsimp [c]
    exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.2 hab))
  have hell_a : ell a = f a := by simp [ell]
  have hell_b : ell b = f b := by dsimp [ell]; linarith
  have hell_y : ell y = alpha * f a + beta * f b := by
    dsimp [ell]
    rw [hya]
    linear_combination beta * hca - f a * hsum
  have hdelta : 0 < f y - ell y := by rw [hell_y]; linarith
  let eta : ℝ := (f y - ell y) / (2 * (y - a) * (b - y))
  have heta : 0 < eta := div_pos hdelta (by positivity)
  have heta_eq : eta * (y - a) * (b - y) = (f y - ell y) / 2 := by
    dsimp [eta]
    field_simp [ne_of_gt (sub_pos.2 hay), ne_of_gt (sub_pos.2 hyb)]
  let P : ℝ → ℝ := fun t => eta * (t - a) * (t - b) - ell t
  let G : ℝ → ℝ := fun t => f t + P t
  have hGa : G a = 0 := by simp [G, P, hell_a]
  have hGb : G b = 0 := by simp [G, P, hell_b]
  have hGy : 0 < G y := by dsimp [G, P]; nlinarith [heta_eq]
  have hPcont : Continuous P := by dsimp [P, ell]; fun_prop
  have hGD : ContinuousOn G (Icc a b) :=
    (hf.mono (hD.ordConnected.out ha hb)).add hPcont.continuousOn
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab.le) hGD
  have hGm : 0 < G m := lt_of_lt_of_le hGy (hmax ⟨hay.le, hyb.le⟩)
  have ham : a < m := by
    refine lt_of_le_of_ne hm.1 ?_
    intro h
    rw [← h, hGa] at hGm
    exact lt_irrefl _ hGm
  have hmb : m < b := by
    refine lt_of_le_of_ne hm.2 ?_
    intro h
    rw [h, hGb] at hGm
    exact lt_irrefl _ hGm
  have hmD : m ∈ interior D := mem_interior_iff_mem_nhds.2
    (Filter.mem_of_superset (Ioo_mem_nhds ham hmb)
      (Ioo_subset_Icc_self.trans (hD.ordConnected.out ha hb)))
  obtain ⟨psi, hpsiC, hcontact, hbelow, hsecond⟩ := hsupport m hmD eta heta
  let phi : ℝ → ℝ := fun t => psi t + P t
  have hmaxloc : IsLocalMax G m := hmax.isLocalMax (Icc_mem_nhds ham hmb)
  have hphimax : IsLocalMax phi m := by
    filter_upwards [hmaxloc, hbelow] with t ht hle
    dsimp [phi, G] at *
    rw [hcontact]
    linarith
  have hell_deriv (t : ℝ) : HasDerivAt ell c t := by
    simpa only [zero_add, mul_one] using!
      (hasDerivAt_const t (f a)).add (((hasDerivAt_id t).sub_const a).const_mul c)
  have hPderiv (t : ℝ) : HasDerivAt P (eta * (2 * t - a - b) - c) t := by
    have h := ((((hasDerivAt_id t).sub_const a).const_mul eta).mul
      ((hasDerivAt_id t).sub_const b)).sub (hell_deriv t)
    convert! h using 1
    simp only [id_eq]
    ring
  have hPd : deriv P = fun t => eta * (2 * t - a - b) - c :=
    funext fun t => (hPderiv t).deriv
  have hPsecond : HasDerivAt (deriv P) (2 * eta) m := by
    rw [hPd]
    simpa only [mul_one, mul_comm eta 2] using!
      (((((hasDerivAt_id m).const_mul 2).sub_const a).sub_const b).const_mul eta).sub_const c
  have hpsiDiff : ∀ᶠ t in 𝓝 m, DifferentiableAt ℝ psi t :=
    (hpsiC.eventually (by norm_num)).mono fun _ h => h.differentiableAt (by norm_num)
  have hphi_deriv : deriv phi =ᶠ[𝓝 m] fun t => deriv psi t + deriv P t := by
    filter_upwards [hpsiDiff] with t ht
    exact deriv_add ht (hPderiv t).differentiableAt
  have hpsiSecond : DifferentiableAt ℝ (deriv psi) m :=
    (hpsiC.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hphi_second : deriv (deriv phi) m = deriv (deriv psi) m + 2 * eta := by
    rw [hphi_deriv.deriv_eq]
    exact (hpsiSecond.hasDerivAt.add hPsecond).deriv
  have hnonpos := second_deriv_nonpos_of_isLocalMax hphimax
    (hpsiC.continuousAt.add hPcont.continuousAt)
  rw [hphi_second] at hnonpos
  linarith

private theorem second_deriv_sq_sub_sq {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) :
    deriv (deriv (fun t => t ^ 2 - f t ^ 2)) x =
      2 - 2 * (deriv f x) ^ 2 - 2 * f x * deriv (deriv f) x := by
  have hfDiff : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ f t :=
    (hf.eventually (by norm_num)).mono fun _ h => h.differentiableAt (by norm_num)
  have hfirst : deriv (fun t => t ^ 2 - f t ^ 2) =ᶠ[𝓝 x]
      fun t => 2 * t - 2 * f t * deriv f t := by
    filter_upwards [hfDiff] with t ht
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq,
      Pi.sub_apply, Pi.pow_apply] using!
      (((hasDerivAt_id t).pow 2).sub (ht.hasDerivAt.pow 2)).deriv
  have hsecond : DifferentiableAt ℝ (deriv f) x :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd := ((hasDerivAt_id x).const_mul 2).sub
    (((hf.differentiableAt (by norm_num)).hasDerivAt.const_mul 2).mul hsecond.hasDerivAt)
  rw [hfirst.deriv_eq]
  convert! hd.deriv using 1
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

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

theorem convexOn_sq_sub_sq_of_sectional_nonnegative_on_minimizing_lenses
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) (u : TangentSpace I q) (hu : g.inner q u u = 1)
    {D : Set ℝ} (hD : Convex ℝ D)
    (hsec : ∀ t ∈ interior D, ∀ y : M,
      riemannianEDist I p y +
        riemannianEDist I y (intrinsicGeodesic (I := I) g hEnorm q u t) =
        riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm q u t) →
      metricRm04At (I := I) g y ∈ tensor04SectionalNonnegativeCone (I := I) (M := M)) :
    ConvexOn ℝ D (fun t => t ^ 2 -
      (riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm q u t)).toReal ^ 2) := by
  let gamma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm q u
  have hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma :=
    intrinsicGeodesic_contMDiff (I := I) g hEnorm q u
  have hgeo : Geometry.Riemannian.Geodesic.IsGeodesic (I := I) g gamma :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm q u
  have hspeed (t : ℝ) : g.inner (gamma t)
      (curveVelocity (I := I) gamma t) (curveVelocity (I := I) gamma t) = 1 := by
    exact (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm q u t).trans hu
  have hdistCont : Continuous (fun t => (riemannianEDist I p (gamma t)).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (ENNReal.continuousAt_toReal (riemannianEDist_ne_top (I := I) p (gamma t))).comp
      (f := fun z : ℝ => riemannianEDist I p (gamma z))
    simpa only [Function.comp_def, riemannianEDist_comm] using
      ((continuous_riemannianEDist_to (I := I) p).comp hgamma.continuous).continuousAt
  apply convexOn_of_approx_lower_support
    (f := fun t => t ^ 2 - (riemannianEDist I p (gamma t)).toReal ^ 2) hD
    ((continuous_id.pow 2).sub (hdistCont.pow 2)).continuousOn
  intro x hxD epsilon hepsilon
  by_cases hpx : p = gamma x
  · refine ⟨fun t => 2 * x * t - x ^ 2, by fun_prop, ?_, ?_, ?_⟩
    · change 2 * x * x - x ^ 2 = x ^ 2 - (riemannianEDist I p (gamma x)).toReal ^ 2
      rw [hpx, riemannianEDist_self, ENNReal.toReal_zero]
      ring
    · apply Filter.Eventually.of_forall
      intro t
      have hle := unit_intrinsic_dist_le_abs (I := I) g hEnorm q u hu x t
      change (riemannianEDist I (gamma x) (gamma t)).toReal ≤ |t - x| at hle
      change 2 * x * t - x ^ 2 ≤ t ^ 2 - (riemannianEDist I p (gamma t)).toReal ^ 2
      rw [hpx]
      have hsq := mul_self_le_mul_self ENNReal.toReal_nonneg hle
      nlinarith [sq_abs (t - x)]
    · have hd : deriv (fun t : ℝ => 2 * x * t - x ^ 2) = fun _ => 2 * x := by
        funext t
        simpa only [mul_one] using!
          (((hasDerivAt_id t).const_mul (2 * x)).sub_const (x ^ 2)).deriv
      rw [hd, deriv_const]
      linarith
  · let delta : ℝ := min epsilon 1
    have hdelta : 0 < delta := lt_min hepsilon zero_lt_one
    have hdelta_one : delta ≤ 1 := min_le_right _ _
    have hdelta_epsilon : delta ≤ epsilon := min_le_left _ _
    have hdelta_two : 0 < 2 + delta := by linarith
    let s : ℝ := delta / (2 + delta)
    have hs : 0 < s := div_pos hdelta hdelta_two
    have hs_half : s ≤ 1 / 2 := by
      apply (div_le_iff₀ hdelta_two).2
      linarith
    have hs_one : s < 1 := lt_of_le_of_lt hs_half (by norm_num)
    let r : ℝ := (riemannianEDist I p (gamma x)).toReal
    have hfin := riemannianEDist_ne_top (I := I) p (gamma x)
    have hdist_ne : riemannianEDist I p (gamma x) ≠ 0 := by
      intro hzero
      exact hpx (riemannianEDist_eq_zero_imp_eq (I := I) p (gamma x) hzero)
    have hr : 0 < r := ENNReal.toReal_pos hdist_ne hfin
    obtain ⟨rho, U, hU, hxU, hrho, hvalue, hupper, hhess⟩ :=
      calabiDist_sharp_hess_support_on_minimizing_lens (I := I) g hEnorm (hsec x hxD) hpx hfin s hs hs_half
    let w : ℝ → ℝ := fun t => rho (gamma t)
    have hw : ContDiffAt ℝ 2 w x := by
      have h := ((hrho (gamma x) hxU).contMDiffAt (hU.mem_nhds hxU)).comp
        x hgamma.contMDiffAt
      exact (contMDiffAt_iff_contDiffAt.mp h).of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    change w x = r at hvalue
    refine ⟨fun t => t ^ 2 - w t ^ 2, contDiffAt_id.pow 2 |>.sub (hw.pow 2), ?_, ?_, ?_⟩
    · change x ^ 2 - w x ^ 2 = x ^ 2 - r ^ 2
      rw [hvalue]
    · filter_upwards [hgamma.continuous.continuousAt.eventually hupper] with t ht
      have hsq := mul_self_le_mul_self ENNReal.toReal_nonneg ht
      change t ^ 2 - w t ^ 2 ≤ t ^ 2 - (riemannianEDist I p (gamma t)).toReal ^ 2
      dsimp only [w]
      nlinarith
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
            (curveVelocity (I := I) gamma x) (curveVelocity (I := I) gamma x) := by
        exact deriv2_comp_geo_on (I := I) g hU hrho hgamma hgeo hxU
      have hbound := hhess (curveVelocity (I := I) gamma x)
      rw [hspeed x, ← hfirst, ← hsecond] at hbound
      change deriv (deriv w) x ≤ (1 - (deriv w x) ^ 2) / ((1 - s) * r) at hbound
      have hden_pos : 0 < (1 - s) * r := mul_pos (sub_pos.mpr hs_one) hr
      have hden : ((1 - s) * r) * (2 + delta) = 2 * r := by
        dsimp only [s]
        field_simp
        ring
      have hscaled : 2 * r * deriv (deriv w) x ≤
          (1 - (deriv w x) ^ 2) * (2 + delta) := by
        calc
          _ = (deriv (deriv w) x * ((1 - s) * r)) * (2 + delta) := by
            linear_combination -(deriv (deriv w) x) * hden
          _ ≤ _ := mul_le_mul_of_nonneg_right
            ((le_div_iff₀ hden_pos).1 hbound) hdelta_two.le
      rw [second_deriv_sq_sub_sq hw, hvalue]
      nlinarith [mul_nonneg hdelta.le (sq_nonneg (deriv w x))]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

end
