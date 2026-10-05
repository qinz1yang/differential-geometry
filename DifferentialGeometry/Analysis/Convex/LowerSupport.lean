import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Set Filter
open scoped Topology

theorem second_deriv_nonpos_of_isLocalMax {f : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hpos : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hmin : IsLocalMin f x := isLocalMin_of_deriv_deriv_pos hpos hmax.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hmax, hmin] with y h1 h2
    exact le_antisymm h1 h2
  have hzero : deriv (deriv f) x = 0 := by
    simpa only [deriv_const', deriv_const] using heq.deriv.deriv_eq
  exact (ne_of_gt hpos) hzero

theorem convexOn_of_lower_support {D : Set ℝ} {f : ℝ → ℝ}
    (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hsupport : ∀ x ∈ interior D, ∃ psi : ℝ → ℝ,
      ContDiffAt ℝ 2 psi x ∧ psi x = f x ∧
        (∀ᶠ y in 𝓝 x, psi y ≤ f y) ∧ 0 ≤ deriv (deriv psi) x) :
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
  obtain ⟨psi, hpsiC, hcontact, hbelow, hsecond⟩ := hsupport m hmD
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

theorem convex_quotient_mono {f : ℝ → ℝ} {T s1 s2 : ℝ}
    (hf : ConvexOn ℝ (Icc 0 T) f) (hzero : f 0 = 0)
    (hs1 : 0 < s1) (hs12 : s1 ≤ s2) (hs2T : s2 ≤ T) :
    f s1 / s1 ≤ f s2 / s2 := by
  have hs2 : 0 < s2 := lt_of_lt_of_le hs1 hs12
  simpa only [hzero, sub_zero] using
    hf.secant_mono ⟨le_rfl, hs2.le.trans hs2T⟩ ⟨hs1.le, hs12.trans hs2T⟩
      ⟨hs2.le, hs2T⟩ hs1.ne' hs2.ne' hs12

theorem convex_endpoint_lower_support {f psi : ℝ → ℝ} {T d : ℝ}
    (hT : 0 < T) (hf : ConvexOn ℝ (Icc 0 T) f)
    (hpsi : HasDerivWithinAt psi d (Ioi 0) 0) (hcontact : psi 0 = f 0)
    (hbelow : ∀ᶠ t in 𝓝[>] (0 : ℝ), psi t ≤ f t) :
    f 0 + T * d ≤ f T := by
  have hlim : Tendsto (slope psi 0) (𝓝[>] (0 : ℝ)) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).1 hpsi
  have hbound : d ≤ (f T - f 0) / T := by
    apply le_of_tendsto hlim
    filter_upwards [hbelow, nhdsWithin_le_nhds (eventually_lt_nhds hT),
      self_mem_nhdsWithin] with t hle htT ht0
    have ht : 0 < t := ht0
    have h1 : (psi t - psi 0) / t ≤ (f t - f 0) / t := by
      apply div_le_div_of_nonneg_right _ ht.le
      rw [hcontact]
      linarith
    have h2 : (f t - f 0) / t ≤ (f T - f 0) / T := by
      simpa only [sub_zero] using
        hf.secant_mono ⟨le_rfl, hT.le⟩ ⟨ht.le, htT.le⟩ ⟨hT.le, le_rfl⟩ ht.ne' hT.ne' htT.le
    simpa only [slope_def_field, sub_zero] using h1.trans h2
  rw [le_div_iff₀ hT] at hbound
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
