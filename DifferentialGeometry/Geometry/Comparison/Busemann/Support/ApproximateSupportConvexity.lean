import DifferentialGeometry.Geometry.Comparison.Toponogov.LowerSupportConvexity
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Topology

theorem convexOn_of_approximate_lower_support {D : Set ℝ} {f : ℝ → ℝ}
    (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hsupport : ∀ x ∈ interior D, ∀ ε : ℝ, 0 < ε → ∃ ψ : ℝ → ℝ,
      ContDiffAt ℝ 2 ψ x ∧ ψ x = f x ∧
        (∀ᶠ y in 𝓝 x, ψ y ≤ f y) ∧ -ε < deriv (deriv ψ) x) :
    ConvexOn ℝ D f := by
  refine LinearOrder.convexOn_of_lt hD ?_
  intro a ha b hb hab alpha beta halpha hbeta hsum
  simp only [smul_eq_mul]
  by_contra hbad
  let y : ℝ := alpha * a + beta * b
  have hgap : alpha * f a + beta * f b < f y := lt_of_not_ge hbad
  have hya : y - a = beta * (b - a) := by
    dsimp only [y]
    linear_combination a * hsum
  have hby : b - y = alpha * (b - a) := by
    dsimp only [y]
    linear_combination -b * hsum
  have hay : a < y := by nlinarith [mul_pos hbeta (sub_pos.mpr hab)]
  have hyb : y < b := by nlinarith [mul_pos halpha (sub_pos.mpr hab)]
  let c : ℝ := (f b - f a) / (b - a)
  let ell : ℝ → ℝ := fun t => f a + c * (t - a)
  have hca : c * (b - a) = f b - f a := by
    dsimp only [c]
    exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hab))
  have hell_a : ell a = f a := by simp [ell]
  have hell_b : ell b = f b := by dsimp only [ell]; linarith
  have hell_y : ell y = alpha * f a + beta * f b := by
    dsimp only [ell]
    rw [hya]
    linear_combination beta * hca - f a * hsum
  have hdelta : 0 < f y - ell y := by rw [hell_y]; linarith
  let δ : ℝ := (f y - ell y) / (2 * (y - a) * (b - y))
  have hδ : 0 < δ := div_pos hdelta (by positivity)
  have hδ_eq : δ * (y - a) * (b - y) = (f y - ell y) / 2 := by
    dsimp only [δ]
    field_simp [ne_of_gt (sub_pos.mpr hay), ne_of_gt (sub_pos.mpr hyb)]
  let P : ℝ → ℝ := fun t => δ * (t - a) * (t - b) - ell t
  let G : ℝ → ℝ := fun t => f t + P t
  have hGa : G a = 0 := by simp [G, P, hell_a]
  have hGb : G b = 0 := by simp [G, P, hell_b]
  have hGy : 0 < G y := by dsimp only [G, P]; nlinarith [hδ_eq]
  have hPcont : Continuous P := by dsimp only [P, ell]; fun_prop
  have hGD : ContinuousOn G (Icc a b) :=
    (hf.mono (hD.ordConnected.out ha hb)).add hPcont.continuousOn
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.le) hGD
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
  have hmD : m ∈ interior D := mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Ioo_mem_nhds ham hmb)
      (Ioo_subset_Icc_self.trans (hD.ordConnected.out ha hb)))
  obtain ⟨ψ, hψC, hcontact, hbelow, hsecond⟩ := hsupport m hmD δ hδ
  let φ : ℝ → ℝ := fun t => ψ t + P t
  have hmaxloc : IsLocalMax G m := hmax.isLocalMax (Icc_mem_nhds ham hmb)
  have hφmax : IsLocalMax φ m := by
    filter_upwards [hmaxloc, hbelow] with t ht hle
    dsimp only [φ, G] at *
    rw [hcontact]
    linarith
  have hell_deriv (t : ℝ) : HasDerivAt ell c t := by
    simpa only [zero_add, mul_one] using!
      (hasDerivAt_const t (f a)).add (((hasDerivAt_id t).sub_const a).const_mul c)
  have hPderiv (t : ℝ) : HasDerivAt P (δ * (2 * t - a - b) - c) t := by
    have h := ((((hasDerivAt_id t).sub_const a).const_mul δ).mul
      ((hasDerivAt_id t).sub_const b)).sub (hell_deriv t)
    convert! h using 1
    simp only [id_eq]
    ring
  have hPd : deriv P = fun t => δ * (2 * t - a - b) - c :=
    funext fun t => (hPderiv t).deriv
  have hPsecond : HasDerivAt (deriv P) (2 * δ) m := by
    rw [hPd]
    simpa only [mul_one, mul_comm δ 2] using!
      (((((hasDerivAt_id m).const_mul 2).sub_const a).sub_const b).const_mul δ).sub_const c
  have hψDiff : ∀ᶠ t in 𝓝 m, DifferentiableAt ℝ ψ t :=
    (hψC.eventually (by norm_num)).mono fun _ h => h.differentiableAt (by norm_num)
  have hφ_deriv : deriv φ =ᶠ[𝓝 m] fun t => deriv ψ t + deriv P t := by
    filter_upwards [hψDiff] with t ht
    exact deriv_add ht (hPderiv t).differentiableAt
  have hψSecond : DifferentiableAt ℝ (deriv ψ) m :=
    (hψC.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hφ_second : deriv (deriv φ) m = deriv (deriv ψ) m + 2 * δ := by
    rw [hφ_deriv.deriv_eq]
    exact (hψSecond.hasDerivAt.add hPsecond).deriv
  have hnonpos := second_deriv_nonpos_of_isLocalMax hφmax
    (hψC.continuousAt.add hPcont.continuousAt)
  rw [hφ_second] at hnonpos
  linarith

end DifferentialGeometry.Geometry.Topology

end
