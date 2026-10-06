import DifferentialGeometry.Analysis.Elliptic.Planar.GradientFactor
import DifferentialGeometry.Analysis.Elliptic.Planar.GradientFactorPolar
import DifferentialGeometry.Analysis.Elliptic.Planar.PolarRoot
import DifferentialGeometry.Analysis.Elliptic.Planar.HarmonicAngularMonomial
import DifferentialGeometry.Analysis.Elliptic.Planar.PolarZeroLocalization
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
open Filter Set Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem exists_polar_angle_in_Icc (z : ℂ) :
    ∃ θ ∈ Icc 0 (2 * Real.pi),
      (‖z‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = z := by
  by_cases harg : 0 ≤ z.arg
  · refine ⟨z.arg, ⟨harg, ?_⟩, Complex.norm_mul_exp_arg_mul_I z⟩
    linarith [Complex.arg_le_pi z, Real.pi_pos]
  · have hn : z.arg < 0 := lt_of_not_ge harg
    refine ⟨z.arg + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
    · linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
    · linarith
    · have hp : Complex.exp (((z.arg + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((z.arg : ℂ) * Complex.I) := by
        simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
          using Complex.exp_mul_I_periodic (z.arg : ℂ)
      rw [hp]
      exact Complex.norm_mul_exp_arg_mul_I z

private theorem exists_common_positive_radius
    {ι : Type*} [Finite ι] {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, ρ ≤ ε i := by
  have hevent : ∀ᶠ r : ℝ in 𝓝 0, ∀ i, r < ε i :=
    Filter.eventually_all.mpr (fun i => gt_mem_nhds (hε i))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro i
  have hmem : r / 2 ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  exact (hsub hmem i).le



private theorem exists_finite_polar_arcs
    {ε : ℝ} (hε : 0 < ε) {W A R : ℝ × ℝ → ℝ}
    (hWc : ContinuousOn W (Ico 0 ε ×ˢ (univ : Set ℝ)))
    (hAc : ContinuousOn A (Ico 0 ε ×ˢ (univ : Set ℝ)))
    (hRc : ContinuousOn R (Ico 0 ε ×ˢ (univ : Set ℝ)))
    (hWd : ContDiffOn ℝ 1 W (Ioo 0 ε ×ˢ (univ : Set ℝ)))
    (hd : ∀ r ∈ Ico 0 ε, ∀ t, HasDerivAt (fun s => W (r, s)) (A (r, t)) t)
    (hRzero : ∀ t, R (0, t) = 0)
    (hReq : ∀ r ∈ Ioo 0 ε, ∀ t, R (r, t) = r * fderiv ℝ W (r, t) (1, 0))
    {J : Set ℝ} (hJ : IsCompact J)
    (hfinite : Set.Finite {t : ℝ | t ∈ J ∧ W (0, t) = 0})
    (hsimple : ∀ t ∈ J, W (0, t) = 0 → A (0, t) ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ε ∧
      ∃ Γ : {t : ℝ // t ∈ J ∧ W (0, t) = 0} → ℝ → ℂ,
        (∀ s, Γ s 0 = 0 ∧ ContDiffOn ℝ 1 (Γ s) (Ioo (-ρ) ρ) ∧
          HasDerivAt (Γ s) (Complex.exp (((s : ℝ) : ℂ) * Complex.I)) 0 ∧
          ∀ r ∈ Ico 0 ρ, ∃ t : ℝ,
            Γ s r = (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ∧ W (r, t) = 0) ∧
        ∀ r ∈ Ico 0 ρ, ∀ t ∈ J, W (r, t) = 0 →
          ∃ s, Γ s r = (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
  classical
  let Z : Set ℝ := {t | t ∈ J ∧ W (0, t) = 0}
  let : Fintype Z := hfinite.fintype
  have hroots (s : Z) := exists_polar_root_arc_of_simple_angular_zero
    hε hWc hAc hRc hWd hd hRzero hReq s.property.2
      (hsimple s s.property.1 s.property.2)
  choose rad δ θ Γ hrad hradε hδ hθzero hθc hθd hroot huniq hweighted
    hΓzero hΓeq hΓd hΓderiv using hroots
  let O : Set ℝ := ⋃ s : Z, Metric.ball (s : ℝ) (δ s)
  have hOo : IsOpen O := isOpen_iUnion (fun _ => isOpen_ball)
  have hOzero (t : ℝ) (ht : t ∈ J) (hz : W (0, t) = 0) : t ∈ O := by
    exact mem_iUnion.mpr ⟨(⟨t, ht, hz⟩ : Z), mem_ball_self (hδ _)⟩
  obtain ⟨κ, hκ, hκε, hlocal⟩ :=
    exists_pos_radius_zero_mem_open_of_isCompact hε hWc hJ hOo hOzero
  obtain ⟨σ, hσ, hσrad⟩ := exists_common_positive_radius hrad
  let ρ := min κ σ
  have hρ : 0 < ρ := lt_min hκ hσ
  have hρrad (s : Z) : ρ ≤ rad s := (min_le_right _ _).trans (hσrad s)
  have hsub (s : Z) : Ico (0 : ℝ) ρ ⊆ Ico 0 (rad s) :=
    fun r hr => ⟨hr.1, hr.2.trans_le (hρrad s)⟩
  refine ⟨ρ, hρ, (min_le_left _ _).trans hκε, Γ, ?_, ?_⟩
  · intro s
    refine ⟨hΓzero s, (hΓd s).mono
      (Ioo_subset_Ioo (neg_le_neg (hρrad s)) (hρrad s)), hΓderiv s, ?_⟩
    intro r hr
    exact ⟨θ s r, hΓeq s r (hsub s hr), (hroot s r (hsub s hr)).2⟩
  · intro r hr t ht hz
    have htO := hlocal r ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩ t ht hz
    obtain ⟨s, hs⟩ := mem_iUnion.mp htO
    have hangle : |t - (s : ℝ)| < δ s := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hs
    have heq := (huniq s r (hsub s hr) t hangle).mp hz
    refine ⟨s, ?_⟩
    rw [hΓeq s r (hsub s hr), ← heq]

/-- The same real scalar at a nonzero-germ critical zero has a complete finite
cover of its local zero set by injective radial `C¹` arcs. The inverse gauge is
only continuous. A closed angle interval may index an endpoint ray twice; no
pairwise-distinctness or cardinality conclusion is asserted. -/
theorem exists_finite_nodal_arcs_of_analytic_inverse_gauge
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ} (ha : a ∈ Ω)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v Ω)
    {P : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)}
    (hP : ContinuousOn P Ω) (hunit : IsUnit (P a))
    (hF : AnalyticAt ℂ (fun z => Ring.inverse (P z) (planarGradientSection v z)) a)
    (hgerm : ¬ ∀ᶠ z in 𝓝 a, v z = 0)
    (hvalue : v a = 0) (hgradient : fderiv ℝ v a = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball a ρ ⊆ Ω ∧
      (∀ z ∈ Metric.ball a ρ, z ≠ a → fderiv ℝ v z ≠ 0) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∃ Γ : S → ℝ → ℂ,
        (∀ s, Γ s 0 = a ∧ ContDiffOn ℝ 1 (Γ s) (Ioo (-ρ) ρ) ∧
          HasDerivAt (Γ s) (Complex.exp (((s : ℝ) : ℂ) * Complex.I)) 0 ∧
          Set.InjOn (Γ s) (Ico 0 ρ) ∧
          ∀ r ∈ Ico 0 ρ, ‖Γ s r - a‖ = r ∧ v (Γ s r) = 0) ∧
        ∀ z ∈ Metric.ball a ρ,
          v z = 0 ↔ z = a ∨ ∃ s : S, ∃ r ∈ Ioo 0 ρ, z = Γ s r := by
  classical
  obtain ⟨U, hUo, haU, hUΩ, k, _, hk, b, hb, hbne, hgradfactor⟩ :=
    exists_planar_gradient_factor_of_analytic_inverse_gauge
      hΩ ha hP hunit hF hgerm hvalue hgradient
  have hbAt : ContinuousAt b a := (hb a haU).continuousAt (hUo.mem_nhds haU)
  have hVnhds : U ∩ {z | b z ≠ 0} ∈ 𝓝 a :=
    inter_mem (hUo.mem_nhds haU) (hbAt.eventually_ne hbne)
  obtain ⟨V, hVU, hVo, haV⟩ := _root_.mem_nhds_iff.mp hVnhds
  have hVU' : V ⊆ U := fun z hz => (hVU hz).1
  have hVΩ : V ⊆ Ω := hVU'.trans hUΩ
  obtain ⟨ε, hε, hεV, W, A, R, hWc, hWd, hpolar, hWzero, hAc, hangular,
    _, _, hRc, hRzero, hReq, _⟩ :=
    exists_polar_data_of_complex_gradient_factor hVo haV (hv.mono hVΩ)
      hvalue k (hb.mono hVU') (fun z hz => hgradfactor z (hVU' hz))
  let φ : ℝ → ℝ := fun t => (2 / ((k + 1 : ℕ) : ℝ)) *
    (b a * Complex.exp ((t : ℂ) * Complex.I) ^ (k + 1)).re
  have hφ : Set.Finite {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ φ t = 0} ∧
      ∀ t : ℝ, φ t = 0 → deriv φ t ≠ 0 := by
    let c : ℂ := ((2 / ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) * b a
    have hc : c ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (div_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)))) hbne
    have hh := finite_simple_zeros_real_monomial_on_circle hc (Nat.succ_le_succ hk)
    simpa only [c, φ, mul_assoc, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hh
  have hfinite : Set.Finite {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ W (0, t) = 0} := by
    simpa only [hWzero, φ] using hφ.1
  have hsimple (t : ℝ) (_ht : t ∈ Icc 0 (2 * Real.pi))
      (hz : W (0, t) = 0) : A (0, t) ≠ 0 := by
    have hd0 := (hangular 0 ⟨le_rfl, hε⟩ t).deriv
    have hfun : (fun s => W (0, s)) = φ := funext hWzero
    rw [hfun] at hd0
    rw [← hd0]
    exact hφ.2 t (by simpa only [hWzero, φ] using hz)
  obtain ⟨ρ, hρ, hρε, γ, hγ, hcover⟩ :=
    exists_finite_polar_arcs hε hWc hAc hRc hWd hangular hRzero hReq
      isCompact_Icc hfinite hsimple
  let S : Set ℝ := {t | t ∈ Icc 0 (2 * Real.pi) ∧ W (0, t) = 0}
  let Γ : S → ℝ → ℂ := fun s r => a + γ s r
  have hρV : Metric.ball a ρ ⊆ V :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hρε)).trans hεV
  have hrε {r : ℝ} (hr : r ∈ Ico 0 ρ) : r ∈ Ico 0 ε :=
    ⟨hr.1, hr.2.trans_le hρε⟩
  have hbranch (s : S) (r : ℝ) (hr : r ∈ Ico 0 ρ) :
      ‖Γ s r - a‖ = r ∧ v (Γ s r) = 0 := by
    obtain ⟨t, hγeq, hWt⟩ := (hγ s).2.2.2 r hr
    have hf := hpolar r (hrε hr) t
    rw [hWt, mul_zero] at hf
    constructor
    · simp only [Γ, add_sub_cancel_left, hγeq, norm_mul, Complex.norm_exp,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero,
        Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr.1]
    · simpa only [Γ, hγeq, Complex.real_smul] using hf
  refine ⟨ρ, hρ, hρV.trans hVΩ, ?_, S, hfinite, Γ, ?_, ?_⟩
  · intro z hz hza hDz
    have hbz : b z ≠ 0 := (hVU (hρV hz)).2
    have hgn : planarComplexGradient v z ≠ 0 := by
      rw [hgradfactor z (hVU' (hρV hz))]
      exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hza)) hbz
    apply hgn
    apply Complex.ext <;> simp [planarComplexGradient, hDz]
  · intro s
    refine ⟨?_, contDiffOn_const.add (hγ s).2.1, ?_, ?_, hbranch s⟩
    · simp only [Γ, (hγ s).1, add_zero]
    · convert (hasDerivAt_const (0 : ℝ) a).add (hγ s).2.2.1 using 1
      simp only [zero_add]
    · intro r hr t ht heq
      have hn := congrArg (fun z : ℂ => ‖z - a‖) heq
      simpa only [(hbranch s r hr).1, (hbranch s t ht).1] using hn
  · intro z hz
    constructor
    · intro hvz
      by_cases hza : z = a
      · exact Or.inl hza
      · have hr : ‖z - a‖ ∈ Ioo (0 : ℝ) ρ :=
          ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hza), by
            simpa only [Metric.mem_ball, dist_eq_norm] using hz⟩
        obtain ⟨t, ht, htpolar⟩ := exists_polar_angle_in_Icc (z - a)
        have hzt : a + ‖z - a‖ • Complex.exp ((t : ℂ) * Complex.I) = z := by
          rw [Complex.real_smul, htpolar, add_comm a, sub_add_cancel]
        have hf := hpolar ‖z - a‖ (hrε (Ioo_subset_Ico_self hr)) t
        rw [hzt, hvz] at hf
        have hWt : W (‖z - a‖, t) = 0 :=
          (mul_eq_zero.mp hf.symm).resolve_left (pow_ne_zero _ (ne_of_gt hr.1))
        obtain ⟨s, hs⟩ := hcover ‖z - a‖ (Ioo_subset_Ico_self hr) t ht hWt
        refine Or.inr ⟨s, ‖z - a‖, hr, ?_⟩
        change z = a + γ s ‖z - a‖
        rw [hs]
        simpa only [Complex.real_smul] using hzt.symm
    · rintro (rfl | ⟨s, r, hr, rfl⟩)
      · exact hvalue
      · exact (hbranch s r (Ioo_subset_Ico_self hr)).2

/-- The same C¹ real scalar with a continuous nonvanishing complex-gradient
factor has full finite positive-arc zero coverage near its critical center.
The signed extension is C¹; nodality is asserted only for nonnegative radius. -/
theorem exists_finite_nodal_arcs_of_complex_gradient_factor
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ} (ha : a ∈ Ω)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v Ω) (hvalue : v a = 0)
    (k : ℕ) (hk : 1 ≤ k) {b : ℂ → ℂ} (hb : ContinuousOn b Ω)
    (hbne : b a ≠ 0)
    (hgradfactor : ∀ z ∈ Ω, planarComplexGradient v z = (z - a) ^ k * b z) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball a ρ ⊆ Ω ∧
      (∀ z ∈ Metric.ball a ρ, z ≠ a → fderiv ℝ v z ≠ 0) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∃ Γ : S → ℝ → ℂ,
        (∀ s, Γ s 0 = a ∧ ContDiffOn ℝ 1 (Γ s) (Ioo (-ρ) ρ) ∧
          HasDerivAt (Γ s) (Complex.exp (((s : ℝ) : ℂ) * Complex.I)) 0 ∧
          Set.InjOn (Γ s) (Ico 0 ρ) ∧
          ∀ r ∈ Ico 0 ρ, ‖Γ s r - a‖ = r ∧ v (Γ s r) = 0) ∧
        ∀ z ∈ Metric.ball a ρ,
          v z = 0 ↔ z = a ∨ ∃ s : S, ∃ r ∈ Ioo 0 ρ, z = Γ s r := by
  classical
  have hbAt : ContinuousAt b a := (hb a ha).continuousAt (hΩ.mem_nhds ha)
  have hVnhds : Ω ∩ {z | b z ≠ 0} ∈ 𝓝 a :=
    inter_mem (hΩ.mem_nhds ha) (hbAt.eventually_ne hbne)
  obtain ⟨V, hVU, hVo, haV⟩ := _root_.mem_nhds_iff.mp hVnhds
  have hVU' : V ⊆ Ω := fun z hz => (hVU hz).1
  have hVΩ : V ⊆ Ω := hVU'
  obtain ⟨ε, hε, hεV, W, A, R, hWc, hWd, hpolar, hWzero, hAc, hangular,
    _, _, hRc, hRzero, hReq, _⟩ :=
    exists_polar_data_of_complex_gradient_factor hVo haV (hv.mono hVΩ)
      hvalue k (hb.mono hVU') (fun z hz => hgradfactor z (hVU' hz))
  let φ : ℝ → ℝ := fun t => (2 / ((k + 1 : ℕ) : ℝ)) *
    (b a * Complex.exp ((t : ℂ) * Complex.I) ^ (k + 1)).re
  have hφ : Set.Finite {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ φ t = 0} ∧
      ∀ t : ℝ, φ t = 0 → deriv φ t ≠ 0 := by
    let c : ℂ := ((2 / ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) * b a
    have hc : c ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (div_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)))) hbne
    have hh := finite_simple_zeros_real_monomial_on_circle hc (Nat.succ_le_succ hk)
    simpa only [c, φ, mul_assoc, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hh
  have hfinite : Set.Finite {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ W (0, t) = 0} := by
    simpa only [hWzero, φ] using hφ.1
  have hsimple (t : ℝ) (_ht : t ∈ Icc 0 (2 * Real.pi))
      (hz : W (0, t) = 0) : A (0, t) ≠ 0 := by
    have hd0 := (hangular 0 ⟨le_rfl, hε⟩ t).deriv
    have hfun : (fun s => W (0, s)) = φ := funext hWzero
    rw [hfun] at hd0
    rw [← hd0]
    exact hφ.2 t (by simpa only [hWzero, φ] using hz)
  obtain ⟨ρ, hρ, hρε, γ, hγ, hcover⟩ :=
    exists_finite_polar_arcs hε hWc hAc hRc hWd hangular hRzero hReq
      isCompact_Icc hfinite hsimple
  let S : Set ℝ := {t | t ∈ Icc 0 (2 * Real.pi) ∧ W (0, t) = 0}
  let Γ : S → ℝ → ℂ := fun s r => a + γ s r
  have hρV : Metric.ball a ρ ⊆ V :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hρε)).trans hεV
  have hrε {r : ℝ} (hr : r ∈ Ico 0 ρ) : r ∈ Ico 0 ε :=
    ⟨hr.1, hr.2.trans_le hρε⟩
  have hbranch (s : S) (r : ℝ) (hr : r ∈ Ico 0 ρ) :
      ‖Γ s r - a‖ = r ∧ v (Γ s r) = 0 := by
    obtain ⟨t, hγeq, hWt⟩ := (hγ s).2.2.2 r hr
    have hf := hpolar r (hrε hr) t
    rw [hWt, mul_zero] at hf
    constructor
    · simp only [Γ, add_sub_cancel_left, hγeq, norm_mul, Complex.norm_exp,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero,
        Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr.1]
    · simpa only [Γ, hγeq, Complex.real_smul] using hf
  refine ⟨ρ, hρ, hρV.trans hVΩ, ?_, S, hfinite, Γ, ?_, ?_⟩
  · intro z hz hza hDz
    have hbz : b z ≠ 0 := (hVU (hρV hz)).2
    have hgn : planarComplexGradient v z ≠ 0 := by
      rw [hgradfactor z (hVU' (hρV hz))]
      exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hza)) hbz
    apply hgn
    apply Complex.ext <;> simp [planarComplexGradient, hDz]
  · intro s
    refine ⟨?_, contDiffOn_const.add (hγ s).2.1, ?_, ?_, hbranch s⟩
    · simp only [Γ, (hγ s).1, add_zero]
    · convert (hasDerivAt_const (0 : ℝ) a).add (hγ s).2.2.1 using 1
      simp only [zero_add]
    · intro r hr t ht heq
      have hn := congrArg (fun z : ℂ => ‖z - a‖) heq
      simpa only [(hbranch s r hr).1, (hbranch s t ht).1] using hn
  · intro z hz
    constructor
    · intro hvz
      by_cases hza : z = a
      · exact Or.inl hza
      · have hr : ‖z - a‖ ∈ Ioo (0 : ℝ) ρ :=
          ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hza), by
            simpa only [Metric.mem_ball, dist_eq_norm] using hz⟩
        obtain ⟨t, ht, htpolar⟩ := exists_polar_angle_in_Icc (z - a)
        have hzt : a + ‖z - a‖ • Complex.exp ((t : ℂ) * Complex.I) = z := by
          rw [Complex.real_smul, htpolar, add_comm a, sub_add_cancel]
        have hf := hpolar ‖z - a‖ (hrε (Ioo_subset_Ico_self hr)) t
        rw [hzt, hvz] at hf
        have hWt : W (‖z - a‖, t) = 0 :=
          (mul_eq_zero.mp hf.symm).resolve_left (pow_ne_zero _ (ne_of_gt hr.1))
        obtain ⟨s, hs⟩ := hcover ‖z - a‖ (Ioo_subset_Ico_self hr) t ht hWt
        refine Or.inr ⟨s, ‖z - a‖, hr, ?_⟩
        change z = a + γ s ‖z - a‖
        rw [hs]
        simpa only [Complex.real_smul] using hzt.symm
    · rintro (rfl | ⟨s, r, hr, rfl⟩)
      · exact hvalue
      · exact (hbranch s r (Ioo_subset_Ico_self hr)).2


end DifferentialGeometry.Analysis
