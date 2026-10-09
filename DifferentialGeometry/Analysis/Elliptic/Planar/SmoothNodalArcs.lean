import DifferentialGeometry.Analysis.Elliptic.Planar.GradientFactor
import DifferentialGeometry.Analysis.Elliptic.Planar.GradientFactorJets
import DifferentialGeometry.Analysis.Elliptic.Planar.PolarBlowup
import DifferentialGeometry.Analysis.Elliptic.Planar.HarmonicAngularMonomial
import DifferentialGeometry.Analysis.Elliptic.Planar.PolarZeroLocalization
import DifferentialGeometry.Analysis.Calculus.Inverse.MonotoneGraph
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
open Set Filter Metric
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


private theorem exists_open_simple_zero_graph_neighborhood
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {t₀ : ℝ} (hp : (0, t₀) ∈ Ω)
    {W : ℝ × ℝ → ℝ} (hW : ContDiffOn ℝ ∞ W Ω)
    (hz : W (0, t₀) = 0)
    (hderiv : deriv (fun t => W (0, t)) t₀ ≠ 0) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0, t₀) ∈ U ∧ U ⊆ Ω ∧
      (∀ p ∈ U, fderiv ℝ W p (0, 1) ≠ 0) ∧
      Set.InjOn (Prod.fst : ℝ × ℝ → ℝ) (U ∩ {p | W p = 0}) := by
  have hWa := hW.contDiffAt (hΩ.mem_nhds hp)
  have hd : HasFDerivAt (fun t => W (0, t))
      ((fderiv ℝ W (0, t₀)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) t₀ :=
    (hWa.differentiableAt (by simp)).hasFDerivAt.comp t₀
      ((hasFDerivAt_const (0 : ℝ) t₀).prodMk (hasFDerivAt_id t₀))
  have hne : ((fderiv ℝ W (0, t₀)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) 1 ≠ 0 := by
    rwa [← hd.hasDerivAt.deriv]
  have hinv : ((fderiv ℝ W (0, t₀)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible :=
    ⟨_, (hd.hasDerivAt.hasFDerivAt_equiv hne).unique hd⟩
  let ψ := hWa.implicitFunction (by simp : (∞ : ℕ∞ω) ≠ 0) hinv
  have huniq : ∀ᶠ p in 𝓝 (0, t₀), W p = 0 ↔ ψ p.1 = p.2 := by
    simpa only [hz] using
      hWa.eventually_apply_eq_iff_implicitFunction (by simp : (∞ : ℕ∞ω) ≠ 0) hinv
  have hDc : ContinuousAt (fun p => fderiv ℝ W p (0, 1)) (0, t₀) :=
    (hWa.fderiv_right (m := 0) (by simp)).continuousAt.clm_apply continuousAt_const
  have hDne : fderiv ℝ W (0, t₀) (0, 1) ≠ 0 := hne
  have hN : Ω ∩ {p | fderiv ℝ W p (0, 1) ≠ 0} ∩
      {p | W p = 0 ↔ ψ p.1 = p.2} ∈ 𝓝 (0, t₀) :=
    inter_mem (inter_mem (hΩ.mem_nhds hp) (hDc.eventually_ne hDne)) huniq
  obtain ⟨U, hUs, hUo, hpU⟩ := _root_.mem_nhds_iff.mp hN
  refine ⟨U, hUo, hpU, fun p hp' => (hUs hp').1.1,
    fun p hp' => (hUs hp').1.2, ?_⟩
  intro p hp' q hq' heq
  apply Prod.ext heq
  calc
    p.2 = ψ p.1 := (((hUs hp'.1).2).mp hp'.2).symm
    _ = ψ q.1 := congrArg ψ heq
    _ = q.2 := ((hUs hq'.1).2).mp hq'.2



private theorem exists_smooth_local_polar_root
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {t₀ : ℝ} (hp : (0, t₀) ∈ Ω)
    {W : ℝ × ℝ → ℝ} (hW : ContDiffOn ℝ ∞ W Ω)
    (hz : W (0, t₀) = 0)
    (hderiv : deriv (fun t => W (0, t)) t₀ ≠ 0) :
    ∃ ρ δ : ℝ, ∃ θ : ℝ → ℝ, ∃ Γ : ℝ → ℂ,
      0 < ρ ∧ 0 < δ ∧ θ 0 = t₀ ∧
      ContDiffOn ℝ ∞ θ (Ioo (-ρ) ρ) ∧
      (∀ r ∈ Ioo (-ρ) ρ, W (r, θ r) = 0) ∧
      (∀ r ∈ Ioo (-ρ) ρ, ∀ t, |t - t₀| < δ → (W (r, t) = 0 ↔ t = θ r)) ∧
      Γ 0 = 0 ∧
      (∀ r, Γ r = (r : ℂ) * Complex.exp ((θ r : ℂ) * Complex.I)) ∧
      ContDiffOn ℝ ∞ Γ (Ioo (-ρ) ρ) ∧
      HasDerivAt Γ (Complex.exp ((t₀ : ℂ) * Complex.I)) 0 := by
  obtain ⟨U, hUo, hpU, hUΩ, hUne, hUinj⟩ :=
    exists_open_simple_zero_graph_neighborhood hΩ hp hW hz hderiv
  obtain ⟨O, hOo, θ, hθ, hgraph⟩ :=
    exists_isOpen_contDiffOn_implicit_graph_of_injOn (by simp : (∞ : ℕ∞ω) ≠ 0)
      hUo (hW.mono hUΩ) (fun p hp' _ => hUne p hp') hUinj
  have hbase : (0 : ℝ) ∈ O ∧ t₀ = θ 0 := by
    have hh : (0, t₀) ∈ U ∩ {p | W p = 0} := ⟨hpU, hz⟩
    rwa [hgraph] at hh
  obtain ⟨η, hη, hηU⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hpU)
  obtain ⟨κ, hκ, hκO⟩ := Metric.mem_nhds_iff.mp (hOo.mem_nhds hbase.1)
  let ρ := min (η / 2) (κ / 2)
  let δ := η / 2
  have hρ : 0 < ρ := lt_min (half_pos hη) (half_pos hκ)
  have hsub : Ioo (-ρ) ρ ⊆ O := by
    intro r hr
    apply hκO
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact (abs_lt.mpr hr).trans ((min_le_right _ _).trans_lt (half_lt_self hκ))
  have hroot (r : ℝ) (hr : r ∈ Ioo (-ρ) ρ) : W (r, θ r) = 0 := by
    have hh : (r, θ r) ∈ {p : ℝ × ℝ | p.1 ∈ O ∧ p.2 = θ p.1} :=
      ⟨hsub hr, rfl⟩
    rw [← hgraph] at hh
    exact hh.2
  have hθd : ContDiffOn ℝ ∞ θ (Ioo (-ρ) ρ) := hθ.mono hsub
  let E : ℝ → ℂ := fun r => Complex.exp ((θ r : ℂ) * Complex.I)
  let Γ : ℝ → ℂ := fun r => (r : ℂ) * E r
  have hEd : ContDiffOn ℝ ∞ E (Ioo (-ρ) ρ) :=
    Complex.contDiff_exp.comp_contDiffOn
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hθd).mul contDiffOn_const)
  have hΓd : ContDiffOn ℝ ∞ Γ (Ioo (-ρ) ρ) :=
    Complex.ofRealCLM.contDiff.contDiffOn.mul hEd
  have hzeroI : (0 : ℝ) ∈ Ioo (-ρ) ρ := ⟨neg_lt_zero.mpr hρ, hρ⟩
  have hEat : DifferentiableAt ℝ E 0 :=
    (hEd.contDiffAt (isOpen_Ioo.mem_nhds hzeroI)).differentiableAt (by simp)
  refine ⟨ρ, δ, θ, Γ, hρ, half_pos hη, hbase.2.symm,
    hθd, hroot, ?_, ?_, fun _ => rfl, hΓd, ?_⟩
  · intro r hr t ht
    have hpU' : (r, t) ∈ U := by
      apply hηU
      rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
      exact max_lt ((abs_lt.mpr hr).trans
        ((min_le_left _ _).trans_lt (half_lt_self hη)))
        (ht.trans (half_lt_self hη))
    constructor
    · intro hwt
      have hh : (r, t) ∈ U ∩ {p | W p = 0} := ⟨hpU', hwt⟩
      rw [hgraph] at hh
      exact hh.2
    · rintro rfl
      exact hroot r hr
  · simp only [Γ, Complex.ofReal_zero, zero_mul]
  · have hh := (Complex.ofRealCLM.hasFDerivAt (x := (0 : ℝ))).hasDerivAt.mul hEat.hasDerivAt
    convert hh using 1
    · rfl
    · simp only [E, Complex.ofRealCLM_apply, Complex.ofReal_zero,
        Complex.ofReal_one, one_mul, zero_mul, add_zero, hbase.2.symm]


private theorem exists_finite_smooth_polar_arcs
    {ε : ℝ} (hε : 0 < ε) {W : ℝ × ℝ → ℝ}
    (hWd : ContDiffOn ℝ ∞ W {p : ℝ × ℝ | |p.1| < ε})
    {J : Set ℝ} (hJ : IsCompact J)
    (hfinite : Set.Finite {t : ℝ | t ∈ J ∧ W (0, t) = 0})
    (hsimple : ∀ t ∈ J, W (0, t) = 0 → deriv (fun s => W (0, s)) t ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ε ∧
      ∃ Γ : {t : ℝ // t ∈ J ∧ W (0, t) = 0} → ℝ → ℂ,
        (∀ s, Γ s 0 = 0 ∧ ContDiffOn ℝ ∞ (Γ s) (Ioo (-ρ) ρ) ∧
          HasDerivAt (Γ s) (Complex.exp (((s : ℝ) : ℂ) * Complex.I)) 0 ∧
          ∀ r ∈ Ioo (-ρ) ρ, ∃ t : ℝ,
            Γ s r = (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ∧ W (r, t) = 0) ∧
        ∀ r ∈ Ico 0 ρ, ∀ t ∈ J, W (r, t) = 0 →
          ∃ s, Γ s r = (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
  classical
  let Z : Set ℝ := {t | t ∈ J ∧ W (0, t) = 0}
  let : Fintype Z := hfinite.fintype
  have hstrip : IsOpen {p : ℝ × ℝ | |p.1| < ε} :=
    isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  have hroots (s : Z) := exists_smooth_local_polar_root hstrip
    (by simpa only [mem_ofPred_eq, abs_zero] using hε) hWd s.property.2
      (hsimple s s.property.1 s.property.2)
  choose rad δ θ Γ hrad hδ hθzero hθd hroot huniq hΓzero hΓeq hΓd hΓderiv using hroots
  let O : Set ℝ := ⋃ s : Z, Metric.ball (s : ℝ) (δ s)
  have hOo : IsOpen O := isOpen_iUnion (fun _ => isOpen_ball)
  have hOzero (t : ℝ) (ht : t ∈ J) (hz : W (0, t) = 0) : t ∈ O :=
    mem_iUnion.mpr ⟨(⟨t, ht, hz⟩ : Z), mem_ball_self (hδ _)⟩
  have hWc : ContinuousOn W (Ico 0 ε ×ˢ (univ : Set ℝ)) :=
    hWd.continuousOn.mono (fun p hp => by
      simpa only [mem_ofPred_eq, abs_of_nonneg hp.1.1] using hp.1.2)
  obtain ⟨κ, hκ, hκε, hlocal⟩ :=
    exists_pos_radius_zero_mem_open_of_isCompact hε hWc hJ hOo hOzero
  obtain ⟨σ, hσ, hσrad⟩ := exists_common_positive_radius hrad
  let ρ := min κ σ
  have hρ : 0 < ρ := lt_min hκ hσ
  have hρrad (s : Z) : ρ ≤ rad s := (min_le_right _ _).trans (hσrad s)
  have hsub (s : Z) : Ioo (-ρ) ρ ⊆ Ioo (-(rad s)) (rad s) :=
    Ioo_subset_Ioo (neg_le_neg (hρrad s)) (hρrad s)
  have hpossub (s : Z) : Ico (0 : ℝ) ρ ⊆ Ioo (-(rad s)) (rad s) :=
    fun r hr => ⟨(neg_lt_zero.mpr (hrad s)).trans_le hr.1,
      hr.2.trans_le (hρrad s)⟩
  refine ⟨ρ, hρ, (min_le_left _ _).trans hκε, Γ, ?_, ?_⟩
  · intro s
    refine ⟨hΓzero s, (hΓd s).mono (hsub s), hΓderiv s, ?_⟩
    intro r hr
    exact ⟨θ s r, hΓeq s r, hroot s r (hsub s hr)⟩
  · intro r hr t ht hz
    have htO := hlocal r ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩ t ht hz
    obtain ⟨s, hs⟩ := mem_iUnion.mp htO
    have hangle : |t - (s : ℝ)| < δ s := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hs
    have heq := (huniq s r (hpossub s hr) t hangle).mp hz
    refine ⟨s, ?_⟩
    rw [hΓeq s r, ← heq]

/-- For the same smooth real scalar, the exact gradient-factor jets identify the
smooth polar leading term and yield a complete finite cover by smooth radial
nodal arcs. This uses genuine smooth scalar data; no smoothness of the gauge or
its nonvanishing continuous gradient factor is assumed. -/
theorem exists_finite_smooth_nodal_arcs_of_analytic_inverse_gauge
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ} (ha : a ∈ Ω)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ ∞ v Ω)
    {P : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)}
    (hP : ContinuousOn P Ω) (hunit : IsUnit (P a))
    (hF : AnalyticAt ℂ (fun z => Ring.inverse (P z) (planarGradientSection v z)) a)
    (hgerm : ¬ ∀ᶠ z in 𝓝 a, v z = 0)
    (hvalue : v a = 0) (hgradient : fderiv ℝ v a = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball a ρ ⊆ Ω ∧
      (∀ z ∈ Metric.ball a ρ, z ≠ a → fderiv ℝ v z ≠ 0) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∃ Γ : S → ℝ → ℂ,
        (∀ s, Γ s 0 = a ∧ ContDiffOn ℝ ∞ (Γ s) (Ioo (-ρ) ρ) ∧
          HasDerivAt (Γ s) (Complex.exp (((s : ℝ) : ℂ) * Complex.I)) 0 ∧
          Set.InjOn (Γ s) (Ico 0 ρ) ∧
          (∀ r ∈ Ioo (-ρ) ρ, ‖Γ s r - a‖ = |r| ∧ v (Γ s r) = 0)) ∧
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
  have hjets := planar_jets_of_complex_gradient_factor hVo haV (hv.mono hVΩ)
    hvalue (hb.mono hVU') (fun z hz => hgradfactor z (hVU' hz))
  obtain ⟨ε, W, hε, hεV, hWd, hpolar, hWzero, _⟩ :=
    exists_smooth_polar_blowup_of_vanishing_jets hVo haV
      (Nat.succ_le_succ (Nat.zero_le k)) (hv.mono hVΩ)
      (fun j hj => hjets.1 j (Nat.le_of_lt_succ hj))
  let φ : ℝ → ℝ := fun t => (2 / ((k + 1 : ℕ) : ℝ)) *
    (b a * Complex.exp ((t : ℂ) * Complex.I) ^ (k + 1)).re
  have hWzero' (t : ℝ) : W (0, t) = φ t := by
    rw [hWzero, smul_eq_mul]
    exact hjets.2 (Complex.exp ((t : ℂ) * Complex.I))
  have hφ : Set.Finite {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ φ t = 0} ∧
      ∀ t : ℝ, φ t = 0 → deriv φ t ≠ 0 := by
    let c : ℂ := ((2 / ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) * b a
    have hc : c ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (div_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)))) hbne
    have hh := finite_simple_zeros_real_monomial_on_circle hc (Nat.succ_le_succ hk)
    simpa only [c, φ, mul_assoc, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hh
  have hfinite : Set.Finite {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ W (0, t) = 0} := by
    simpa only [hWzero', φ] using hφ.1
  have hsimple (t : ℝ) (_ht : t ∈ Icc 0 (2 * Real.pi))
      (hz : W (0, t) = 0) : deriv (fun s => W (0, s)) t ≠ 0 := by
    simpa only [hWzero', φ] using hφ.2 t (by simpa only [hWzero', φ] using hz)
  obtain ⟨ρ, hρ, hρε, γ, hγ, hcover⟩ :=
    exists_finite_smooth_polar_arcs hε hWd isCompact_Icc hfinite hsimple
  let S : Set ℝ := {t | t ∈ Icc 0 (2 * Real.pi) ∧ W (0, t) = 0}
  let Γ : S → ℝ → ℂ := fun s r => a + γ s r
  have hρV : Metric.ball a ρ ⊆ V :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hρε)).trans hεV
  have hbranch (s : S) (r : ℝ) (hr : r ∈ Ioo (-ρ) ρ) :
      ‖Γ s r - a‖ = |r| ∧ v (Γ s r) = 0 := by
    obtain ⟨t, hγeq, hWt⟩ := (hγ s).2.2.2 r hr
    have hf := hpolar r t ((abs_lt.mpr hr).trans_le hρε)
    rw [hWt, mul_zero] at hf
    constructor
    · simp only [Γ, add_sub_cancel_left, hγeq, norm_mul, Complex.norm_exp,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero,
        Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs]
    · simpa only [Γ, hγeq, Complex.real_smul] using hf
  have hpos {r : ℝ} (hr : r ∈ Ico 0 ρ) : r ∈ Ioo (-ρ) ρ :=
    ⟨(neg_lt_zero.mpr hρ).trans_le hr.1, hr.2⟩
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
      simpa only [(hbranch s r (hpos hr)).1, (hbranch s t (hpos ht)).1,
        abs_of_nonneg hr.1, abs_of_nonneg ht.1] using hn
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
        have hf := hpolar ‖z - a‖ t (by
          rw [abs_of_nonneg (norm_nonneg _)]
          exact hr.2.trans_le hρε)
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
      · exact (hbranch s r (hpos (Ioo_subset_Ico_self hr))).2

end DifferentialGeometry.Analysis
