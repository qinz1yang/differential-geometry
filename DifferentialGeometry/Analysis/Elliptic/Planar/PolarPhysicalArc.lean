import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.LeftRight
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- A one-sided polar arc with vanishing weighted angular derivative has a `C¹`
straight extension through its center. No derivative of the angle at zero is assumed. -/
theorem exists_contDiff_polar_physical_arc {ε : ℝ} (hε : 0 < ε)
    {θ : ℝ → ℝ} {θ₀ : ℝ} (hθ0 : θ 0 = θ₀)
    (hθc : ContinuousOn θ (Ico 0 ε)) (hθd : ContDiffOn ℝ 1 θ (Ioo 0 ε))
    (hweighted : Tendsto (fun r => r * deriv θ r) (𝓝[>] 0) (𝓝 0)) :
    ∃ Γ : ℝ → ℂ, Γ 0 = 0 ∧
      (∀ r ∈ Ico 0 ε, Γ r = (r : ℂ) * Complex.exp ((θ r : ℂ) * Complex.I)) ∧
      ContDiffOn ℝ 1 Γ (Ioo (-ε) ε) ∧
      HasDerivAt Γ (Complex.exp ((θ₀ : ℂ) * Complex.I)) 0 := by
  let e : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * Complex.I)
  let Γ : ℝ → ℂ := fun r => if r ≤ 0 then r • e θ₀ else r • e (θ r)
  let D : ℝ → ℂ := fun r => if r ≤ 0 then e θ₀ else
    e (θ r) + ((r * deriv θ r : ℝ) : ℂ) * Complex.I * e (θ r)
  have hΓ0 : Γ 0 = 0 := by simp [Γ]
  have hD0 : D 0 = e θ₀ := by simp [D]
  have he : Continuous e :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hθlim : Tendsto θ (𝓝[>] 0) (𝓝 θ₀) := by
    have hright : ContinuousWithinAt θ (Ioi 0) 0 :=
      (hθc 0 ⟨le_rfl, hε⟩).mono_of_mem_nhdsWithin (by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε)] with r hr hrε
        exact ⟨le_of_lt hr, hrε⟩)
    simpa only [hθ0] using hright.tendsto
  have helim : Tendsto (fun r => e (θ r)) (𝓝[>] 0) (𝓝 (e θ₀)) :=
    (he.tendsto θ₀).comp hθlim
  have hd0 : HasDerivAt Γ (e θ₀) 0 := by
    apply hasDerivAt_iff_tendsto_slope_left_right.mpr
    constructor
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      change r < (0 : ℝ) at hr
      simp only [slope_def_module, sub_zero, hΓ0]
      simp [Γ, le_of_lt hr, ne_of_lt hr]
    · apply helim.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      change (0 : ℝ) < r at hr
      simp only [slope_def_module, sub_zero, hΓ0]
      simp [Γ, not_le.mpr hr, ne_of_gt hr]
  have hdpos (r : ℝ) (hr : 0 < r) (hrε : r < ε) :
      HasDerivAt Γ (D r) r := by
    have hθr : HasDerivAt θ (deriv θ r) r :=
      ((hθd r ⟨hr, hrε⟩).contDiffAt (isOpen_Ioo.mem_nhds ⟨hr, hrε⟩)).differentiableAt
        one_ne_zero |>.hasDerivAt
    have hcomplex : HasDerivAt (fun t : ℝ => (θ t : ℂ)) ((deriv θ r : ℝ) : ℂ) r :=
      hθr.ofReal_comp
    have hangle : HasDerivAt (fun t : ℝ => (θ t : ℂ) * Complex.I)
        (((deriv θ r : ℝ) : ℂ) * Complex.I) r := hcomplex.mul_const Complex.I
    have heθ : HasDerivAt (fun t => e (θ t))
        (e (θ r) * (((deriv θ r : ℝ) : ℂ) * Complex.I)) r := hangle.cexp
    have hprod : HasDerivAt (fun t : ℝ => t • e (θ t))
        (r • (e (θ r) * (((deriv θ r : ℝ) : ℂ) * Complex.I)) + e (θ r)) r := by
      simpa only [Pi.smul_def', id_eq, one_smul] using (hasDerivAt_id r).smul heθ
    have hcoeff : r • (e (θ r) * (((deriv θ r : ℝ) : ℂ) * Complex.I)) + e (θ r) = D r := by
      simp only [D, not_le.mpr hr, ite_false, Complex.real_smul, Complex.ofReal_mul]
      ring
    have hprod' := hprod.congr_deriv hcoeff
    apply hprod'.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hr] with t ht
    change (0 : ℝ) < t at ht
    simp [Γ, not_le.mpr ht]
  have hdneg (r : ℝ) (hr : r < 0) : HasDerivAt Γ (D r) r := by
    have hprod : HasDerivAt (fun t : ℝ => t • e θ₀) (e θ₀) r := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id r).smul_const (e θ₀)
    have hprod' : HasDerivAt (fun t : ℝ => t • e θ₀) (D r) r := by
      simpa only [D, le_of_lt hr, ite_true] using hprod
    apply hprod'.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hr] with t ht
    change t < (0 : ℝ) at ht
    simp [Γ, le_of_lt ht]
  have hd (r : ℝ) (hr : r ∈ Ioo (-ε) ε) : HasDerivAt Γ (D r) r := by
    rcases lt_trichotomy r 0 with h | h | h
    · exact hdneg r h
    · subst r
      simpa only [hD0] using hd0
    · exact hdpos r h hr.2
  have hDc0 : ContinuousAt D 0 := by
    rw [continuousAt_iff_continuous_left'_right']
    constructor
    · change Tendsto D (𝓝[<] 0) (𝓝 (D 0))
      rw [hD0]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      change r < (0 : ℝ) at hr
      simp [D, le_of_lt hr]
    · change Tendsto D (𝓝[>] 0) (𝓝 (D 0))
      rw [hD0]
      have hw : Tendsto (fun r => ((r * deriv θ r : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
        simpa only [Function.comp_def, Complex.ofReal_zero] using
          (Complex.continuous_ofReal.tendsto 0).comp hweighted
      have hlim := helim.add ((hw.mul_const Complex.I).mul helim)
      simp only [zero_mul, add_zero] at hlim
      apply hlim.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      change (0 : ℝ) < r at hr
      simp [D, not_le.mpr hr]
  have hDc : ContinuousOn D (Ioo (-ε) ε) := by
    intro r hr
    rcases lt_trichotomy r 0 with h | h | h
    · have hconst : ContinuousAt (fun _ : ℝ => e θ₀) r := continuousAt_const
      apply (hconst.congr ?_).continuousWithinAt
      filter_upwards [Iio_mem_nhds h] with t ht
      change t < (0 : ℝ) at ht
      simp [D, le_of_lt ht]
    · subst r
      exact hDc0.continuousWithinAt
    · have hθcr : ContinuousAt θ r :=
        (hθd.continuousOn r ⟨h, hr.2⟩).continuousAt (isOpen_Ioo.mem_nhds ⟨h, hr.2⟩)
      have hθdr : ContinuousAt (deriv θ) r :=
        (hθd.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl r ⟨h, hr.2⟩).continuousAt
          (isOpen_Ioo.mem_nhds ⟨h, hr.2⟩)
      have hecr : ContinuousAt (fun t => e (θ t)) r := he.continuousAt.comp hθcr
      have hwcr : ContinuousAt (fun t => ((t * deriv θ t : ℝ) : ℂ)) r :=
        Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.mul hθdr)
      have hsum := hecr.add ((hwcr.mul_const Complex.I).mul hecr)
      apply (hsum.congr ?_).continuousWithinAt
      filter_upwards [Ioi_mem_nhds h] with t ht
      change (0 : ℝ) < t at ht
      simp [D, not_le.mpr ht]
  have hΓc : ContDiffOn ℝ 1 Γ (Ioo (-ε) ε) := by
    rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun r hr => (hd r hr).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact hDc.congr (fun r hr => (hd r hr).deriv)
  refine ⟨Γ, hΓ0, ?_, hΓc, hd0⟩
  intro r hr
  rcases eq_or_lt_of_le hr.1 with h | h
  · subst r
    simp only [hΓ0, Complex.ofReal_zero, zero_mul]
  · simp only [Γ, not_le.mpr h, ite_false, Complex.real_smul, e]

end DifferentialGeometry.Analysis
