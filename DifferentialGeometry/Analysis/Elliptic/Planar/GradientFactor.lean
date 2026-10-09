import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.FiniteOrder
import DifferentialGeometry.Analysis.Elliptic.Planar.FirstOrderReduction
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.FunProp

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace DifferentialGeometry.Analysis

private theorem complex_power_real_factor_zero
    {a : ℂ} {k : ℕ} (hk : 0 < k) {K : ℂ → ℂ}
    (hK : ContinuousAt K a)
    (hreal : ∀ᶠ z in 𝓝 a, ((z - a) ^ k * K z).im = 0) :
    K a = 0 := by
  have hdir (u : ℂ) : (u ^ k * K a).im = 0 := by
    have ht : Tendsto (fun t : ℝ => a + (t : ℂ) * u)
        (𝓝[>] (0 : ℝ)) (𝓝 a) := by
      have hc : Continuous (fun t : ℝ => a + (t : ℂ) * u) := by fun_prop
      simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
        (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun t : ℝ => (u ^ k * K (a + (t : ℂ) * u)).im)
        (𝓝[>] (0 : ℝ)) (𝓝 ((u ^ k * K a).im)) :=
      Complex.continuous_im.continuousAt.tendsto.comp
        (tendsto_const_nhds.mul (hK.tendsto.comp ht))
    have heq : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        (u ^ k * K (a + (t : ℂ) * u)).im = 0 := by
      filter_upwards [ht.eventually hreal, self_mem_nhdsWithin] with t hz htpos
      have htpos' : 0 < t := htpos
      rw [add_sub_cancel_left, mul_pow, mul_assoc] at hz
      have hz' : t ^ k * (u ^ k * K (a + (t : ℂ) * u)).im = 0 := by
        simpa only [← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, add_zero] using hz
      exact (mul_eq_zero.mp hz').resolve_left (pow_ne_zero _ (ne_of_gt htpos'))
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm))
  have him : (K a).im = 0 := by simpa using hdir 1
  have hroot : (Complex.I ^ (k⁻¹ : ℂ)) ^ k = Complex.I :=
    Complex.cpow_nat_inv_pow _ (ne_of_gt hk)
  have hre : (K a).re = 0 := by
    simpa only [hroot, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_add] using hdir (Complex.I ^ (k⁻¹ : ℂ))
  exact Complex.ext hre him



private theorem exists_first_component_factor_of_real_second
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ} (ha : a ∈ Ω)
    {ξ : ℂ → ℂ × ℂ} {P : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)}
    (hP : ContinuousOn P Ω) (hunit : IsUnit (P a))
    (hF : AnalyticAt ℂ (fun z => Ring.inverse (P z) (ξ z)) a)
    (hgerm : ¬ ∀ᶠ z in 𝓝 a, ξ z = 0)
    (hzero : ξ a = 0) (hreal : ∀ z, (ξ z).2.im = 0) :
    ∃ U : Set ℂ, IsOpen U ∧ a ∈ U ∧ U ⊆ Ω ∧
      ∃ k : ℕ, k = analyticOrderNatAt (fun z => Ring.inverse (P z) (ξ z)) a ∧
        1 ≤ k ∧ ∃ b : ℂ → ℂ, ContinuousOn b U ∧ b a ≠ 0 ∧
          ∀ z ∈ U, (ξ z).1 = (z - a) ^ k * b z := by
  have hP0 : ContDiffAt ℝ 0 P a :=
    contDiffAt_zero.mpr ⟨Ω, hΩ.mem_nhds ha, hP⟩
  obtain ⟨_, G, _, _, hK, hKne, hfactor⟩ :=
    exists_finite_order_factor_of_analytic_inverse_gauge hP0 hunit hF hgerm
  let K : ℂ → ℂ × ℂ := fun z => P z (G z)
  let k := analyticOrderNatAt (fun z => Ring.inverse (P z) (ξ z)) a
  change ContDiffAt ℝ 0 K a at hK
  change K a ≠ 0 at hKne
  change ∀ᶠ z in 𝓝 a, ξ z = (z - a) ^ k • K z at hfactor
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hk0
    have hh := hfactor.self_of_nhds
    rw [hk0, pow_zero, one_smul, hzero] at hh
    exact hKne hh.symm
  have hKr : ∀ᶠ z in 𝓝 a, ((z - a) ^ k * (K z).2).im = 0 := by
    filter_upwards [hfactor] with z hz
    have hr := hreal z
    rw [hz] at hr
    simpa only [Prod.smul_snd, smul_eq_mul] using hr
  have hK2 : (K a).2 = 0 :=
    complex_power_real_factor_zero hk hK.continuousAt.snd hKr
  have hK1 : (K a).1 ≠ 0 := by
    intro hh
    apply hKne
    exact Prod.ext hh hK2
  obtain ⟨s, hs, hKs⟩ := contDiffAt_zero.mp hK
  have hN : s ∩ Ω ∩ {z | ξ z = (z - a) ^ k • K z} ∈ 𝓝 a :=
    inter_mem (inter_mem hs (hΩ.mem_nhds ha)) hfactor
  obtain ⟨U, hUs, hUo, haU⟩ := mem_nhds_iff.mp hN
  refine ⟨U, hUo, haU, fun z hz => (hUs hz).1.2, k, rfl, hk,
    fun z => (K z).1, (hKs.mono (fun z hz => (hUs hz).1.1)).fst, hK1, ?_⟩
  intro z hz
  have hh := congrArg Prod.fst (hUs hz).2
  simpa only [Prod.smul_fst, smul_eq_mul] using hh



/-- A nonzero scalar germ at an actual critical zero has a nonvanishing continuous
factor in its actual half-normalized complex gradient. The order is exactly the
order of the same analytic inverse-gauge augmented section. -/
theorem exists_planar_gradient_factor_of_analytic_inverse_gauge
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ} (ha : a ∈ Ω)
    {v : ℂ → ℝ} {P : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)}
    (hP : ContinuousOn P Ω) (hunit : IsUnit (P a))
    (hF : AnalyticAt ℂ (fun z => Ring.inverse (P z) (planarGradientSection v z)) a)
    (hgerm : ¬ ∀ᶠ z in 𝓝 a, v z = 0)
    (hvalue : v a = 0) (hgradient : fderiv ℝ v a = 0) :
    ∃ U : Set ℂ, IsOpen U ∧ a ∈ U ∧ U ⊆ Ω ∧
      ∃ k : ℕ,
        k = analyticOrderNatAt
          (fun z => Ring.inverse (P z) (planarGradientSection v z)) a ∧
        1 ≤ k ∧ ∃ b : ℂ → ℂ, ContinuousOn b U ∧ b a ≠ 0 ∧
          ∀ z ∈ U, planarComplexGradient v z = (z - a) ^ k * b z := by
  have hsection : ¬ ∀ᶠ z in 𝓝 a, planarGradientSection v z = 0 := by
    intro hz
    apply hgerm
    filter_upwards [hz] with z hzz
    exact ((planarGradientSection_eq_zero_iff v z).mp hzz).1
  have hzero : planarGradientSection v a = 0 :=
    (planarGradientSection_eq_zero_iff v a).mpr ⟨hvalue, hgradient⟩
  have hreal : ∀ z, (planarGradientSection v z).2.im = 0 := by
    intro z
    simp only [planarGradientSection, Complex.ofReal_im]
  exact exists_first_component_factor_of_real_second hΩ ha hP hunit hF
    hsection hzero hreal

/-- The same actual scalar is zero on a neighborhood, or its actual complex
 gradient has the continuous nonvanishing factor required by the polar argument. -/
theorem planar_scalar_zero_germ_or_gradient_factor_of_critical_zero
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ} (ha : a ∈ Ω)
    {v : ℂ → ℝ} {P : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)}
    (hP : ContinuousOn P Ω) (hunit : IsUnit (P a))
    (hF : AnalyticAt ℂ (fun z => Ring.inverse (P z) (planarGradientSection v z)) a)
    (hvalue : v a = 0) (hgradient : fderiv ℝ v a = 0) :
    (∀ᶠ z in 𝓝 a, v z = 0) ∨
      ∃ U : Set ℂ, IsOpen U ∧ a ∈ U ∧ U ⊆ Ω ∧
        ∃ k : ℕ,
          k = analyticOrderNatAt
            (fun z => Ring.inverse (P z) (planarGradientSection v z)) a ∧
          1 ≤ k ∧ ∃ b : ℂ → ℂ, ContinuousOn b U ∧ b a ≠ 0 ∧
            ∀ z ∈ U, planarComplexGradient v z = (z - a) ^ k * b z := by
  by_cases hgerm : ∀ᶠ z in 𝓝 a, v z = 0
  · exact Or.inl hgerm
  · exact Or.inr (exists_planar_gradient_factor_of_analytic_inverse_gauge
      hΩ ha hP hunit hF hgerm hvalue hgradient)

end DifferentialGeometry.Analysis
