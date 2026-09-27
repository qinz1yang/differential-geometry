import DifferentialGeometry.Analysis.Convex.SpacetimeUpperContact
import DifferentialGeometry.Analysis.Integration.Integral.LipschitzProductIntegrationByParts

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace DifferentialGeometry.Analysis.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ν : Measure ℝ} {μ : Measure E}
  [IsFiniteMeasureOnCompacts ν] [Measure.IsAddHaarMeasure μ]
  {κ : Type*} [Fintype κ] {f : ℝ × E → ℝ} {S : Set ℝ} {U : Set E}

private theorem contDiff_mul_of_tsupport_subset
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {W : Set P} (hW : IsOpen W) {a φ : P → ℝ}
    (ha : ContDiffOn ℝ 2 a W) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφW : tsupport φ ⊆ W) :
    ContDiff ℝ 2 (fun p => a p * φ p) := by
  obtain ⟨aExt, haExt, _, heq⟩ := exists_contDiff_compactSupport_extension_on_isCompact
    hφc.isCompact hW hφW ha
  have hproduct : (fun p => aExt p * φ p) = (fun p => a p * φ p) := by
    funext p
    by_cases hp : p ∈ tsupport φ
    · exact congrArg (fun z => z * φ p) (heq.self_of_nhdsSet hp)
    · simp only [image_eq_zero_of_notMem_tsupport hp, mul_zero]
  exact hproduct ▸ haExt.mul hφ

private theorem fderiv_mul_of_tsupport_subset
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {W : Set P} (hW : IsOpen W) {a φ : P → ℝ}
    (ha : ContDiffOn ℝ 2 a W) (hφ : ContDiff ℝ 2 φ)
    (hφW : tsupport φ ⊆ W) (p v : P) :
    fderiv ℝ (fun y => a y * φ y) p v =
      fderiv ℝ a p v * φ p + a p * fderiv ℝ φ p v := by
  by_cases hp : p ∈ tsupport φ
  · have had : DifferentiableAt ℝ a p :=
      ((ha p (hφW hp)).contDiffAt (hW.mem_nhds (hφW hp))).differentiableAt (by norm_num)
    rw [fderiv_fun_mul had (hφ.differentiable (by norm_num) p)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  · have hz : p ∉ tsupport (fun y => a y * φ y) :=
      fun h => hp (tsupport_mul_subset_right h)
    rw [fderiv_of_notMem_tsupport ℝ hz, fderiv_of_notMem_tsupport ℝ hp,
      image_eq_zero_of_notMem_tsupport hp]
    simp

omit [IsFiniteMeasureOnCompacts ν] [Measure.IsAddHaarMeasure μ] in
private theorem integrable_mul_compact_test
    {q w : ℝ × E → ℝ} (hq : LocallyIntegrableOn q (S ×ˢ U) (ν.prod μ))
    (hw : ContinuousOn w (S ×ˢ U)) (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ S ×ˢ U) :
    Integrable (fun p => q p * w p) (ν.prod μ) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right q w).trans (subset_tsupport w))).mp
  exact (hq.integrableOn_compact_subset hwU hwc.isCompact).mul_continuousOn
    (hw.mono hwU) hwc.isCompact

theorem integral_add_sum_spatial_derivative_mul_nonneg_of_ae_approximate_upper_contacts
    (hlip : LocallyLipschitzOn (S ×ˢ U) f)
    (hS : IsOpen S) (hU : IsOpen U) (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ t ∈ S, ConcaveOn ℝ U (fun x => f (t, x) - A x x / 2))
    (v : κ → E) (a : κ → ℝ × E → ℝ)
    (ha : ∀ k, ContDiffOn ℝ 2 (a k) (S ×ˢ U))
    (hanonneg : ∀ k, ∀ p ∈ S ×ˢ U, 0 ≤ a k p)
    (B : ℝ × E → ℝ) (hB : LocallyIntegrableOn B (S ×ˢ U) (ν.prod μ))
    (hcontact : ∀ᵐ p ∂ν.prod μ, p ∈ S ×ˢ U → ∀ ε : ℝ, 0 < ε → ∃ ψ : κ → ℝ → ℝ,
      (∀ k, ContDiffAt ℝ 2 (ψ k) 0) ∧
      (∀ k, ∀ᶠ t in 𝓝 0, f (p.1, p.2 + t • v k) ≤ ψ k t) ∧
      (∀ k, f p = ψ k 0) ∧
      (∑ k, a k p * deriv (deriv (ψ k)) 0) ≤ B p -
        (∑ k, fderiv ℝ (a k) p (0, v k) *
          fderiv ℝ (fun x => f (p.1, x)) p.2 (v k)) + ε)
    (φ : ℝ × E → ℝ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ S ×ˢ U) (hφnonneg : ∀ p, 0 ≤ φ p) :
    0 ≤ ∫ p, B p * φ p + ∑ k, a k p *
      fderiv ℝ (fun x => f (p.1, x)) p.2 (v k) * fderiv ℝ φ p (0, v k) ∂ν.prod μ := by
  classical
  let d : κ → ℝ × E → ℝ := fun k p => fderiv ℝ (fun x => f (p.1, x)) p.2 (v k)
  let da : κ → ℝ × E → ℝ := fun k p => fderiv ℝ (a k) p (0, v k)
  let drift : ℝ × E → ℝ := fun p => ∑ k, da k p * d k p
  have hdint : ∀ k, LocallyIntegrableOn (d k) (S ×ˢ U) (ν.prod μ) := by
    intro k
    apply MeasureTheory.locallyIntegrableOn_of_integrable_mul_contDiff (n := 1) (hS.prod hU)
    intro θ hθ hθc hθU _
    exact (hlip.integral_fderiv_prod_eq_neg (hS.prod hU) hθ hθc hθU (v k)).2.1
  have hdacont : ∀ k, ContinuousOn (da k) (S ×ˢ U) := by
    intro k
    exact ((ha k).continuousOn_fderiv_of_isOpen (hS.prod hU) (by norm_num)).clm_apply
      continuousOn_const
  have hdrift : LocallyIntegrableOn drift (S ×ˢ U) (ν.prod μ) := by
    apply (locallyIntegrableOn_iff (hS.prod hU).isLocallyClosed).mpr
    intro K hKU hK
    apply integrable_finsetSum Finset.univ
    intro k _
    exact ((hdint k).continuousOn_mul (hdacont k)
      (hS.prod hU).isLocallyClosed).integrableOn_compact_subset hKU hK
  have hcmp := integral_sum_spatial_second_derivative_le_of_ae_approximate_upper_contacts
    hlip.continuousOn hS hU A hf v a ha hanonneg (fun p => B p - drift p)
    (hB.sub hdrift) hcontact φ hφ hφc hφU hφnonneg
  let w : κ → ℝ × E → ℝ := fun k p => a k p * φ p
  have hw : ∀ k, ContDiff ℝ 2 (w k) := fun k =>
    contDiff_mul_of_tsupport_subset (hS.prod hU) (ha k) hφ hφc hφU
  have hwc : ∀ k, HasCompactSupport (w k) := fun _ => hφc.mul_left
  have hwU : ∀ k, tsupport (w k) ⊆ S ×ˢ U :=
    fun _ => tsupport_mul_subset_right.trans hφU
  let dw : κ → ℝ × E → ℝ := fun k p => fderiv ℝ (w k) p (0, v k)
  have hdw : ∀ k, ContDiff ℝ 1 (dw k) := fun k =>
    ((hw k).fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdwc : ∀ k, HasCompactSupport (dw k) := fun k =>
    (hwc k).fderiv_apply ℝ (0, v k)
  have hdwU : ∀ k, tsupport (dw k) ⊆ S ×ˢ U := fun k =>
    (tsupport_fderiv_apply_subset ℝ (0, v k)).trans (hwU k)
  have hibp (k) := hlip.integral_fderiv_prod_eq_neg (ν := ν) (μ := μ) (hS.prod hU)
    (hdw k) (hdwc k) (hdwU k) (v k)
  have hpair (k) : (∫ p, f p * fderiv ℝ (dw k) p (0, v k) ∂ν.prod μ) =
      -(∫ p, d k p * dw k p ∂ν.prod μ) := (hibp k).2.2
  have hdweq (k) (p) : dw k p = da k p * φ p + a k p * fderiv ℝ φ p (0, v k) :=
    fderiv_mul_of_tsupport_subset (hS.prod hU) (ha k) hφ hφU p (0, v k)
  let flux : ℝ × E → ℝ := fun p => ∑ k, a k p * d k p * fderiv ℝ φ p (0, v k)
  have hfluxint : Integrable flux (ν.prod μ) := by
    apply integrable_finsetSum Finset.univ
    intro k _
    have hwgt : ContinuousOn (fun p => a k p * fderiv ℝ φ p (0, v k)) (S ×ˢ U) :=
      (ha k).continuousOn.mul
        ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn
    have hi := integrable_mul_compact_test (hdint k) hwgt
      ((hφc.fderiv_apply ℝ (0, v k)).mul_left)
      (tsupport_mul_subset_right.trans
        ((tsupport_fderiv_apply_subset ℝ (0, v k)).trans hφU))
    apply hi.congr
    exact Eventually.of_forall fun p => by dsimp [d]; ring
  have hBint : Integrable (fun p => B p * φ p) (ν.prod μ) :=
    integrable_mul_compact_test hB hφ.continuous.continuousOn hφc hφU
  have hdriftint : Integrable (fun p => drift p * φ p) (ν.prod μ) :=
    integrable_mul_compact_test hdrift hφ.continuous.continuousOn hφc hφU
  have hleft : (∫ p, f p * ∑ k, fderiv ℝ (dw k) p (0, v k) ∂ν.prod μ) =
      -((∫ p, drift p * φ p ∂ν.prod μ) + ∫ p, flux p ∂ν.prod μ) := by
    calc
      _ = ∑ k, ∫ p, f p * fderiv ℝ (dw k) p (0, v k) ∂ν.prod μ := by
        simp_rw [Finset.mul_sum]
        exact integral_finsetSum Finset.univ fun k _ => (hibp k).1
      _ = -(∑ k, ∫ p, d k p * dw k p ∂ν.prod μ) := by
        simp only [hpair, Finset.sum_neg_distrib]
      _ = -(∫ p, ∑ k, d k p * dw k p ∂ν.prod μ) := by
        rw [integral_finsetSum Finset.univ fun k _ => (hibp k).2.1]
      _ = -(∫ p, drift p * φ p + flux p ∂ν.prod μ) := by
        congr 1
        apply integral_congr_ae
        apply Eventually.of_forall
        intro p
        dsimp only [drift, flux]
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [hdweq]
        ring
      _ = _ := by rw [integral_add hdriftint hfluxint]
  have hright : (∫ p, (B p - drift p) * φ p ∂ν.prod μ) =
      (∫ p, B p * φ p ∂ν.prod μ) - ∫ p, drift p * φ p ∂ν.prod μ := by
    simp_rw [sub_mul]
    exact integral_sub hBint hdriftint
  change (∫ p, f p * ∑ k, fderiv ℝ (dw k) p (0, v k) ∂ν.prod μ) ≤
    ∫ p, (B p - drift p) * φ p ∂ν.prod μ at hcmp
  rw [hleft, hright] at hcmp
  change 0 ≤ ∫ p, B p * φ p + flux p ∂ν.prod μ
  rw [integral_add hBint hfluxint]
  linarith

end DifferentialGeometry.Analysis.Calculus
