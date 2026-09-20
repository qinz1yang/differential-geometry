import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support


noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem mul_exp_neg_mul_nonneg_of_tsupport_subset
    {X : Type*} [TopologicalSpace X] {Ω : Set X} {a ell φ : X → ℝ}
    (ha : ∀ x ∈ Ω, 0 ≤ a x) (hφ : ∀ x, 0 ≤ φ x)
    (hsupp : tsupport φ ⊆ Ω) (x : X) :
    0 ≤ a x * Real.exp (-ell x) * φ x := by
  by_cases hx : x ∈ tsupport φ
  · exact mul_nonneg (mul_nonneg (ha x (hsupp hx)) (Real.exp_pos _).le) (hφ x)
  · have hzero : φ x = 0 := by
      by_contra hne
      exact hx (subset_tsupport φ hne)
    simp only [hzero, mul_zero, le_refl]

section LocalRegularity

variable {E : Type*} [PseudoEMetricSpace E]

private theorem locallyLipschitzOn_real_mul
    {s : Set E} {f g : E → ℝ}
    (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g) :
    LocallyLipschitzOn s (fun x => f x * g x) := by
  have hm : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 * p.2) :=
    contDiff_fst.mul contDiff_snd
  apply locallyLipschitzOn_iff_restrict.mpr
  exact hm.locallyLipschitz.comp (hf.restrict.prodMk hg.restrict)

theorem locallyLipschitzOn_mul_exp_neg
    {s : Set E} {a ell : E → ℝ}
    (ha : LocallyLipschitzOn s a) (hell : LocallyLipschitzOn s ell) :
    LocallyLipschitzOn s (fun x => a x * Real.exp (-ell x)) := by
  have he : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-t)) := contDiff_id.neg.exp
  have hellExp : LocallyLipschitzOn s (fun x => Real.exp (-ell x)) := by
    apply locallyLipschitzOn_iff_restrict.mpr
    exact he.locallyLipschitz.comp hell.restrict
  exact locallyLipschitzOn_real_mul ha hellExp

theorem locallyLipschitzOn_mul_exp_neg_mul
    {s : Set E} {a ell φ : E → ℝ}
    (ha : LocallyLipschitzOn s a) (hell : LocallyLipschitzOn s ell)
    (hφ : LocallyLipschitzOn s φ) :
    LocallyLipschitzOn s (fun x => a x * Real.exp (-ell x) * φ x) :=
  locallyLipschitzOn_real_mul (locallyLipschitzOn_mul_exp_neg ha hell) hφ

theorem locallyLipschitz_mul_exp_neg_mul_of_tsupport_subset
    {Ω : Set E} (hΩ : IsOpen Ω) {a ell φ : E → ℝ}
    (ha : LocallyLipschitzOn Ω a) (hell : LocallyLipschitzOn Ω ell)
    (hφ : LocallyLipschitzOn Ω φ) (hsupp : tsupport φ ⊆ Ω) :
    LocallyLipschitz (fun x => a x * Real.exp (-ell x) * φ x) := by
  have hψ := locallyLipschitzOn_mul_exp_neg_mul ha hell hφ
  intro x
  by_cases hx : x ∈ Ω
  · obtain ⟨C, U, hU, hC⟩ := hψ hx
    exact ⟨C, U, by simpa only [hΩ.nhdsWithin_eq hx] using hU, hC⟩
  · have hxnot : x ∈ (tsupport φ)ᶜ := fun hs => hx (hsupp hs)
    refine ⟨0, (tsupport φ)ᶜ, (isClosed_tsupport φ).isOpen_compl.mem_nhds hxnot, ?_⟩
    intro y hy z hz
    have hyzero : φ y = 0 := by
      by_contra hne
      exact hy (subset_tsupport φ hne)
    have hzzero : φ z = 0 := by
      by_contra hne
      exact hz (subset_tsupport φ hne)
    simp only [hyzero, hzzero, mul_zero, edist_self, ENNReal.coe_zero, zero_mul, le_refl]

end LocalRegularity

section Derivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_mul_exp_neg
    {a ell : E → ℝ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hell : DifferentiableAt ℝ ell x) :
    fderiv ℝ (fun y => a y * Real.exp (-ell y)) x =
      Real.exp (-ell x) • fderiv ℝ a x -
        (a x * Real.exp (-ell x)) • fderiv ℝ ell x := by
  simpa only [Pi.mul_apply, Pi.neg_apply, smul_neg, smul_smul, sub_eq_add_neg, add_comm] using
    (ha.hasFDerivAt.fun_mul hell.hasFDerivAt.neg.exp).fderiv

section Haar

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

private theorem ae_differentiableAt_of_locallyLipschitzOn_compact_closure
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f) :
    ∀ᵐ x ∂μ.restrict Ω, DifferentiableAt ℝ f x := by
  obtain ⟨C, hC⟩ := hf.exists_lipschitzOnWith_of_compact hΩc
  filter_upwards [ae_restrict_mem hΩ.measurableSet,
    (hC.mono subset_closure).ae_differentiableWithinAt (μ := μ) hΩ.measurableSet]
      with x hx hdx
  exact hdx.differentiableAt (hΩ.mem_nhds hx)

theorem ae_fderiv_mul_exp_neg_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {a ell : E → ℝ} (ha : LocallyLipschitzOn (closure Ω) a)
    (hell : LocallyLipschitzOn (closure Ω) ell) :
    (fun x => fderiv ℝ (fun y => a y * Real.exp (-ell y)) x)
      =ᵐ[μ.restrict Ω]
        (fun x => Real.exp (-ell x) • fderiv ℝ a x -
          (a x * Real.exp (-ell x)) • fderiv ℝ ell x) := by
  filter_upwards [ae_differentiableAt_of_locallyLipschitzOn_compact_closure
    hΩ hΩc ha, ae_differentiableAt_of_locallyLipschitzOn_compact_closure
    hΩ hΩc hell] with x hax hellx
  exact fderiv_mul_exp_neg hax hellx

theorem ae_fderiv_mul_exp_neg_mul_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {a ell φ : E → ℝ} (ha : LocallyLipschitzOn (closure Ω) a)
    (hell : LocallyLipschitzOn (closure Ω) ell)
    (hφ : LocallyLipschitzOn (closure Ω) φ) :
    (fun x => fderiv ℝ (fun y => a y * Real.exp (-ell y) * φ y) x)
      =ᵐ[μ.restrict Ω]
        (fun x => (a x * Real.exp (-ell x)) • fderiv ℝ φ x +
          φ x • fderiv ℝ (fun y => a y * Real.exp (-ell y)) x) := by
  filter_upwards [ae_differentiableAt_of_locallyLipschitzOn_compact_closure
    hΩ hΩc (locallyLipschitzOn_mul_exp_neg ha hell),
    ae_differentiableAt_of_locallyLipschitzOn_compact_closure
      hΩ hΩc hφ] with x hux hφx
  exact fderiv_fun_mul hux hφx

theorem ae_fderiv_mul_exp_neg_mul_expanded_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {a ell φ : E → ℝ} (ha : LocallyLipschitzOn (closure Ω) a)
    (hell : LocallyLipschitzOn (closure Ω) ell)
    (hφ : LocallyLipschitzOn (closure Ω) φ) :
    (fun x => fderiv ℝ (fun y => a y * Real.exp (-ell y) * φ y) x)
      =ᵐ[μ.restrict Ω]
        (fun x => (a x * Real.exp (-ell x)) • fderiv ℝ φ x +
          φ x • (Real.exp (-ell x) • fderiv ℝ a x -
            (a x * Real.exp (-ell x)) • fderiv ℝ ell x)) := by
  filter_upwards [ae_fderiv_mul_exp_neg_mul_of_locallyLipschitzOn hΩ hΩc ha hell hφ,
    ae_fderiv_mul_exp_neg_of_locallyLipschitzOn hΩ hΩc ha hell] with x hψ hu
  exact hψ.trans (congrArg (fun L =>
    (a x * Real.exp (-ell x)) • fderiv ℝ φ x + φ x • L) hu)

end Haar

end Derivatives

end DifferentialGeometry.Analysis
