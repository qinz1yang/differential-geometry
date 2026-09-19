import DifferentialGeometry.Analysis.Integration.Measure.Affine
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.FDeriv.Affine

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

theorem weak_divergence_comp_affineEquiv
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ᴬ[ℝ] F) {μ : Measure E} {ν : Measure F}
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    {Ω : Set F} (s : Finset ι) (v : E) (w : ι → E)
    {U R : F → ℝ} {V : ι → F → ℝ}
    (hweak : ∀ φ : F → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, U x * fderiv ℝ φ x (e.toAffineEquiv.linear v) ∂ν) =
        (∑ i ∈ s, ∫ x in Ω, V i x * fderiv ℝ φ x (e.toAffineEquiv.linear (w i)) ∂ν) -
          ∫ x in Ω, R x * φ x ∂ν) :
    ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ e ⁻¹' Ω →
      (∫ x in e ⁻¹' Ω, U (e x) * fderiv ℝ φ x v ∂μ) =
        (∑ i ∈ s, ∫ x in e ⁻¹' Ω, V i (e x) * fderiv ℝ φ x (w i) ∂μ) -
          ∫ x in e ⁻¹' Ω, R (e x) * φ x ∂μ := by
  intro φ hφ hφc hφs
  let ψ : F → ℝ := φ ∘ e.symm
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp e.symm.toContinuousAffineMap.contDiff
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph e.symm.toHomeomorph
  have hψs : tsupport ψ ⊆ Ω := by
    intro y hy
    have hy' := hφs (tsupport_comp_subset_preimage (f := e.symm) φ e.symm.continuous hy)
    simpa only [mem_preimage, ContinuousAffineEquiv.apply_symm_apply] using hy'
  have hderiv (x z : E) : fderiv ℝ ψ (e x) (e.toAffineEquiv.linear z) =
      fderiv ℝ φ x z := by
    have he : ψ ∘ e = φ := by ext x; simp [ψ]
    have hd := fderiv_comp x (hψ.differentiable (by simp) (e x))
      e.toContinuousAffineMap.differentiableAt
    rw [he] at hd
    have hde : fderiv ℝ (e : E → F) x = e.toContinuousAffineMap.contLinear :=
      e.toContinuousAffineMap.fderiv
    rw [hde] at hd
    exact (congrArg (fun L => L z) hd).symm
  have htest (x) : ψ (e x) = φ x := by simp [ψ]
  have h := hweak ψ hψ hψc hψs
  calc
    _ = Measure.addHaarScalarFactor (μ.map e) ν •
        ∫ y in Ω, U y * fderiv ℝ ψ y (e.toAffineEquiv.linear v) ∂ν := by
      rw [← integral_comp_affineEquiv e μ ν Ω]
      simp only [hderiv]
    _ = Measure.addHaarScalarFactor (μ.map e) ν •
        ((∑ i ∈ s, ∫ y in Ω, V i y * fderiv ℝ ψ y (e.toAffineEquiv.linear (w i)) ∂ν) -
          ∫ y in Ω, R y * ψ y ∂ν) := by rw [h]
    _ = _ := by
      simp only [smul_sub, Finset.smul_sum, ← integral_comp_affineEquiv e μ ν Ω, hderiv, htest]

theorem weak_deriv_comp_affineEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ᴬ[ℝ] F) {μ : Measure E} {ν : Measure F}
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    {Ω : Set F} (v : E) {U R : F → ℝ}
    (hweak : ∀ φ : F → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, U x * fderiv ℝ φ x (e.toAffineEquiv.linear v) ∂ν) =
        -∫ x in Ω, R x * φ x ∂ν) :
    ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ e ⁻¹' Ω →
      (∫ x in e ⁻¹' Ω, U (e x) * fderiv ℝ φ x v ∂μ) =
        -∫ x in e ⁻¹' Ω, R (e x) * φ x ∂μ := by
  have h := weak_divergence_comp_affineEquiv e (μ := μ) (ν := ν)
    (∅ : Finset Unit) v (fun _ => 0) (V := fun _ _ => 0)
    (fun φ hφ hφc hφs => by simpa using hweak φ hφ hφc hφs)
  simpa using h

end DifferentialGeometry.Analysis.Sobolev
