import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Compactness.LocallyCompact


noncomputable section

namespace LocallyLipschitzOn

open Filter MeasureTheory Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]
  {Ω : Set E} {f φ : E → ℝ}

theorem integral_fderiv_mul_eq_neg_mul_fderiv
    (hf : LocallyLipschitzOn Ω f) (hΩ : IsOpen Ω)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) (v : E) :
    (∫ z, fderiv ℝ f z v * φ z ∂μ) =
      -∫ z, f z * fderiv ℝ φ z v ∂μ := by
  obtain ⟨L, hL, hφL, hLΩ⟩ := exists_compact_between hφc hΩ hφΩ
  obtain ⟨C, hfL⟩ := (hf.mono hLΩ).exists_lipschitzOnWith_of_compact hL
  obtain ⟨g, hg, hfg⟩ := hfL.extend_real
  have hfgerm {z : E} (hz : z ∈ tsupport φ) : f =ᶠ[𝓝 z] g := by
    filter_upwards [isOpen_interior.mem_nhds (hφL hz)] with y hy
    exact hfg (interior_subset hy)
  obtain ⟨D, hφlip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ one_ne_zero
  have hleft :
      (fun z => lineDeriv ℝ g z v * φ z) =ᵐ[μ]
        (fun z => fderiv ℝ f z v * φ z) := by
    filter_upwards [hg.ae_differentiableAt (μ := μ)] with z hz
    by_cases hzs : z ∈ tsupport φ
    · rw [hz.lineDeriv_eq_fderiv, ← (hfgerm hzs).fderiv_eq]
    · rw [image_eq_zero_of_notMem_tsupport hzs]
      simp only [mul_zero]
  have hright :
      (fun z => lineDeriv ℝ φ z (-v) * g z) =
        (fun z => -(f z * fderiv ℝ φ z v)) := by
    funext z
    rw [(hφ.differentiable one_ne_zero z).lineDeriv_eq_fderiv, map_neg]
    by_cases hzs : z ∈ tsupport φ
    · rw [← hfg (interior_subset (hφL hzs))]
      ring
    · rw [fderiv_of_notMem_tsupport ℝ hzs]
      simp only [zero_apply, neg_zero, zero_mul, mul_zero]
  calc
    (∫ z, fderiv ℝ f z v * φ z ∂μ) =
        ∫ z, lineDeriv ℝ g z v * φ z ∂μ :=
      (integral_congr_ae hleft).symm
    _ = ∫ z, lineDeriv ℝ φ z (-v) * g z ∂μ :=
      hg.integral_lineDeriv_mul_eq hφlip hφc v
    _ = -∫ z, f z * fderiv ℝ φ z v ∂μ := by
      rw [hright, integral_neg]

end LocallyLipschitzOn
