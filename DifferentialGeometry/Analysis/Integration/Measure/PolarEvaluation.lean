import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Polar evaluation for additive Haar measure

This file exposes the product and iterated-lintegral forms of the generalized
polar decomposition supplied by `Measure.measurePreserving_homeomorphUnitSphereProd`.
-/

noncomputable section

open Metric Set
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [Nontrivial E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Polar product decomposition of a nonnegative integral against additive
Haar measure. The origin is discarded as a null set. -/
theorem lintegral_polar_prod (f : E → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ =
      ∫⁻ z : sphere (0 : E) 1 × Ioi (0 : ℝ),
        f (z.2.1 • z.1.1)
          ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  let Φ := homeomorphUnitSphereProd E
  calc
    ∫⁻ x, f x ∂μ = ∫⁻ x in ({0}ᶜ : Set E), f x ∂μ := by
      exact congrArg (fun ν : Measure E => ∫⁻ x, f x ∂ν)
        (restrict_compl_singleton (μ := μ) 0).symm
    _ = ∫⁻ x : ({0}ᶜ : Set E), f x ∂(μ.comap ((↑) : ({0}ᶜ : Set E) → E)) := by
      rw [lintegral_subtype_comap isOpen_compl_singleton.measurableSet]
    _ = ∫⁻ z : sphere (0 : E) 1 × Ioi (0 : ℝ),
          f ((Φ.symm z : ({0}ᶜ : Set E)) : E)
            ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      simpa only [Φ, Homeomorph.symm_apply_apply] using
        (μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
          Φ.measurableEmbedding
          (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) =>
            f ((Φ.symm z : ({0}ᶜ : Set E)) : E)))
    _ = ∫⁻ z : sphere (0 : E) 1 × Ioi (0 : ℝ),
          f (z.2.1 • z.1.1)
            ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      congr 1

/-- Tonelli form of `lintegral_polar_prod`. -/
theorem lintegral_polar (f : E → ℝ≥0∞) (hf : AEMeasurable f μ) :
    ∫⁻ x, f x ∂μ =
      ∫⁻ u : sphere (0 : E) 1,
        ∫⁻ r : Ioi (0 : ℝ), f (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) ∂μ.toSphere := by
  let Φ := homeomorphUnitSphereProd E
  let G : sphere (0 : E) 1 × Ioi (0 : ℝ) → ℝ≥0∞ :=
    fun z => f ((Φ.symm z : ({0}ᶜ : Set E)) : E)
  have hfsub : AEMeasurable
      (fun x : ({0}ᶜ : Set E) => f x)
      (μ.comap ((↑) : ({0}ᶜ : Set E) → E)) := by
    exact (aemeasurable_restrict_iff_comap_subtype
      isOpen_compl_singleton.measurableSet).mp hf.restrict
  have hG : AEMeasurable G
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    rw [← μ.measurePreserving_homeomorphUnitSphereProd.map_eq]
    apply Φ.measurableEmbedding.aemeasurable_map_iff.mpr
    have hfun : G ∘ Φ = fun x : ({0}ᶜ : Set E) => f x := by
      funext x
      simp only [G, Function.comp_apply]
      rw [Φ.symm_apply_apply]
    rw [hfun]
    exact hfsub
  rw [lintegral_polar_prod μ f]
  simpa only [G, Φ, homeomorphUnitSphereProd_symm_apply_coe] using
    (lintegral_prod G hG)

end MeasureTheory

end
