import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open Metric Set
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [Nontrivial E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

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

section Signed

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem integrable_ioiPow_iff (d : ℕ) (F : ℝ → G) :
    Integrable (fun r : Ioi (0 : ℝ) => F r.1) (Measure.volumeIoiPow d) ↔
      IntegrableOn (fun r : ℝ => r ^ d • F r) (Ioi (0 : ℝ)) := by
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioi, Function.comp_def,
    Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul',
    integrable_congr]
  · refine .of_forall ?_
    rintro ⟨r, hr : 0 < r⟩
    simp (disch := positivity) [ENNReal.toReal_ofReal]
  · measurability
  · simp

theorem integral_ioiPow (d : ℕ) (F : ℝ → G) :
    (∫ r : Ioi (0 : ℝ), F r.1 ∂Measure.volumeIoiPow d) =
      ∫ r in Ioi (0 : ℝ), r ^ d • F r := by
  rw [Measure.volumeIoiPow,
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_subtype_coe.pow_const d).ennreal_ofReal)
      (by filter_upwards with r; exact ENNReal.ofReal_lt_top)]
  calc
    (∫ r : Ioi (0 : ℝ),
        (ENNReal.ofReal (r.1 ^ d)).toReal • F r.1
          ∂Measure.comap Subtype.val volume) =
        ∫ r : Ioi (0 : ℝ), r.1 ^ d • F r.1
          ∂Measure.comap Subtype.val volume := by
      apply integral_congr_ae
      filter_upwards with r
      rw [ENNReal.toReal_ofReal (pow_nonneg r.2.le d)]
    _ = ∫ r in Ioi (0 : ℝ), r ^ d • F r :=
      integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r ^ d • F r)

theorem integral_ioiPow_set (d : ℕ) (S : Set ℝ) (hS : MeasurableSet S)
    (hS0 : S ⊆ Ioi (0 : ℝ)) (F : ℝ → G) :
    (∫ r : Ioi (0 : ℝ), S.indicator F r.1 ∂Measure.volumeIoiPow d) =
      ∫ r in S, r ^ d • F r := by
  rw [integral_ioiPow d (S.indicator F)]
  calc
    (∫ r in Ioi (0 : ℝ), r ^ d • S.indicator F r) =
        ∫ r in S, r ^ d • S.indicator F r := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hS0
      intro r hr
      rw [indicator_of_notMem hr.2, smul_zero]
    _ = ∫ r in S, r ^ d • F r := by
      apply setIntegral_congr_fun hS
      intro r hr
      change r ^ d • S.indicator F r = r ^ d • F r
      rw [indicator_of_mem hr]

theorem integral_polar_prod (f : E → G) :
    ∫ x, f x ∂μ =
      ∫ z : sphere (0 : E) 1 × Ioi (0 : ℝ),
        f (z.2.1 • z.1.1)
          ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  let Φ := homeomorphUnitSphereProd E
  calc
    ∫ x, f x ∂μ = ∫ x in ({0}ᶜ : Set E), f x ∂μ := by
      exact congrArg (fun ν : Measure E => ∫ x, f x ∂ν)
        (restrict_compl_singleton (μ := μ) 0).symm
    _ = ∫ x : ({0}ᶜ : Set E),
          f x ∂(μ.comap ((↑) : ({0}ᶜ : Set E) → E)) := by
      rw [integral_subtype_comap isOpen_compl_singleton.measurableSet]
    _ = ∫ z : sphere (0 : E) 1 × Ioi (0 : ℝ),
          f ((Φ.symm z : ({0}ᶜ : Set E)) : E)
            ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      simpa only [Φ, Homeomorph.symm_apply_apply] using
        (μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
          Φ.measurableEmbedding
          (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) =>
            f ((Φ.symm z : ({0}ᶜ : Set E)) : E)))
    _ = ∫ z : sphere (0 : E) 1 × Ioi (0 : ℝ),
          f (z.2.1 • z.1.1)
            ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      congr 1

omit [NormedSpace ℝ G] in
theorem integrable_polar_prod (f : E → G) (hf : Integrable f μ) :
    Integrable
      (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) => f (z.2.1 • z.1.1))
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  let Φ := homeomorphUnitSphereProd E
  let F : sphere (0 : E) 1 × Ioi (0 : ℝ) → G :=
    fun z => f ((Φ.symm z : ({0}ᶜ : Set E)) : E)
  have hfres : Integrable f (μ.restrict ({0}ᶜ : Set E)) := by
    simpa only [restrict_compl_singleton] using hf
  have hfsub : Integrable
      (fun x : ({0}ᶜ : Set E) => f x)
      (μ.comap ((↑) : ({0}ᶜ : Set E) → E)) := by
    change Integrable
      (f ∘ ((↑) : ({0}ᶜ : Set E) → E))
      (μ.comap ((↑) : ({0}ᶜ : Set E) → E))
    rw [← (MeasurableEmbedding.subtype_coe
      isOpen_compl_singleton.measurableSet).integrable_map_iff,
      map_comap_subtype_coe isOpen_compl_singleton.measurableSet]
    exact hfres
  have hF : Integrable F
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    apply (μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
      Φ.measurableEmbedding).mp
    apply hfsub.congr
    filter_upwards with x
    simp only [F, Φ, Function.comp_apply, Homeomorph.symm_apply_apply]
  simpa only [F, Φ, homeomorphUnitSphereProd_symm_apply_coe] using hF

theorem integral_polar (f : E → G) (hf : Integrable f μ) :
    ∫ x, f x ∂μ =
      ∫ u : sphere (0 : E) 1,
        ∫ r : Ioi (0 : ℝ), f (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) ∂μ.toSphere := by
  rw [integral_polar_prod μ f]
  exact MeasureTheory.integral_prod _ (integrable_polar_prod μ f hf)

theorem setIntegral_polar (s : Set E) (hs : MeasurableSet s)
    (f : E → G) (hf : IntegrableOn f s μ) :
    (∫ x in s, f x ∂μ) =
      ∫ u : sphere (0 : E) 1,
        ∫ r : Ioi (0 : ℝ), s.indicator f (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) ∂μ.toSphere := by
  rw [← integral_indicator hs]
  exact integral_polar μ (s.indicator f) (hf.integrable_indicator hs)

end Signed

theorem setLIntegral_polar (s : Set E) (hs : MeasurableSet s)
    (f : E → ℝ≥0∞) (hf : AEMeasurable f μ) :
    (∫⁻ x in s, f x ∂μ) =
      ∫⁻ u : sphere (0 : E) 1,
        ∫⁻ r : Ioi (0 : ℝ), s.indicator f (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) ∂μ.toSphere := by
  rw [← lintegral_indicator hs]
  exact lintegral_polar μ (s.indicator f) (hf.indicator hs)

end MeasureTheory

end
