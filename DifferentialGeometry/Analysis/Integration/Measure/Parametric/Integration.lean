import DifferentialGeometry.Analysis.Integration.Measure.Parametric.AreaFormula
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open Set Filter Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem map_withDensity_paramDensity
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) (hinj : InjOn f K) :
    Measure.map f ((modelHaar (E := E)).restrict K |>.withDensity
      (fun x => ENNReal.ofReal (paramDensity (I := I) g f x))) =
      (riemannianVolumeMeasure (I := I) (M := M) g).restrict (f '' K) := by
  have hfm := (hf.continuousOn.mono hKU).aemeasurable (μ := modelHaar (E := E)) hK
  have hfw := hfm.mono' (withDensity_absolutelyContinuous
    ((modelHaar (E := E)).restrict K)
    (fun x => ENNReal.ofReal (paramDensity (I := I) g f x)))
  refine Measure.ext fun A hA => ?_
  have hpre : MeasurableSet (f ⁻¹' A ∩ K) := by
    have hm : Measurable (fun x : K => f x) :=
      (hf.continuousOn.mono hKU).domRestrict.measurable
    convert (MeasurableEmbedding.subtype_coe hK).measurableSet_image'
      (hA.preimage hm) using 1
    ext x
    simp only [mem_image, mem_preimage, mem_inter_iff, Subtype.exists, exists_and_right,
      exists_eq_right]
    constructor
    · rintro ⟨ha, hk⟩
      exact ⟨hk, ha⟩
    · rintro ⟨hk, ha⟩
      exact ⟨ha, hk⟩
  rw [Measure.map_apply_of_aemeasurable hfw hA, Measure.restrict_apply hA,
    withDensity_apply', Measure.restrict_restrict' hK]
  rw [show A ∩ f '' K = f '' (f ⁻¹' A ∩ K) from
    (Set.image_preimage_inter f K A).symm]
  exact (riemannianVolumeMeasure_image_eq (I := I) g hU hpre
    (inter_subset_right.trans hKU) hf (hinj.mono inter_subset_right)).symm

theorem lintegral_image_eq_lintegral_paramDensity_mul
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) (hinj : InjOn f K)
    (φ : M → ℝ≥0∞)
    (hφ : AEMeasurable φ ((riemannianVolumeMeasure (I := I) (M := M) g).restrict (f '' K))) :
    (∫⁻ y in f '' K, φ y ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x) * φ (f x)
        ∂(modelHaar (E := E)) := by
  have hfm := (hf.continuousOn.mono hKU).aemeasurable (μ := modelHaar (E := E)) hK
  have hfw := hfm.mono' (withDensity_absolutelyContinuous
    ((modelHaar (E := E)).restrict K)
    (fun x => ENNReal.ofReal (paramDensity (I := I) g f x)))
  have hJ := ((continuousOn_paramDensity g hU hf).mono hKU).aemeasurable
    (μ := modelHaar (E := E)) hK |>.ennreal_ofReal
  rw [← map_withDensity_paramDensity g hU hK hKU hf hinj] at hφ ⊢
  rw [lintegral_map' hφ hfw]
  exact lintegral_withDensity_eq_lintegral_mul₀' hJ (hφ.comp_aemeasurable hfw)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integrableOn_image_iff_paramDensity_smul
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) (hinj : InjOn f K)
    (φ : M → F)
    (hφ : AEStronglyMeasurable φ
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict (f '' K))) :
    IntegrableOn φ (f '' K) (riemannianVolumeMeasure (I := I) (M := M) g) ↔
      IntegrableOn (fun x => paramDensity (I := I) g f x • φ (f x))
        K (modelHaar (E := E)) := by
  have hfm := (hf.continuousOn.mono hKU).aemeasurable (μ := modelHaar (E := E)) hK
  have hfw := hfm.mono' (withDensity_absolutelyContinuous
    ((modelHaar (E := E)).restrict K)
    (fun x => ENNReal.ofReal (paramDensity (I := I) g f x)))
  have hJ := ((continuousOn_paramDensity g hU hf).mono hKU).aemeasurable
    (μ := modelHaar (E := E)) hK |>.ennreal_ofReal
  simp only [IntegrableOn]
  rw [← map_withDensity_paramDensity g hU hK hKU hf hinj] at hφ ⊢
  rw [integrable_map_measure hφ hfw,
    integrable_withDensity_iff_integrable_smul₀' hJ
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [Function.comp_apply, paramDensity,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

theorem integral_image_eq_integral_paramDensity_smul
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) (hinj : InjOn f K)
    (φ : M → F)
    (hφ : AEStronglyMeasurable φ
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict (f '' K))) :
    (∫ y in f '' K, φ y ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x in K, paramDensity (I := I) g f x • φ (f x)
        ∂(modelHaar (E := E)) := by
  have hfm := (hf.continuousOn.mono hKU).aemeasurable (μ := modelHaar (E := E)) hK
  have hfw := hfm.mono' (withDensity_absolutelyContinuous
    ((modelHaar (E := E)).restrict K)
    (fun x => ENNReal.ofReal (paramDensity (I := I) g f x)))
  have hJ := ((continuousOn_paramDensity g hU hf).mono hKU).aemeasurable
    (μ := modelHaar (E := E)) hK |>.ennreal_ofReal
  rw [← map_withDensity_paramDensity g hU hK hKU hf hinj] at hφ ⊢
  rw [integral_map hfw hφ, integral_withDensity_eq_integral_toReal_smul₀ hJ
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (show 0 ≤ paramDensity (I := I) g f x from
      Real.sqrt_nonneg _)]

end DifferentialGeometry.Integral.Measure
