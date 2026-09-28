import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Integration
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section

open Set Function Filter MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem lintegral_paramDensity_mul_le_lintegral_image
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) (hinj : InjOn f K) (φ : M → ℝ≥0∞) :
    ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x) * φ (f x) ∂(modelHaar (E := E)) ≤
      ∫⁻ y in f '' K, φ y ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  let J : E → ℝ≥0∞ := fun x => ENNReal.ofReal (paramDensity (I := I) g f x)
  let ν : Measure E := ((modelHaar (E := E)).restrict K).withDensity J
  have hJ : AEMeasurable J ((modelHaar (E := E)).restrict K) :=
    (((continuousOn_paramDensity (I := I) g hU hf).mono hKU).aemeasurable hK).ennreal_ofReal
  have hfw : AEMeasurable f ν :=
    ((hf.continuousOn.mono hKU).aemeasurable (μ := modelHaar (E := E)) hK).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have he : MeasurableEmbedding (K.domRestrict f) :=
    (hf.continuousOn.mono hKU).measurableEmbedding hK hinj
  have hsub : MeasurableEmbedding (Subtype.val : K → E) := MeasurableEmbedding.subtype_coe hK
  let ρ : Measure K := Measure.comap (Subtype.val : K → E) ν
  have hνK : ν.restrict K = ν := by
    change (((modelHaar (E := E)).restrict K).withDensity J).restrict K = _
    rw [restrict_withDensity hK, Measure.restrict_restrict hK, inter_self]
  have hmapcomap : Measure.map (Subtype.val : K → E) ρ = ν := by
    rw [hsub.map_comap, Subtype.range_coe, hνK]
  have hmap : Measure.map (K.domRestrict f) ρ = Measure.map f ν := by
    have h1 : AEMeasurable f (Measure.map (Subtype.val : K → E) ρ) := by
      rw [hmapcomap]; exact hfw
    rw [show K.domRestrict f = f ∘ Subtype.val from rfl,
      ← AEMeasurable.map_map_of_aemeasurable h1 hsub.measurable.aemeasurable, hmapcomap]
  refine le_of_eq ?_
  calc
    ∫⁻ x in K, J x * φ (f x) ∂(modelHaar (E := E)) = ∫⁻ x, φ (f x) ∂ν :=
      (lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hJ
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _).symm
    _ = ∫⁻ x, φ (f x) ∂(Measure.map (Subtype.val : K → E) ρ) := by
      rw [hmapcomap]
    _ = ∫⁻ x : K, φ (K.domRestrict f x) ∂ρ :=
      hsub.lintegral_map _
    _ = ∫⁻ y, φ y ∂(Measure.map (K.domRestrict f) ρ) :=
      (he.lintegral_map _).symm
    _ = ∫⁻ y in f '' K, φ y ∂riemannianVolumeMeasure (I := I) (M := M) g := by
      rw [hmap, map_withDensity_paramDensity (I := I) g hU hK hKU hf hinj]

end DifferentialGeometry.Integral.Measure
