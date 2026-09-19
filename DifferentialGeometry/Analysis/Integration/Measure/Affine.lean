import Mathlib.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ContinuousAffineEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

instance isAddHaarMeasure_map (e : E ≃ᴬ[𝕜] F) (μ : Measure E) [Measure.IsAddHaarMeasure μ] :
    Measure.IsAddHaarMeasure (μ.map e) := by
  let L : E ≃L[𝕜] F :=
    { toLinearEquiv := e.toAffineEquiv.linear
      continuous_toFun := e.toContinuousAffineMap.contLinear.continuous
      continuous_invFun := e.symm.toContinuousAffineMap.contLinear.continuous }
  have he : (e : E → F) = (fun y => y + e 0) ∘ L := by
    funext x
    exact congrFun e.toAffineEquiv.toAffineMap.decomp x
  have hc : Measurable (fun y : F => y + e 0) := (continuous_id.add continuous_const).measurable
  rw [he, ← Measure.map_map hc L.continuous.measurable]
  infer_instance

end ContinuousAffineEquiv

namespace MeasureTheory

theorem MemLp.comp_affineEquiv
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [ContinuousENorm G]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ᴬ[ℝ] F) {μ : Measure E} {ν : Measure F}
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    {Ω : Set F} {p : ℝ≥0∞} {f : F → G} (hf : MemLp f p (ν.restrict Ω)) :
    MemLp (f ∘ e) p (μ.restrict (e ⁻¹' Ω)) := by
  let : FiniteDimensional ℝ F := e.toAffineEquiv.linear.finiteDimensional
  have hm : MeasurePreserving e μ (μ.map e) := ⟨e.continuous.measurable, rfl⟩
  apply MemLp.comp_measurePreserving (ν := (μ.map e).restrict Ω) _
    (hm.restrict_preimage_emb e.toHomeomorph.isClosedEmbedding.measurableEmbedding Ω)
  rw [Measure.isAddLeftInvariant_eq_smul (μ.map e) ν, Measure.restrict_smul]
  exact hf.smul_measure ENNReal.coe_ne_top

end MeasureTheory

namespace DifferentialGeometry.Analysis

theorem integral_comp_affineEquiv
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ᴬ[ℝ] F) (μ : Measure E) (ν : Measure F)
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν] (Ω : Set F) (f : F → G) :
    (∫ x in e ⁻¹' Ω, f (e x) ∂μ) =
      Measure.addHaarScalarFactor (μ.map e) ν • ∫ y in Ω, f y ∂ν := by
  let : FiniteDimensional ℝ F := e.toAffineEquiv.linear.finiteDimensional
  have hm : MeasurePreserving e μ (μ.map e) := ⟨e.continuous.measurable, rfl⟩
  have ht := hm.restrict_preimage_emb e.toHomeomorph.isClosedEmbedding.measurableEmbedding Ω
  rw [ht.integral_comp e.toHomeomorph.isClosedEmbedding.measurableEmbedding f]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (μ.map e) ν]
  rw [Measure.restrict_smul, integral_smul_nnreal_measure]

end DifferentialGeometry.Analysis
