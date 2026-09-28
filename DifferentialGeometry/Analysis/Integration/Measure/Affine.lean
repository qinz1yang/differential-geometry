import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace Measure

variable (ν : Measure E) [IsAddHaarMeasure ν]

theorem map_add_smul_addHaar (b : E) {r : ℝ} (hr : r ≠ 0) :
    ν.map (fun x => b + r • x) =
      ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| • ν := by
  change ν.map ((b + ·) ∘ (r • ·)) = _
  rw [← Measure.map_map (measurable_const_add b) (measurable_const_smul r),
    map_addHaar_smul ν hr, Measure.map_smul _ (measurable_const_add b).aemeasurable,
    map_add_left_eq_self ν b]

theorem map_add_smul_restrict_addHaar (b : E) {r : ℝ} (hr : r ≠ 0) (Ω : Set E) :
    (ν.restrict ((fun x => b + r • x) ⁻¹' Ω)).map (fun x => b + r • x) =
      ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| • ν.restrict Ω := by
  let e : E ≃ᵐ E :=
    (MeasurableEquiv.smul₀ r hr).trans (MeasurableEquiv.addLeft b)
  change (ν.restrict (e ⁻¹' Ω)).map e = _
  rw [← e.restrict_map, show ν.map e = _ from map_add_smul_addHaar ν b hr,
    Measure.restrict_smul]
  rfl

theorem map_prod_add_smul_restrict_addHaar
    {T : Type*} [MeasurableSpace T] (μ : Measure T) [SFinite μ]
    (b : E) {r : ℝ} (hr : r ≠ 0) (Ω : Set E) :
    (μ.prod (ν.restrict ((fun x => b + r • x) ⁻¹' Ω))).map
        (fun p => (p.1, b + r • p.2)) =
      ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| • μ.prod (ν.restrict Ω) := by
  change (μ.prod (ν.restrict ((fun x => b + r • x) ⁻¹' Ω))).map
    (Prod.map id (fun x => b + r • x)) = _
  have hS : Measurable (fun x : E => b + r • x) :=
    (measurable_const_add b).comp (measurable_const_smul r)
  rw [← Measure.map_prod_map _ _ measurable_id hS,
    Measure.map_id, map_add_smul_restrict_addHaar ν b hr Ω, Measure.prod_smul_right]

end Measure

variable {T F : Type*} [MeasurableSpace T] [NormedAddCommGroup F]
  (μ : Measure T) [SFinite μ] (ν : Measure E) [Measure.IsAddHaarMeasure ν]

theorem MemLp.comp_prod_add_smul
    {p : ℝ≥0∞} {f : T × E → F} {Ω : Set E}
    (hf : MemLp f p (μ.prod (ν.restrict Ω)))
    (b : E) {r : ℝ} (hr : r ≠ 0) :
    MemLp (fun x => f (x.1, b + r • x.2)) p
      (μ.prod (ν.restrict ((fun x => b + r • x) ⁻¹' Ω))) := by
  have hmap : MemLp f p
      ((μ.prod (ν.restrict ((fun x => b + r • x) ⁻¹' Ω))).map
        (fun x => (x.1, b + r • x.2))) := by
    rw [Measure.map_prod_add_smul_restrict_addHaar ν μ b hr Ω]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hmap.comp_of_map
    ((measurable_fst.prodMk ((measurable_const_add b).comp
      ((measurable_const_smul r).comp measurable_snd))).aemeasurable)

theorem exists_lp_comp_prod_add_smul
    {p : ℝ≥0∞} {Ω : Set E} (f : Lp F p (μ.prod (ν.restrict Ω)))
    (b : E) {r : ℝ} (hr : r ≠ 0) :
    ∃ u : Lp F p (μ.prod (ν.restrict ((fun x => b + r • x) ⁻¹' Ω))),
      u =ᵐ[μ.prod (ν.restrict ((fun x => b + r • x) ⁻¹' Ω))]
        fun x => f (x.1, b + r • x.2) := by
  let h := (Lp.memLp f).comp_prod_add_smul μ ν b hr
  exact ⟨h.toLp _, h.coeFn_toLp⟩

theorem quasiMeasurePreserving_prod_add_smul_restrict
    (b : E) {r : ℝ} (hr : r ≠ 0) (Ω : Set E) :
    Measure.QuasiMeasurePreserving (fun x : T × E => (x.1, b + r • x.2))
      (μ.prod (ν.restrict ((fun x => b + r • x) ⁻¹' Ω)))
      (μ.prod (ν.restrict Ω)) := by
  refine ⟨measurable_fst.prodMk ((measurable_const_add b).comp
    ((measurable_const_smul r).comp measurable_snd)), ?_⟩
  rw [Measure.map_prod_add_smul_restrict_addHaar ν μ b hr Ω]
  exact Measure.smul_absolutelyContinuous


theorem integral_prod_comp_add_smul [NormedSpace ℝ F]
    (f : T × E → F) (b : E) {r : ℝ} (hr : r ≠ 0) (Ω : Set E) :
    (∫ x, f (x.1, b + r • x.2)
      ∂μ.prod (ν.restrict ((fun y => b + r • y) ⁻¹' Ω))) =
      |(r ^ Module.finrank ℝ E)⁻¹| • ∫ x, f x ∂μ.prod (ν.restrict Ω) := by
  let e : T × E ≃ᵐ T × E := (MeasurableEquiv.refl T).prodCongr
    ((MeasurableEquiv.smul₀ r hr).trans (MeasurableEquiv.addLeft b))
  have hmap :
      (μ.prod (ν.restrict ((fun y => b + r • y) ⁻¹' Ω))).map e =
        ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| • μ.prod (ν.restrict Ω) :=
    Measure.map_prod_add_smul_restrict_addHaar ν μ b hr Ω
  change (∫ x, f (e x)
    ∂μ.prod (ν.restrict ((fun y => b + r • y) ⁻¹' Ω))) = _
  rw [← integral_map_equiv e, hmap, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _)]

theorem integral_prod_abs_pow_smul_comp_add_smul [NormedSpace ℝ F]
    (f : T × E → F) (b : E) {r : ℝ} (hr : r ≠ 0) (Ω : Set E) :
    (∫ x, |r ^ Module.finrank ℝ E| • f (x.1, b + r • x.2)
      ∂μ.prod (ν.restrict ((fun y => b + r • y) ⁻¹' Ω))) =
      ∫ x, f x ∂μ.prod (ν.restrict Ω) := by
  rw [integral_smul, integral_prod_comp_add_smul μ ν f b hr Ω, smul_smul,
    abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr (pow_ne_zero _ hr)), one_smul]

end MeasureTheory

end

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F]

theorem MemLp.comp_add_smul
    {ν : Measure E} [Measure.IsAddHaarMeasure ν]
    {p : ℝ≥0∞} {f : E → F} {Ω : Set E}
    (hf : MemLp f p (ν.restrict Ω)) (b : E) {r : ℝ} (hr : r ≠ 0) :
    MemLp (fun x => f (b + r • x)) p
      (ν.restrict ((fun x => b + r • x) ⁻¹' Ω)) := by
  have hmap : MemLp f p
      ((ν.restrict ((fun x => b + r • x) ⁻¹' Ω)).map (fun x => b + r • x)) := by
    rw [Measure.map_add_smul_restrict_addHaar ν b hr Ω]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hmap.comp_of_map
    (((measurable_const_add b).comp (measurable_const_smul r)).aemeasurable)

theorem quasiMeasurePreserving_add_smul_restrict
    (ν : Measure E) [Measure.IsAddHaarMeasure ν]
    (b : E) {r : ℝ} (hr : r ≠ 0) (Ω : Set E) :
    Measure.QuasiMeasurePreserving (fun x : E => b + r • x)
      (ν.restrict ((fun x => b + r • x) ⁻¹' Ω)) (ν.restrict Ω) := by
  refine ⟨(measurable_const_add b).comp (measurable_const_smul r), ?_⟩
  rw [Measure.map_add_smul_restrict_addHaar ν b hr Ω]
  exact Measure.smul_absolutelyContinuous

end MeasureTheory

end

end

section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

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

theorem LocallyIntegrableOn.comp_affineEquiv
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [ContinuousENorm G]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ᴬ[ℝ] F) {μ : Measure E} {ν : Measure F}
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    {Ω : Set F} {f : F → G} (hf : LocallyIntegrableOn f Ω ν) :
    LocallyIntegrableOn (f ∘ e) (e ⁻¹' Ω) μ := by
  intro x hx
  obtain ⟨W, hW, hfW⟩ := hf (e x) hx
  refine ⟨e ⁻¹' W, ?_, ?_⟩
  · exact (e.continuous.continuousAt.continuousWithinAt.tendsto_nhdsWithin
      (fun y (hy : y ∈ e ⁻¹' Ω) => hy)) hW
  · exact memLp_one_iff_integrable.mp
      ((memLp_one_iff_integrable.mpr hfW).comp_affineEquiv e)


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

end

end
