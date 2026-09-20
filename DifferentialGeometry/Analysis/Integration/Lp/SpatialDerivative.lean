import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic


noncomputable section

namespace DifferentialGeometry.Analysis.Calculus

open Filter
open scoped NNReal Topology

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_fderiv_comp_inl_le_of_lipschitzOn
    (f : E × F → G) (z : E × F) {U : Set E} (hU : U ∈ 𝓝 z.1)
    {C : ℝ≥0} (hf : LipschitzOnWith C (fun x => f (x, z.2)) U) :
    ‖(fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E F)‖ ≤ C := by
  by_cases hdiff : DifferentiableAt ℝ f z
  · have he : fderiv ℝ (fun x => f (x, z.2)) z.1 =
        (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E F) :=
      (hdiff.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)).fderiv
    rw [← he]
    exact norm_fderiv_le_of_lipschitzOn ℝ hU hf
  · rw [fderiv_zero_of_not_differentiableAt hdiff]
    simpa only [ContinuousLinearMap.zero_comp, norm_zero] using C.coe_nonneg

end DifferentialGeometry.Analysis.Calculus

namespace MeasureTheory

open Set
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem memLp_fderiv_comp_inl_of_lipschitzOn
    (f : E × ℝ → ℝ) (μ : Measure (E × ℝ)) {U K : Set E} {J : Set ℝ}
    (hU : IsOpen U) (hK : MeasurableSet K) (hJ : MeasurableSet J) (hKU : K ⊆ U)
    [IsFiniteMeasure (μ.restrict (K ×ˢ J))] {C : ℝ≥0}
    (hf : ∀ t ∈ J, LipschitzOnWith C (fun x => f (x, t)) U) (p : ℝ≥0∞) :
    MemLp (fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)) p
      (μ.restrict (K ×ˢ J)) := by
  have hm : Measurable
      (fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)) :=
    (((ContinuousLinearMap.compL ℝ E (E × ℝ) ℝ).flip
      (ContinuousLinearMap.inl ℝ E ℝ)).continuous.measurable).comp
        (measurable_fderiv ℝ f)
  apply MemLp.of_bound hm.aestronglyMeasurable (C : ℝ)
  filter_upwards [ae_restrict_mem (hK.prod hJ)] with z hz
  exact DifferentialGeometry.Analysis.Calculus.norm_fderiv_comp_inl_le_of_lipschitzOn
    f z (hU.mem_nhds (hKU hz.1)) (hf z.2 hz.2)

end MeasureTheory
