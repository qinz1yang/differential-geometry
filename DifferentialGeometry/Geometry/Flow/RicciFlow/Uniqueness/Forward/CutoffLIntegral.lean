import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.CutoffEnergy
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Filter MeasureTheory Manifold Set Topology
open scoped Manifold Topology ContDiff ENNReal

open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

theorem tendsto_cutoff_lintegral_of_nonnegative
    (K : CompactExhaustion M) {μ : Measure M} {f : M → ℝ}
    (hf : Measurable f) (hfnn : ∀ x, 0 ≤ f x) :
    Tendsto
      (fun n => ∫⁻ x,
        ENNReal.ofReal
          (compactExhaustionCutoff (I := I) (M := M) K n x * f x) ∂μ)
      atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂μ)) := by
  have hcover : MeasureTheory.AECover μ atTop (fun n => K n) := by
    refine ⟨?_, fun n => (K.isCompact n).measurableSet⟩
    filter_upwards [Filter.Eventually.of_forall fun x => K.exists_mem x] with x hx
    obtain ⟨n₀, hn₀⟩ := hx
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact K.subset hn hn₀
  have hf_ennreal : AEMeasurable (fun x => ENNReal.ofReal (f x)) μ :=
    (hf.ennreal_ofReal).aemeasurable
  have hlower : ∀ n,
      (∫⁻ x in K n, ENNReal.ofReal (f x) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal
          (compactExhaustionCutoff (I := I) (M := M) K n x * f x) ∂μ := by
    intro n
    rw [← MeasureTheory.lintegral_indicator (K.isCompact n).measurableSet]
    apply MeasureTheory.lintegral_mono
    intro x
    by_cases hx : x ∈ K n
    · rw [Set.indicator_of_mem hx]
      have hχ := (compactExhaustionCutoff_spec (I := I) (M := M) K n).2.2.1 x hx
      simp [hχ]
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  have hupper : ∀ n,
      (∫⁻ x, ENNReal.ofReal
          (compactExhaustionCutoff (I := I) (M := M) K n x * f x) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
    intro n
    apply MeasureTheory.lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    have hχ := (compactExhaustionCutoff_spec (I := I) (M := M) K n).2.2.2.2
      (show compactExhaustionCutoff (I := I) (M := M) K n x ∈
        Set.range (compactExhaustionCutoff (I := I) (M := M) K n) from ⟨x, rfl⟩)
    exact mul_le_of_le_one_left (hfnn x) hχ.2
  have hlower_tendsto :
      Tendsto (fun n => ∫⁻ x in K n, ENNReal.ofReal (f x) ∂μ) atTop
        (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂μ)) :=
    hcover.lintegral_tendsto_of_nat hf_ennreal
  exact hlower_tendsto.squeeze'
    tendsto_const_nhds
    (Filter.Eventually.of_forall hlower)
    (Filter.Eventually.of_forall hupper)

end DifferentialGeometry.PDE.RicciFlow

end
