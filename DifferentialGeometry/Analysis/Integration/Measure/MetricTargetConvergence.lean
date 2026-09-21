import DifferentialGeometry.Topology.MetricSpace.DistanceConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

section

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory
open scoped Topology

theorem DenseRange.exists_ae_tendsto_of_ae_tendsto_dist
    {A I X : Type*} [MeasurableSpace A] [Countable I]
    [PseudoMetricSpace X] [ProperSpace X]
    {a : I → X} (ha : DenseRange a) (μ : Measure A) (u : ℕ → A → X)
    (hu : ∀ i, ∀ᵐ z ∂μ, ∃ r : ℝ,
      Tendsto (fun n => dist (u n z) (a i)) atTop (𝓝 r)) :
    ∃ v : A → X, ∀ᵐ z ∂μ, Tendsto (fun n => u n z) atTop (𝓝 (v z)) := by
  classical
  let P : A → Prop := fun z => ∃ x : X,
    Tendsto (fun n => u n z) atTop (𝓝 x)
  have hP : ∀ᵐ z ∂μ, P z := by
    filter_upwards [ae_all_iff.mpr hu] with z hz
    exact ha.exists_tendsto_of_tendsto_dist hz
  let v : A → X := fun z => if h : P z then h.choose else u 0 z
  refine ⟨v, ?_⟩
  filter_upwards [hP] with z hz
  simpa only [v, dif_pos hz] using hz.choose_spec

theorem DenseRange.exists_aemeasurable_ae_tendsto_of_ae_tendsto_dist
    {A I X : Type*} [MeasurableSpace A] [Countable I]
    [PseudoMetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
    {a : I → X} (ha : DenseRange a) (μ : Measure A) (u : ℕ → A → X)
    (hum : ∀ n, AEMeasurable (u n) μ)
    (hu : ∀ i, ∀ᵐ z ∂μ, ∃ r : ℝ,
      Tendsto (fun n => dist (u n z) (a i)) atTop (𝓝 r)) :
    ∃ v : A → X, AEMeasurable v μ ∧
      ∀ᵐ z ∂μ, Tendsto (fun n => u n z) atTop (𝓝 (v z)) := by
  obtain ⟨v, hv⟩ := ha.exists_ae_tendsto_of_ae_tendsto_dist μ u hu
  exact ⟨v, aemeasurable_of_tendsto_metrizable_ae' hum hv, hv⟩

end

end
