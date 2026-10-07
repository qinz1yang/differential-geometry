import DifferentialGeometry.Analysis.Integration.Measure.CylindricalEnd
import DifferentialGeometry.Topology.Ends.CylindricalCore
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Compact

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

namespace DifferentialGeometry.Topology

theorem exists_pos_subset_cylindricalCore_measure_compl_lt
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {C : ι → Type*} [∀ i, TopologicalSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (μ : Measure X) (hfinite : ∀ i, μ (range (e i)) ≠ ⊤)
    {B : Set X} (hB : IsCompact B) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ B ⊆ cylindricalCore e (fun _ => R) ∧
      μ ((cylindricalCore e (fun _ => R))ᶜ) < ε := by
  classical
  let _ := Fintype.ofFinite ι
  have hsum : Tendsto (fun R : ℝ => ∑ i, μ (e i '' {p | R ≤ p.2.val}))
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
      (fun i _ => (he i).tendsto_measure_image_cylinder_tail μ (hfinite i))
  have hheight (i : ι) : ∀ᶠ R : ℝ in atTop, ∀ p, e i p ∈ B → p.2.val ≤ R := by
    obtain ⟨b, hb⟩ := ((he i).isCompact_preimage hB).bddAbove_image
      (continuous_subtype_val.comp continuous_snd).continuousOn
    filter_upwards [eventually_ge_atTop b] with R hR
    intro p hp
    exact (hb ⟨p, hp, rfl⟩).trans hR
  obtain ⟨R, hR, hb, hm⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((eventually_all.mpr hheight).and (hsum.eventually (Iio_mem_nhds hε)))).exists
  refine ⟨R, hR, ?_, ?_⟩
  · intro x hx htail
    obtain ⟨i, p, hp, hpx⟩ := mem_iUnion.mp htail
    change R < p.2.val at hp
    exact hp.not_ge (hb i p (hpx.symm ▸ hx))
  · calc
      μ ((cylindricalCore e (fun _ => R))ᶜ) = μ (⋃ i, e i '' {p | R < p.2.val}) := by
        rw [cylindricalCore, compl_compl]
      _ ≤ ∑ i, μ (e i '' {p | R < p.2.val}) := measure_iUnion_fintype_le μ _
      _ ≤ ∑ i, μ (e i '' {p | R ≤ p.2.val}) :=
        Finset.sum_le_sum (fun i _ => measure_mono (image_mono (by
          intro p hp
          change R < p.2.val at hp
          change R ≤ p.2.val
          exact hp.le)))
      _ < ε := hm

end DifferentialGeometry.Topology
