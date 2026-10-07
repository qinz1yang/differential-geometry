import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Topology.IsClosedEmbedding

variable {C X : Type*} [TopologicalSpace C] [TopologicalSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

theorem tendsto_measure_image_cylinder_tail
    {e : C × Ici (0 : ℝ) → X} (he : IsClosedEmbedding e)
    (μ : Measure X) (hfinite : μ (range e) ≠ ∞) :
    Tendsto (fun R : ℝ => μ (e '' {p | R ≤ p.2.val})) atTop (𝓝 0) := by
  let S (R : ℝ) : Set X := e '' {p | R ≤ p.2.val}
  have hmeas (R : ℝ) : MeasurableSet (S R) :=
    (he.isClosedMap _ (isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd))).measurableSet
  have hanti : Antitone S := by
    intro R T hRT
    exact image_mono (fun p hp => hRT.trans hp)
  have hinter : (⋂ R : ℝ, S R) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨p, hp, hpx⟩ := mem_iInter.mp hx 0
    obtain ⟨q, hq, hqx⟩ := mem_iInter.mp hx (p.2.val + 1)
    have hqp : q = p := he.injective (hqx.trans hpx.symm)
    rw [hqp] at hq
    change p.2.val + 1 ≤ p.2.val at hq
    linarith
  have hfin : μ (S 0) ≠ ∞ :=
    ne_top_of_le_ne_top hfinite (measure_mono (image_subset_range _ _))
  have ht := tendsto_measure_iInter_atTop (fun R => (hmeas R).nullMeasurableSet) hanti ⟨0, hfin⟩
  simpa only [hinter, measure_empty, Function.comp_def, S] using ht

end Topology.IsClosedEmbedding
