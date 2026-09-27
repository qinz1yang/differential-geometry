import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Set
open scoped ENNReal

variable {α E : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [OpensMeasurableSpace α] [NormedAddCommGroup E]
  {f : α → E} {s t : Set α} {μ : Measure α}

theorem ContinuousOn.memLp_top_of_subset_isCompact
    (hf : ContinuousOn f s) (hs : IsCompact s) (ht : MeasurableSet t) (hts : t ⊆ s) :
    MemLp f ∞ (μ.restrict t) := by
  obtain ⟨C, hC⟩ := hs.bddAbove_image hf.norm
  apply memLp_top_of_bound (hf.aestronglyMeasurable_of_subset_isCompact hs ht hts) C
  filter_upwards [ae_restrict_mem ht] with x hx
  exact hC (mem_image_of_mem (fun y => ‖f y‖) (hts hx))

theorem ContinuousOn.memLp_top_of_isCompact
    (hf : ContinuousOn f s) (hs : IsCompact s) (hsm : MeasurableSet s) :
    MemLp f ∞ (μ.restrict s) :=
  hf.memLp_top_of_subset_isCompact hs hsm Subset.rfl
