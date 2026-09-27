import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace MeasureTheory

theorem aestronglyMeasurable_apply_of_ae_continuous
    {α β γ : Type*} [MeasurableSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] [TopologicalSpace.PseudoMetrizableSpace γ] {μ : Measure α}
    {F : α → β → γ} (hF : ∀ y, AEStronglyMeasurable (fun a => F a y) μ)
    (hcont : ∀ᵐ a ∂μ, Continuous (F a)) {f : α → β} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun a => F a (f a)) μ := by
  classical
  cases isEmpty_or_nonempty α with
  | inl hα =>
    let := hα
    exact StronglyMeasurable.of_subsingleton_dom.aestronglyMeasurable
  | inr hα =>
    let : Nonempty β := ⟨f (Classical.choice hα)⟩
    have hs (s : SimpleFunc α β) : AEStronglyMeasurable (fun a => F a (s a)) μ := by
      induction s with
      | const y => exact hF y
      | @pcw s t A hA hs ht =>
        have hh := AEStronglyMeasurable.piecewise hA hs.restrict ht.restrict
        simpa only [SimpleFunc.coe_piecewise, Set.apply_piecewise] using hh
    apply aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (fun n => hs (hf.stronglyMeasurable_mk.approx n))
    filter_upwards [hf.ae_eq_mk, hcont] with a ha hca
    rw [ha]
    exact (hca.tendsto _).comp (hf.stronglyMeasurable_mk.tendsto_approx a)

end MeasureTheory
