import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.Lindelof

section

set_option autoImplicit false

open Set MeasureTheory Metric

namespace MeasureTheory

theorem ae_restrict_of_ae_restrict_closedBall_subset
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    {μ : Measure X} {Ω : Set X} (hΩ : IsOpen Ω) {p : X → Prop}
    (hp : ∀ c : X, ∀ r : ℝ, closedBall c r ⊆ Ω → ∀ᵐ x ∂μ.restrict (ball c r), p x) :
    ∀ᵐ x ∂μ.restrict Ω, p x := by
  classical
  have hr : ∀ c : Ω, ∃ r > 0, closedBall (c : X) r ⊆ Ω := fun c =>
    Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds c.property)
  choose r hrpos hrsub using hr
  let U : Ω → Set X := fun c => ball c (r c)
  have hcover : Ω ⊆ ⋃ c, U c := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hrpos _)⟩
  obtain ⟨s, hs, hsc⟩ := (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover
    U (fun _ => isOpen_ball) hcover
  have hu : ∀ᵐ x ∂μ.restrict (⋃ c ∈ s, U c), p x :=
    (ae_restrict_biUnion_iff U hs p).mpr fun c _ => hp c (r c) (hrsub c)
  exact ae_restrict_of_ae_restrict_of_subset hsc hu

end MeasureTheory

end
