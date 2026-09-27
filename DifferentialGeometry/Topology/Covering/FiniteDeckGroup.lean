import DifferentialGeometry.Topology.Covering.DeckGroup

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

private theorem finite_coveringDeckGroup_of_nonempty
    [CompactSpace E] [PreconnectedSpace E] [Nonempty E] [T1Space X]
    {p : E → X} (hp : IsCoveringMap p) : Finite (coveringDeckGroup p) := by
  let x : E := Classical.ofNonempty
  let _ : DiscreteTopology (p ⁻¹' {p x}) := (hp (p x)).discreteTopology_fiber
  let _ : CompactSpace (p ⁻¹' {p x}) :=
    isCompact_iff_compactSpace.mp (isClosed_singleton.preimage hp.continuous).isCompact
  let _ : Finite (p ⁻¹' {p x}) := finite_of_compact_of_discrete
  let f : coveringDeckGroup p → p ⁻¹' {p x} := fun gamma =>
    ⟨gamma • x, coveringDeckGroup_map gamma x⟩
  apply Finite.of_injective f
  intro gamma delta h
  have hpoint : gamma • x = delta • x := congrArg Subtype.val h
  apply Subtype.ext
  apply Equiv.ext
  have heq := hp.eq_of_comp_eq gamma.property.1 delta.property.1
    (by
      funext y
      exact (coveringDeckGroup_map gamma y).trans (coveringDeckGroup_map delta y).symm)
    x hpoint
  exact congrFun heq

theorem finite_coveringDeckGroup_of_compactSpace
    [CompactSpace E] [PreconnectedSpace E] [T1Space X]
    {p : E → X} (hp : IsCoveringMap p) : Finite (coveringDeckGroup p) := by
  cases isEmpty_or_nonempty E with
  | inl h =>
    let _ := h
    infer_instance
  | inr h =>
    let _ := h
    exact finite_coveringDeckGroup_of_nonempty hp

end DifferentialGeometry
