import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspCollars
import DifferentialGeometry.Topology.Connected.FinitePartitions

/-!
Every nearly cuspidal boundary of the fixed annulus times circle carrier has two components.
The component labels are compared with the two actual connected closed end tori, independently
of the metric and of any particular choice of the boundary packet.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Seifert GC.Endpoint
open scoped Manifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem NearlyCuspidalBoundary.annulusComponentEquiv
    {g : SmoothRiemannianMetric annulusCircleCarrier.{u}.model annulusCircleCarrier.{u}.Carrier}
    {K : ℕ} {δ : ℝ} (B : NearlyCuspidalBoundary annulusCircleCarrier.{u} g K δ) :
    ∃ e : Fin B.count ≃ Fin 2, ∀ i, B.component i = doubleCuspBoundary.{u} (e i) := by
  exact DifferentialGeometry.Topology.finite_connected_partitions_equiv
    B.component doubleCuspBoundary B.connected doubleCuspBoundary_connected
    B.closed doubleCuspBoundary_closed B.disjoint doubleCuspBoundary_disjoint
    (B.covers.trans doubleCuspBoundary_cover.symm)

theorem NearlyCuspidalBoundary.count_eq_two_of_annulus
    {g : SmoothRiemannianMetric annulusCircleCarrier.{u}.model annulusCircleCarrier.{u}.Carrier}
    {K : ℕ} {δ : ℝ} (B : NearlyCuspidalBoundary annulusCircleCarrier.{u} g K δ) :
    B.count = 2 := by
  obtain ⟨e, hcomponents⟩ := B.annulusComponentEquiv
  have hcard := Fintype.card_congr e
  simpa only [Fintype.card_fin] using hcard

end DifferentialGeometry.Geometry.Collapse
