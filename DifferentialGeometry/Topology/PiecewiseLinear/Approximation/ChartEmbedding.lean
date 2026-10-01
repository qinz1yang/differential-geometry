import DifferentialGeometry.Topology.PiecewiseLinear.ChartLocalApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.Embedding

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart
    {M : Type*} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [HasGroupoid M (plGroupoid 3)] {C : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsPLBall 3 C)
    {h : EuclideanSpace ℝ (Fin 3) → M} (hcont : ContinuousOn h C) (hinj : InjOn h C)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ (plGroupoid 3).maximalAtlas M) (hmap : MapsTo h C e.source)
    {τ : EuclideanSpace ℝ (Fin 3) → ℝ} (hτ : ContinuousOn τ C) (hτpos : ∀ x ∈ C, 0 < τ x) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → M, IsPLHomeomorphInto 3 f C ∧ MapsTo f C e.source ∧
      ∀ x ∈ C, dist (f x) (h x) < τ x := by
  apply Moise341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart
    (fun C hC f hcont hinj ε hε =>
      exists_isPLHomeomorphOn_dist_lt_of_isPLBall_three C hC f hcont hinj ε hε)
    hC hcont hinj e he hmap hτ hτpos

end DifferentialGeometry.Topology.PiecewiseLinear
