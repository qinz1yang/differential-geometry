import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottConvergence
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottIsometryTransport

set_option autoImplicit false

open Filter

namespace GC.MetricGeometry.PointedGHConverges

theorem comap_source_isometry {X Y : ℕ → Type*} {Z : Type*}
    [∀ n, MetricSpace (X n)] [∀ n, MetricSpace (Y n)] [MetricSpace Z]
    {p : ∀ n, X n} {q : ∀ n, Y n} {z : Z}
    (h : PointedGHConverges p z) (e : ∀ n, Y n ≃ᵢ X n)
    (he : ∀ n, e n (q n) = p n) : PointedGHConverges q z := by
  let := h.complete_space
  obtain ⟨δ, _, hδ, hf⟩ := h.exists_kleinerLott_sequence
  apply of_kleinerLott_sequence hδ
  filter_upwards [hf] with n hn
  obtain ⟨f⟩ := hn
  exact ⟨f.comapSourceIsometryAt (e n) (q n) (he n)⟩

end GC.MetricGeometry.PointedGHConverges
