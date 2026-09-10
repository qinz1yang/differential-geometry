import DifferentialGeometry.Topology.PlanarJordan.ClosedInterior
import DifferentialGeometry.Topology.PlanarJordan.PeriodicOrbit

open Set Metric

namespace Poincare.Topology.PlanarJordan

theorem exists_invariant_disk_of_periodic_orbit
    (φ : _root_.Flow ℝ ℂ) {x : ℂ}
    (hnon : ∃ s : ℝ, φ s x ≠ x) (hreturn : ∃ t > 0, φ t x = x) :
    ∃ U : Set ℂ, IsOpen U ∧ IsConnected U ∧ frontier U = φ.orbit x ∧
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ closure U) ∧ IsInvariant φ (closure U) := by
  obtain ⟨U, _, hU, _, hconn, _, _, _, hfrontier, _, hcompact, _, hinv, _⟩ :=
    exists_invariant_regions_of_periodic_orbit φ hnon hreturn
  obtain ⟨γ, hγ, hclose, hinj, himage⟩ :=
    Poincare.Topology.Flow.exists_simple_closed_curve_of_periodic_orbit φ hnon hreturn
  refine ⟨U, hU, hconn, hfrontier,
    nonempty_homeomorph_closedBall_closure hU hconn hcompact hγ.continuousOn
      hclose hinj (hfrontier.trans himage.symm), ?_⟩
  intro t
  exact (hinv t).closure (φ.continuous continuous_const continuous_id)

end Poincare.Topology.PlanarJordan
