import DifferentialGeometry.Analysis.ODE.AreaUpperBarrier
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.SmoothTorusReconstruction

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Analysis Set
open scoped Manifold ContDiff

namespace GC.LongTime

theorem incompressible_of_shifted_area_barriers
    {C : GC.Endpoint.CompactCarrier} {G : GC.Endpoint.TorusGluing C}
    (S : GC.Endpoint.SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold 3} (r : S.Reconstruction P)
    (harea : ∀ i : Fin G.count, ∀ x : GC.Endpoint.Torus,
      ¬ Function.Injective (FundamentalGroup.map (S.torusInPrime r i) x) →
      ∃ (T c : ℝ) (A : ℝ → ℝ), 0 ≤ T ∧ 0 < c ∧
        ContinuousOn A (Ici T) ∧ (∀ t ∈ Ici T, 0 ≤ A t) ∧
        (∀ t ∈ Ici T, hasLocalSmoothUpperBarrier A (Ici T) t
          (3 * A t / (4 * (t + c)) - Real.pi))) :
    S.Incompressible r := by
  intro i x
  by_contra h
  obtain ⟨T, c, A, hT, hc, hcont, hn, hb⟩ := harea i x h
  exact not_nonnegative_area_upper_barriers_pi_shift A T c (by linarith) hcont hn hb

end GC.LongTime
