import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactCanonicalCover
import DifferentialGeometry.Geometry.Neck.CompactCapClassification

noncomputable section

open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_compact_canonical_poincareStandard_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : ConnectedClosedOrientedManifold.{u} 3) {D : RealTimeInterval}
        (S : SolutionOn (I := I3) (M := M.Carrier) D) (C1 C2 t : ℝ)
        (W : ∀ x : M.Carrier, CanonicalWitness S eps C1 C2 x t),
        (∀ x, (W x).capTubeHasNeckChart eps) → isPoincareStandard M.Carrier := by
  obtain ⟨eta, heta, hclass⟩ := exists_compact_spatial_poincareStandard_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M D S C1 C2 t W hchart
  apply hclass eps heps M (S.base.metric t)
  intro x hx
  rcases (W x).spatial_cap_or_whole_of_not_spatial_neck (hchart x) hx with hp | hr | hc
  · exact Or.inl hp
  · obtain ⟨z, hr⟩ := hr
    exact Or.inr (Or.inl (isPositiveSpaceFormModel_of_roundComponent M hr.some))
  · exact Or.inr (Or.inr hc)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
