import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactCanonicalCover
import DifferentialGeometry.Geometry.Neck.CompactClassification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PositiveComponentSpaceForm

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
  obtain ⟨eta₀, hη₀, hclass⟩ := exists_compact_canonical_neck_cap_cover_alternatives_tolerance.{u}
  obtain ⟨eta₁, hη₁, hneck⟩ := exists_spatial_neck_standard_factor_tolerance.{u}
  refine ⟨min eta₀ eta₁, lt_min hη₀ hη₁, ?_⟩
  intro eps heps M D S C1 C2 t W hchart
  rcases hclass eps (heps.trans (min_le_left _ _)) M.Carrier S C1 C2 t W hchart with
    hn | hpos | hround | ⟨K, L, _, _, _, hcK, hcL, _, _, hinter, _, hcover⟩
  · exact isPoincareStandard_of_standard_factor M
      (hneck eps (heps.trans (min_le_right _ _)) M (S.base.metric t) hn)
  · exact isPoincareStandard_of_positiveComponent hpos.some
  · obtain ⟨x, hr⟩ := hround
    exact isPoincareStandard_of_standard_factor M
      (isStandardFactor_of_isPositiveSpaceFormModel sphericalSpaceFormCovering_holds
        (isPositiveSpaceFormModel_of_roundComponent M hr.some))
  · exact isPoincareStandard_of_capCore_cover hcK.some hcL.some hinter hcover

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
