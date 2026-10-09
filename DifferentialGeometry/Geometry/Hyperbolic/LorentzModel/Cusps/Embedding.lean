import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Cylinder
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ThinRegionClosure

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Busemann (horoball)

variable {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r : ℝ}
  (D : FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ : D.centers)

include hΓ in
theorem horoballQuotientInclusion_isClosedEmbedding :
    Topology.IsClosedEmbedding (D.horoballQuotientInclusion ξ) := by
  apply OrbifoldThinRegions.isClosedEmbedding_stabilizerQuotientInclusion hn Γ {ξ.val}
    (horoball ξ.val (D.level ξ)) hΓ
    (isClosed_le (HorosphereProjection.continuous_busemann ξ.val) continuous_const)
    ((D.horoball_inside ξ).trans interior_subset)
  intro γ p hp
  let δ : Γ := ⟨γ, γ.property.1⟩
  have hfix := (CuspCrossSections.mem_endStabilizer_singleton hn Γ ξ.val γ).mp γ.property
  rw [← (D.precisely_invariant hΓ ξ δ).1 hfix.2]
  exact ⟨p, hp, rfl⟩

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
