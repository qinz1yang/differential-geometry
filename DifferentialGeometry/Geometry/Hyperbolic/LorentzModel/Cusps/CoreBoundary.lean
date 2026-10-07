import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Core
import DifferentialGeometry.Topology.Ends.CylindricalCoreBoundary

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)

variable {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r : ℝ}
  (D : FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ))

theorem interior_cylindricalCore (R : D.centers → ℝ) :
    interior (Topology.cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ) R) =
      (⋃ ξ, D.horoballCylinderMap hΓ ξ '' {p | R ξ ≤ p.2.val})ᶜ := by
  let : Finite D.centers := D.finite_centers
  exact Topology.interior_cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ)
    (D.horoballCylinderMap_isClosedEmbedding hΓ) R

theorem frontier_cylindricalCore (R : D.centers → ℝ) (hR : ∀ ξ, 0 ≤ R ξ) :
    frontier (Topology.cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ) R) =
      ⋃ ξ, D.horoballCylinderMap hΓ ξ '' {p | p.2.val = R ξ} := by
  let : Finite D.centers := D.finite_centers
  exact Topology.frontier_cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ)
    (D.horoballCylinderMap_isClosedEmbedding hΓ) (D.isOpen_image_horoballCylinderMap_pos hΓ)
    (D.pairwise_disjoint_range_horoballCylinderMap hΓ) R hR

theorem closure_interior_cylindricalCore (R : D.centers → ℝ) (hR : ∀ ξ, 0 < R ξ) :
    closure (interior (Topology.cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ) R)) =
      Topology.cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ) R := by
  let : Finite D.centers := D.finite_centers
  exact Topology.closure_interior_cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ)
    (D.horoballCylinderMap_isClosedEmbedding hΓ) (D.isOpen_image_horoballCylinderMap_pos hΓ)
    (D.pairwise_disjoint_range_horoballCylinderMap hΓ) R hR

theorem isConnected_interior_cylindricalCore (R : D.centers → ℝ) (hR : ∀ ξ, 0 < R ξ) :
    IsConnected (interior (Topology.cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ) R)) := by
  let : PathConnectedSpace (HUpper n) := HyperbolicGeodesic.pathConnectedSpace hn
  let : Finite D.centers := D.finite_centers
  exact Topology.isConnected_interior_cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ)
    (D.horoballCylinderMap_isClosedEmbedding hΓ) (D.isOpen_image_horoballCylinderMap_pos hΓ)
    (D.pairwise_disjoint_range_horoballCylinderMap hΓ) R hR

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
