import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Core
import DifferentialGeometry.Topology.Ends.CylindricalCoreHomotopy

noncomputable section

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)

variable {n : ℕ} {hn : 1 ≤ n} {Γ : Subgroup (PO n 1)} {r : ℝ}
  (D : FiniteCuspTruncation hn Γ r) (hΓ : IsDiscrete (SetLike.coe Γ))

local notation "πΓ" => Quotient.mk
  (@MulAction.orbitRel Γ (HUpper n) _ (EquivariantMap.subAction hn Γ))
local notation "QΓ" => @MulAction.orbitRel.Quotient Γ (HUpper n) _
  (EquivariantMap.subAction hn Γ)

theorem exists_deformation_retraction_cylindricalCore
    (R : D.centers → ℝ) (hR : ∀ ξ, 0 ≤ R ξ) :
    ∃ f : C(QΓ, QΓ),
      Set.range f = Topology.cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ) R ∧
      Nonempty ((ContinuousMap.id QΓ).HomotopyRel f
        (Topology.cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ) R)) := by
  let : Finite D.centers := D.finite_centers
  exact Topology.exists_deformation_retraction_cylindricalCore
    (fun ξ ↦ D.horoballCylinderMap hΓ ξ) (D.horoballCylinderMap_isClosedEmbedding hΓ)
    (D.isOpen_image_horoballCylinderMap_pos hΓ)
    (D.pairwise_disjoint_range_horoballCylinderMap hΓ) R hR

theorem exists_homotopyEquiv_cylindricalCore
    (R : D.centers → ℝ) (hR : ∀ ξ, 0 ≤ R ξ) :
    ∃ F : ContinuousMap.HomotopyEquiv
        (Topology.cylindricalCore (fun ξ ↦ D.horoballCylinderMap hΓ ξ) R) QΓ,
      (∀ x, F x = x.val) ∧ (∀ x, F.symm x.val = x) := by
  let : Finite D.centers := D.finite_centers
  exact Topology.exists_homotopyEquiv_cylindricalCore
    (fun ξ ↦ D.horoballCylinderMap hΓ ξ) (D.horoballCylinderMap_isClosedEmbedding hΓ)
    (D.isOpen_image_horoballCylinderMap_pos hΓ)
    (D.pairwise_disjoint_range_horoballCylinderMap hΓ) R hR

include hΓ in
theorem exists_homotopyEquiv_quotient_truncatedSet :
    ∃ F : ContinuousMap.HomotopyEquiv (πΓ '' truncatedSet hn Γ D.centers D.level) QΓ,
      (∀ x, F x = x.val) ∧ (∀ x, F.symm x.val = x) := by
  rw [← D.cylindricalCore_zero hΓ]
  exact D.exists_homotopyEquiv_cylindricalCore hΓ (fun _ ↦ 0) (fun _ ↦ le_rfl)

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
