import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

variable (m : ℕ)

private abbrev inside := intrinsicInterior (𝓡∂ (m + 1)) ∞ (by simp)
  (M := ClosedCell (m + 1))
private abbrev openBall :=
  (⟨Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, Metric.isOpen_ball⟩ :
    TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1))))

theorem closedCell_interior_eq_ball :
    (𝓡∂ (m + 1)).interior (ClosedCell (m + 1)) = {x | ‖x.val‖ < 1} := by
  rw [← ModelWithCorners.compl_boundary, closedCell_boundary_eq_sphere m]
  ext x
  change ¬‖x.val‖ = 1 ↔ ‖x.val‖ < 1
  exact (lt_iff_le_and_ne.trans (and_iff_right x.property)).symm

private def interiorToBall (x : inside m) : openBall m :=
  ⟨x.val.val, mem_ball_zero_iff.mpr (by
    have h : x.val ∈ (𝓡∂ (m + 1)).interior (ClosedCell (m + 1)) := x.property
    rwa [closedCell_interior_eq_ball] at h)⟩

private def ballToInterior (x : openBall m) : inside m :=
  ⟨⟨x.val, (mem_ball_zero_iff.mp x.property).le⟩, by
    change (⟨x.val, (mem_ball_zero_iff.mp x.property).le⟩ : ClosedCell (m + 1)) ∈
      (𝓡∂ (m + 1)).interior (ClosedCell (m + 1))
    rw [closedCell_interior_eq_ball]
    exact mem_ball_zero_iff.mp x.property⟩

def closedCellInteriorDiffeomorph :
    (intrinsicInterior (𝓡∂ (m + 1)) ∞ (by simp) (M := ClosedCell (m + 1)))
      ≃ₘ⟮𝓡∂ (m + 1), 𝓡 (m + 1)⟯
        (⟨Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, Metric.isOpen_ball⟩ :
          TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1)))) where
  toFun := interiorToBall m
  invFun := ballToInterior m
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (openBall m) (interiorToBall m)).mp
    exact (isSmoothEmbedding_closedCell_inclusion m).contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (inside m) (ballToInterior m)).mp
    apply (ContMDiff.iff_comp_isImmersion
      (isSmoothEmbedding_closedCell_inclusion m).isImmersion).mpr
    exact ⟨continuous_subtype_val.subtype_mk _, contMDiff_subtype_val⟩

theorem closedCellInteriorDiffeomorph_apply
    (x : intrinsicInterior (𝓡∂ (m + 1)) ∞ (by simp) (M := ClosedCell (m + 1))) :
    (closedCellInteriorDiffeomorph m x).val = x.val.val := rfl

theorem closedCellInteriorDiffeomorph_symm_apply
    (x : (⟨Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, Metric.isOpen_ball⟩ :
      TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1))))) :
    ((closedCellInteriorDiffeomorph m).symm x).val.val = x.val := rfl

end DifferentialGeometry.Topology.Manifold
