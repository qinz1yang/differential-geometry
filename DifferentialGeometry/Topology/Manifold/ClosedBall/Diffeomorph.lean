import DifferentialGeometry.Topology.Manifold.ClosedBall
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {m : ℕ}

private local instance closedCellCharts : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  Handle.closedCellChartedSpaceSucc m

private local instance closedCellSmooth : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  Handle.closedCellIsManifold m

variable (D : EuclideanSpace ℝ (Fin (m + 1)) ≃ₘ⟮𝓡 (m + 1), 𝓡 (m + 1)⟯
    EuclideanSpace ℝ (Fin (m + 1)))
  (hD : D '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)

include hD in
private theorem norm_le_one_iff (x : EuclideanSpace ℝ (Fin (m + 1))) : ‖x‖ ≤ 1 ↔ ‖D x‖ ≤ 1 := by
  have h : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ↔
      D x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
    constructor
    · intro hx
      rw [← hD]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hD] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      exact D.injective hxy ▸ hy
  simpa only [Metric.mem_closedBall, dist_zero_right] using h

def closedCellDiffeomorph :
    ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ ClosedCell (m + 1) where
  toEquiv := D.toEquiv.subtypeEquiv (norm_le_one_iff D hD)
  contMDiff_toFun := by
    apply (ContMDiff.iff_comp_isImmersion (isSmoothEmbedding_closedCell_inclusion m).isImmersion).mpr
    exact ⟨(D.continuous.comp continuous_subtype_val).subtype_mk _,
      D.contMDiff.comp (isSmoothEmbedding_closedCell_inclusion m).contMDiff⟩
  contMDiff_invFun := by
    apply (ContMDiff.iff_comp_isImmersion (isSmoothEmbedding_closedCell_inclusion m).isImmersion).mpr
    exact ⟨(D.symm.continuous.comp continuous_subtype_val).subtype_mk _,
      D.symm.contMDiff.comp (isSmoothEmbedding_closedCell_inclusion m).contMDiff⟩

@[simp] theorem closedCellDiffeomorph_apply (x : ClosedCell (m + 1)) :
    (closedCellDiffeomorph D hD x).val = D x.val := rfl

@[simp] theorem closedCellDiffeomorph_symm_apply (x : ClosedCell (m + 1)) :
    ((closedCellDiffeomorph D hD).symm x).val = D.symm x.val := rfl

theorem closedCellDiffeomorph_eq_self_iff (x : ClosedCell (m + 1)) :
    closedCellDiffeomorph D hD x = x ↔ D x.val = x.val :=
  Subtype.ext_iff

theorem closedCellDiffeomorph_eq_self_of_norm_le {r : ℝ}
    (hfix : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ ≤ r → D y = y) (x : ClosedCell (m + 1))
    (hx : ‖x.val‖ ≤ r) : closedCellDiffeomorph D hD x = x :=
  (closedCellDiffeomorph_eq_self_iff D hD x).mpr (hfix x.val hx)

theorem closedCellDiffeomorph_cellBoundaryInclusion (a : CellBoundary (m + 1) → CellBoundary (m + 1))
    (ha : ∀ z : CellBoundary (m + 1), D z.val = (a z).val) (z : CellBoundary (m + 1)) :
    closedCellDiffeomorph D hD (cellBoundaryInclusion (m + 1) z) =
      cellBoundaryInclusion (m + 1) (a z) :=
  Subtype.ext (ha z)

theorem closedCellDiffeomorph_boundary_eq_self
    (hfix : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ = 1 → D y = y) (z : CellBoundary (m + 1)) :
    closedCellDiffeomorph D hD (cellBoundaryInclusion (m + 1) z) =
      cellBoundaryInclusion (m + 1) z :=
  Subtype.ext (hfix z.val z.property)

end DifferentialGeometry.Topology.Manifold
