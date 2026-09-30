import DifferentialGeometry.Topology.Handle.Manifold

noncomputable section

open Set Manifold
open scoped Manifold

namespace DifferentialGeometry.Topology.Handle

private local instance (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

theorem closedCell_chartAt_of_norm_lt_one {m : ℕ}
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1) :
    chartAt (EuclideanHalfSpace (m + 1)) α = closedCellInteriorChart m := by
  change closedCellChartAt α = _
  rw [closedCellChartAt, dite_eq_left hα]

theorem closedCell_extChartAt_apply_of_norm_lt_one {m : ℕ}
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    (x : ClosedCell (m + 1)) :
    extChartAt (𝓡∂ (m + 1)) α x = closedCellShiftSucc m 1 x.val := by
  change (closedCellChartAt α x).val = _
  rw [closedCellChartAt, dite_eq_left hα]
  rfl

theorem closedCell_extChartAt_source_of_norm_lt_one {m : ℕ}
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1) :
    (extChartAt (𝓡∂ (m + 1)) α).source =
      {x : ClosedCell (m + 1) | ‖x.val‖ < 1} := by
  rw [extChartAt_source,
    closedCell_chartAt_of_norm_lt_one α hα]
  rfl

theorem closedCell_extChartAt_symm_val_of_norm_lt_one {m : ℕ}
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    (z : EuclideanSpace ℝ (Fin (m + 1)))
    (hz : z ∈ (extChartAt (𝓡∂ (m + 1)) α).target) :
    ((extChartAt (𝓡∂ (m + 1)) α).symm z).val =
      closedCellShiftSucc m (-1) z := by
  have he := (extChartAt (𝓡∂ (m + 1)) α).right_inv hz
  rw [closedCell_extChartAt_apply_of_norm_lt_one α hα] at he
  calc
    ((extChartAt (𝓡∂ (m + 1)) α).symm z).val =
        closedCellShiftSucc m (-1)
          (closedCellShiftSucc m 1
            ((extChartAt (𝓡∂ (m + 1)) α).symm z).val) :=
      (closedCellShiftSucc_neg_left_inv m 1 _).symm
    _ = closedCellShiftSucc m (-1) z :=
      congrArg (closedCellShiftSucc m (-1)) he

theorem mem_closedCell_extChartAt_target_iff_of_norm_lt_one {m : ℕ}
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    (z : EuclideanSpace ℝ (Fin (m + 1))) :
    z ∈ (extChartAt (𝓡∂ (m + 1)) α).target ↔
      ‖closedCellShiftSucc m (-1) z‖ < 1 := by
  constructor
  · intro hz
    have hs := (extChartAt (𝓡∂ (m + 1)) α).map_target hz
    rw [closedCell_extChartAt_source_of_norm_lt_one α hα] at hs
    change ‖((extChartAt (𝓡∂ (m + 1)) α).symm z).val‖ < 1 at hs
    rwa [closedCell_extChartAt_symm_val_of_norm_lt_one α hα z hz] at hs
  · intro hz
    let x : ClosedCell (m + 1) :=
      ⟨closedCellShiftSucc m (-1) z, hz.le⟩
    have hx : x ∈ (extChartAt (𝓡∂ (m + 1)) α).source := by
      rw [closedCell_extChartAt_source_of_norm_lt_one α hα]
      exact hz
    have ht := (extChartAt (𝓡∂ (m + 1)) α).map_source hx
    rw [closedCell_extChartAt_apply_of_norm_lt_one α hα] at ht
    change closedCellShiftSucc m 1 (closedCellShiftSucc m (-1) z) ∈
      (extChartAt (𝓡∂ (m + 1)) α).target at ht
    rwa [closedCellShiftSucc_neg_right_inv m 1 z] at ht

end DifferentialGeometry.Topology.Handle
