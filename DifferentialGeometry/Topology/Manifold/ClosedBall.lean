import DifferentialGeometry.Topology.Handle.Manifold
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false

open Set Manifold IsManifold
open scoped Manifold Topology
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Handle

namespace DifferentialGeometry.Topology.Manifold

noncomputable section

private local instance (m : ℕ) : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

private local instance (m : ℕ) : IsManifold (𝓡∂ (m + 1)) (⊤ : ℕ∞) (ClosedCell (m + 1)) :=
  closedCellIsManifold m

theorem closedCell_boundary_eq_sphere (m : ℕ) :
    (𝓡∂ (m + 1)).boundary (ClosedCell (m + 1)) = {x | ‖x.val‖ = 1} := by
  ext x
  change ((𝓡∂ (m + 1)) (closedCellChartAt x x) ∈
    frontier (range (𝓡∂ (m + 1)))) ↔ ‖x.val‖ = 1
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  by_cases hx : ‖x.val‖ < 1
  · rw [closedCellChartAt, dif_pos hx]
    change (0 = (closedCellShiftSucc m 1 x.val) 0) ↔ ‖x.val‖ = 1
    rw [closedCellShiftSucc_apply_zero]
    have hcoord := closedCellCoord_norm_le_norm x.val
    have hlow : -‖x.val‖ ≤ x.val 0 := by
      have := (abs_le.mp (show |x.val 0| ≤ ‖x.val‖ from hcoord)).1
      exact this
    constructor <;> intro h <;> linarith
  · rw [closedCellChartAt, dif_neg hx]
    change (0 = 1 - ‖x.val‖ ^ 2) ↔ ‖x.val‖ = 1
    constructor <;> intro h <;> nlinarith [norm_nonneg x.val, x.property]

private def boundaryForward (m : ℕ) (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : EuclideanSpace ℝ (Fin (m + 1))) : EuclideanSpace ℝ (Fin (m + 1)) :=
  closedCellCons m (1 - ‖x‖ ^ 2) (closedCellTail m (closedCellPermute e x))

private theorem boundaryForward_contDiff (m : ℕ) (e : Fin (m + 1) ≃ Fin (m + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (boundaryForward m e) :=
  closedCellCons_contDiff.comp
    ((contDiff_const.sub (contDiff_norm_sq ℝ)).prodMk
      ((closedCellTail_contDiff (m := m)).comp (closedCellPermute_contDiff e)))

private theorem boundaryForward_radicand (m : ℕ) (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : EuclideanSpace ℝ (Fin (m + 1))) :
    1 - boundaryForward m e x 0 - ‖closedCellTail m (boundaryForward m e x)‖ ^ 2 =
      (closedCellPermute e x 0) ^ 2 := by
  simp only [boundaryForward, closedCellCons_apply_zero, closedCellCons_tail]
  have h := closedCellSplit_norm_sq m (closedCellPermute e x)
  rw [closedCellPermute_norm] at h
  linarith

private theorem boundaryForward_left_inv (m : ℕ) (e : Fin (m + 1) ≃ Fin (m + 1))
    (σ : Bool) (x : EuclideanSpace ℝ (Fin (m + 1)))
    (hx : 0 < closedCellSign σ * closedCellPermute e x 0) :
    closedCellBoundaryInvValue m e (closedCellSign σ) (boundaryForward m e x) = x := by
  unfold closedCellBoundaryInvValue
  rw [boundaryForward_radicand, Real.sqrt_sq_eq_abs, closedCellSign_mul_abs hx]
  simp only [boundaryForward, closedCellCons_tail]
  rw [closedCellCons_split, closedCellPermute_left_inv]

private theorem boundaryForward_right_inv (m : ℕ) (e : Fin (m + 1) ≃ Fin (m + 1))
    (σ : Bool) (y : EuclideanSpace ℝ (Fin (m + 1)))
    (hy : 0 < 1 - y 0 - ‖closedCellTail m y‖ ^ 2) :
    boundaryForward m e (closedCellBoundaryInvValue m e (closedCellSign σ) y) = y := by
  unfold boundaryForward
  rw [closedCellBoundaryInvValue_norm_sq e (closedCellSign_sq σ) y hy]
  simp only [closedCellBoundaryInvValue, closedCellPermute_right_inv, closedCellCons_tail]
  rw [show 1 - (1 - y 0) = y 0 by ring, closedCellCons_split]

private def boundaryAmbientChart (m : ℕ) (i : Fin (m + 1)) (σ : Bool) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (m + 1)))
      (EuclideanSpace ℝ (Fin (m + 1))) := by
  let e := Equiv.swap i (0 : Fin (m + 1))
  refine
    { source := {x | 0 < closedCellSign σ * closedCellPermute e x 0}
      target := {y | 0 < 1 - y 0 - ‖closedCellTail m y‖ ^ 2}
      toFun := boundaryForward m e
      invFun := closedCellBoundaryInvValue m e (closedCellSign σ)
      map_source' := ?_
      map_target' := ?_
      left_inv' := boundaryForward_left_inv m e σ
      right_inv' := boundaryForward_right_inv m e σ
      continuousOn_toFun := (boundaryForward_contDiff m e).continuous.continuousOn
      continuousOn_invFun := (closedCellBoundaryInvValue_contDiffOn e (closedCellSign σ)).continuousOn
      open_source := ?_
      open_target := ?_ }
  · intro x hx
    change 0 < 1 - boundaryForward m e x 0 - ‖closedCellTail m (boundaryForward m e x)‖ ^ 2
    rw [boundaryForward_radicand]
    exact sq_pos_of_ne_zero (closedCellPermute_coord_ne_zero e hx)
  · intro y hy
    change 0 < closedCellSign σ *
      closedCellPermute e (closedCellBoundaryInvValue m e (closedCellSign σ) y) 0
    simp only [closedCellBoundaryInvValue, closedCellPermute_right_inv, closedCellCons_apply_zero]
    rw [← mul_assoc, closedCellSign_mul_self, one_mul]
    exact Real.sqrt_pos.mpr hy
  · exact isOpen_lt continuous_const
      (continuous_const.mul ((PiLp.continuous_apply 2 (fun _ : Fin (m + 1) => ℝ) 0).comp
        (closedCellPermute e).continuous))
  · apply isOpen_lt continuous_const
    exact (continuous_const.sub (PiLp.continuous_apply 2 (fun _ : Fin (m + 1) => ℝ) 0)).sub
      ((continuous_norm.comp (closedCellTail_contDiff (m := m)).continuous).pow 2)

private theorem boundaryAmbientChart_mem_maximalAtlas (m : ℕ) (i : Fin (m + 1)) (σ : Bool) :
    boundaryAmbientChart m i σ ∈ maximalAtlas (𝓡 (m + 1)) (⊤ : ℕ∞)
      (EuclideanSpace ℝ (Fin (m + 1))) := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (boundaryForward_contDiff m (Equiv.swap i 0)).contMDiff.contMDiffOn
  · exact (closedCellBoundaryInvValue_contDiffOn (Equiv.swap i 0) (closedCellSign σ)).contMDiffOn

private def interiorAmbientChart (m : ℕ) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (m + 1)))
      (EuclideanSpace ℝ (Fin (m + 1))) where
  source := univ
  target := univ
  toFun := closedCellShiftSucc m 1
  invFun := closedCellShiftSucc m (-1)
  map_source' := fun _ _ => mem_univ _
  map_target' := fun _ _ => mem_univ _
  left_inv' := fun x _ => closedCellShiftSucc_neg_left_inv m 1 x
  right_inv' := fun x _ => closedCellShiftSucc_neg_right_inv m 1 x
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := (closedCellShiftSucc_contDiff 1).continuous.continuousOn
  continuousOn_invFun := (closedCellShiftSucc_contDiff (-1)).continuous.continuousOn

private theorem interiorAmbientChart_mem_maximalAtlas (m : ℕ) :
    interiorAmbientChart m ∈ maximalAtlas (𝓡 (m + 1)) (⊤ : ℕ∞)
      (EuclideanSpace ℝ (Fin (m + 1))) := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (closedCellShiftSucc_contDiff 1).contMDiff.contMDiffOn
  · exact (closedCellShiftSucc_contDiff (-1)).contMDiff.contMDiffOn

private theorem closedCell_inclusion_isImmersionOfComplement (m : ℕ) :
    IsImmersionOfComplement Unit (𝓡∂ (m + 1)) (𝓡 (m + 1)) (⊤ : ℕ∞)
      (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) := by
  intro x
  let φ := ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin (m + 1))) Unit
  by_cases hx : ‖x.val‖ < 1
  · have hchart : chartAt (EuclideanHalfSpace (m + 1)) x = closedCellInteriorChart m := by
      change closedCellChartAt x = _
      rw [closedCellChartAt, dif_pos hx]
    apply IsImmersionAtOfComplement.mk_of_continuousAt continuous_subtype_val.continuousAt φ
      (chartAt (EuclideanHalfSpace (m + 1)) x) (interiorAmbientChart m)
      (mem_chart_source _ x) (mem_univ _) (chart_mem_maximalAtlas _)
      (interiorAmbientChart_mem_maximalAtlas m)
    intro z hz
    change closedCellShiftSucc m 1
      (((chartAt (EuclideanHalfSpace (m + 1)) x).extend (𝓡∂ (m + 1))).symm z).val = z
    have h := ((chartAt (EuclideanHalfSpace (m + 1)) x).extend (𝓡∂ (m + 1))).right_inv hz
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, hchart] at h
    rw [hchart]
    exact h
  · let i : Fin (m + 1) := Classical.choose (exists_closedCell_coord_ne_zero x.val (by
      have := x.property
      linarith))
    let σ : Bool := decide (0 < x.val i)
    have hchart : chartAt (EuclideanHalfSpace (m + 1)) x = closedCellBoundaryChart m i σ := by
      change closedCellChartAt x = _
      rw [closedCellChartAt, dif_neg hx]
    have hsource : x.val ∈ (boundaryAmbientChart m i σ).source := by
      have h := mem_chart_source (EuclideanHalfSpace (m + 1)) x
      rw [hchart] at h
      exact h
    apply IsImmersionAtOfComplement.mk_of_continuousAt continuous_subtype_val.continuousAt φ
      (chartAt (EuclideanHalfSpace (m + 1)) x) (boundaryAmbientChart m i σ)
      (mem_chart_source _ x) hsource (chart_mem_maximalAtlas _)
      (boundaryAmbientChart_mem_maximalAtlas m i σ)
    intro z hz
    change boundaryForward m (Equiv.swap i 0)
      (((chartAt (EuclideanHalfSpace (m + 1)) x).extend (𝓡∂ (m + 1))).symm z).val = z
    have h := ((chartAt (EuclideanHalfSpace (m + 1)) x).extend (𝓡∂ (m + 1))).right_inv hz
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, hchart] at h
    rw [hchart]
    exact h

theorem isSmoothEmbedding_closedCell_inclusion (m : ℕ) :
    IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) (⊤ : ℕ∞)
      (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) :=
  ⟨(closedCell_inclusion_isImmersionOfComplement m).isImmersion,
    _root_.Topology.IsEmbedding.subtypeVal⟩

end

end DifferentialGeometry.Topology.Manifold
