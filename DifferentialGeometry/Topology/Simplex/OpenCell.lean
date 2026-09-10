import DifferentialGeometry.Topology.Simplex.BallHomeomorphism
import DifferentialGeometry.Topology.Simplex.Reindex
import DifferentialGeometry.Topology.Simplex.RelativeHomology

set_option autoImplicit false
noncomputable section
open Set Metric
namespace Poincare.Simplex


def openCellReindexHomeomorph {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    openCell ι ≃ₜ openCell κ :=
  (reindexHomeomorph e).subtype (fun x ↦ by
    simp only [openCell_eq_compl_boundary, Set.mem_compl_iff]
    exact not_congr (reindexHomeomorph_mem_boundary e x).symm)


@[simp]
theorem openCellReindexHomeomorph_val {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (x : openCell ι) : (openCellReindexHomeomorph e x).val = reindexHomeomorph e x.val := rfl


@[simp]
theorem openCellReindexHomeomorph_symm_val {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (x : openCell κ) :
    ((openCellReindexHomeomorph e).symm x).val = (reindexHomeomorph e).symm x.val := rfl

def stdSimplexOpenBallHomeomorph (n : ℕ) :
    openCell (Fin (n + 1)) ≃ₜ ball (0 : Fin n → ℝ) 1 where
  toFun x := ⟨(stdSimplexBallHomeomorph n x.val).val, by
    have hle : ‖(stdSimplexBallHomeomorph n x.val).val‖ ≤ 1 :=
      mem_closedBall_zero_iff.mp (stdSimplexBallHomeomorph n x.val).prop
    apply mem_ball_zero_iff.mpr
    apply lt_of_le_of_ne hle
    intro he
    have hx : x.val ∉ boundary (Fin (n + 1)) := by
      simpa only [openCell_eq_compl_boundary, Set.mem_compl_iff] using x.prop
    exact hx ((stdSimplexBallHomeomorph_norm_eq_one_iff n x.val).mp he)⟩
  invFun y := ⟨(stdSimplexBallHomeomorph n).symm ⟨y.val, ball_subset_closedBall y.prop⟩, by
    rw [openCell_eq_compl_boundary]
    intro h
    have hh := (stdSimplexBallHomeomorph_mem_sphere_iff n _).mpr h
    rw [Homeomorph.apply_symm_apply] at hh
    exact (ne_of_lt (mem_ball_zero_iff.mp y.prop)) (mem_sphere_zero_iff_norm.mp hh)⟩
  left_inv x := by
    apply Subtype.ext
    exact (stdSimplexBallHomeomorph n).symm_apply_apply x.val
  right_inv y := by
    apply Subtype.ext
    change ((stdSimplexBallHomeomorph n) ((stdSimplexBallHomeomorph n).symm
      ⟨y.val, ball_subset_closedBall y.prop⟩)).val = y.val
    rw [Homeomorph.apply_symm_apply]
  continuous_toFun := (continuous_subtype_val.comp
    ((stdSimplexBallHomeomorph n).continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := ((stdSimplexBallHomeomorph n).symm.continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _


@[simp]
theorem stdSimplexOpenBallHomeomorph_val (n : ℕ) (x : openCell (Fin (n + 1))) :
    (stdSimplexOpenBallHomeomorph n x).val = (stdSimplexBallHomeomorph n x.val).val := rfl


@[simp]
theorem stdSimplexOpenBallHomeomorph_symm_val (n : ℕ) (y : ball (0 : Fin n → ℝ) 1) :
    ((stdSimplexOpenBallHomeomorph n).symm y).val =
      (stdSimplexBallHomeomorph n).symm ⟨y.val, ball_subset_closedBall y.prop⟩ := rfl

end Poincare.Simplex
