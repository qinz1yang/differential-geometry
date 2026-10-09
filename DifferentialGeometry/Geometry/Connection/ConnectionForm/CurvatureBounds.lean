import DifferentialGeometry.Geometry.Connection.ConnectionForm.Curvature
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

variable {V E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem norm_clm_triple_apply_le
    (D : V →L[ℝ] V →L[ℝ] E →L[ℝ] E) (X Y : V) (u : E) :
    ‖D X Y u‖ ≤ ‖D‖ * ‖X‖ * ‖Y‖ * ‖u‖ := by
  calc
    _ ≤ ‖D X Y‖ * ‖u‖ := (D X Y).le_opNorm u
    _ ≤ (‖D X‖ * ‖Y‖) * ‖u‖ := by
      gcongr
      exact (D X).le_opNorm Y
    _ ≤ (‖D‖ * ‖X‖) * ‖Y‖ * ‖u‖ := by
      gcongr
      exact D.le_opNorm X

private theorem norm_connectionForm_comp_apply_le
    (P Q : V →L[ℝ] E →L[ℝ] E) (X Y : V) (u : E) :
    ‖P X (Q Y u)‖ ≤ ‖P‖ * ‖Q‖ * ‖X‖ * ‖Y‖ * ‖u‖ := by
  calc
    _ ≤ ‖P X‖ * ‖Q Y u‖ := (P X).le_opNorm (Q Y u)
    _ ≤ (‖P‖ * ‖X‖) * (‖Q Y‖ * ‖u‖) :=
      mul_le_mul (P.le_opNorm X) ((Q Y).le_opNorm u) (norm_nonneg _) (by positivity)
    _ ≤ (‖P‖ * ‖X‖) * ((‖Q‖ * ‖Y‖) * ‖u‖) := by
      gcongr
      exact Q.le_opNorm Y
    _ = _ := by ring

private theorem norm_curvature_expression_le
    (D : V →L[ℝ] V →L[ℝ] E →L[ℝ] E)
    (P Q : V →L[ℝ] E →L[ℝ] E) (X Y : V) (u : E) :
    ‖D X Y u - D Y X u + P X (Q Y u) - P Y (Q X u)‖ ≤
      (2 * ‖D‖ + 2 * ‖P‖ * ‖Q‖) * ‖X‖ * ‖Y‖ * ‖u‖ := by
  calc
    _ ≤ ‖D X Y u - D Y X u + P X (Q Y u)‖ + ‖P Y (Q X u)‖ := norm_sub_le _ _
    _ ≤ (‖D X Y u - D Y X u‖ + ‖P X (Q Y u)‖) + ‖P Y (Q X u)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (‖D X Y u‖ + ‖D Y X u‖ + ‖P X (Q Y u)‖) + ‖P Y (Q X u)‖ :=
      add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ ≤ (‖D‖ * ‖X‖ * ‖Y‖ * ‖u‖ + ‖D‖ * ‖Y‖ * ‖X‖ * ‖u‖ +
        ‖P‖ * ‖Q‖ * ‖X‖ * ‖Y‖ * ‖u‖) + ‖P‖ * ‖Q‖ * ‖Y‖ * ‖X‖ * ‖u‖ :=
      add_le_add (add_le_add (add_le_add (norm_clm_triple_apply_le D X Y u)
        (norm_clm_triple_apply_le D Y X u)) (norm_connectionForm_comp_apply_le P Q X Y u))
        (norm_connectionForm_comp_apply_le P Q Y X u)
    _ = _ := by ring

theorem norm_connectionFormCurvature_le
    (A : V → V →L[ℝ] E →L[ℝ] E) (x X Y : V) (u : E) :
    ‖connectionFormCurvature A x X Y u‖ ≤
      (2 * ‖fderiv ℝ A x‖ + 2 * ‖A x‖ ^ 2) * ‖X‖ * ‖Y‖ * ‖u‖ := by
  simpa only [connectionFormCurvature, pow_two, mul_assoc] using
    norm_curvature_expression_le (fderiv ℝ A x) (A x) (A x) X Y u

theorem norm_connectionFormCurvature_sub_le
    (A B : V → V →L[ℝ] E →L[ℝ] E) (x X Y : V) (u : E) :
    ‖connectionFormCurvature A x X Y u - connectionFormCurvature B x X Y u‖ ≤
      (2 * ‖fderiv ℝ A x - fderiv ℝ B x‖ +
        2 * (‖A x‖ + ‖B x‖) * ‖A x - B x‖) * ‖X‖ * ‖Y‖ * ‖u‖ := by
  let D := fderiv ℝ A x - fderiv ℝ B x
  let C := A x - B x
  have heq : connectionFormCurvature A x X Y u - connectionFormCurvature B x X Y u =
      (D X Y u - D Y X u + C X (A x Y u) - C Y (A x X u)) +
        ((0 : V →L[ℝ] V →L[ℝ] E →L[ℝ] E) X Y u -
          (0 : V →L[ℝ] V →L[ℝ] E →L[ℝ] E) Y X u +
          B x X (C Y u) - B x Y (C X u)) := by
    simp only [D, C, connectionFormCurvature, sub_apply, map_sub, zero_apply]
    abel
  rw [heq]
  calc
    _ ≤ ‖D X Y u - D Y X u + C X (A x Y u) - C Y (A x X u)‖ +
        ‖(0 : V →L[ℝ] V →L[ℝ] E →L[ℝ] E) X Y u -
          (0 : V →L[ℝ] V →L[ℝ] E →L[ℝ] E) Y X u +
          B x X (C Y u) - B x Y (C X u)‖ := norm_add_le _ _
    _ ≤ (2 * ‖D‖ + 2 * ‖C‖ * ‖A x‖) * ‖X‖ * ‖Y‖ * ‖u‖ +
        (2 * ‖(0 : V →L[ℝ] V →L[ℝ] E →L[ℝ] E)‖ + 2 * ‖B x‖ * ‖C‖) *
          ‖X‖ * ‖Y‖ * ‖u‖ :=
      add_le_add (norm_curvature_expression_le D C (A x) X Y u)
        (norm_curvature_expression_le 0 (B x) C X Y u)
    _ = _ := by
      simp only [norm_zero, D, C]
      ring

end DifferentialGeometry.Geometry.Connection
