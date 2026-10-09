import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace ContinuousLinearMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_comp_sub_comp_le (A B : F →L[ℝ] G) (U V : E →L[ℝ] F) :
    ‖A.comp U - B.comp V‖ ≤ ‖A‖ * ‖U - V‖ + ‖A - B‖ * ‖V‖ := by
  have heq : A.comp U - B.comp V = A.comp (U - V) + (A - B).comp V := by
    ext x
    simp only [sub_apply, add_apply, comp_apply, map_sub]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _))

end ContinuousLinearMap

namespace DifferentialGeometry.Analysis

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_fderiv_comp_sub_le {W : F → G} {U V : E → F} {x : E}
    (hW : Differentiable ℝ W) (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    {A B L ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hDW : ‖fderiv ℝ W (U x)‖ ≤ A)
    (hLip : ‖fderiv ℝ W (U x) - fderiv ℝ W (V x)‖ ≤ B * ‖U x - V x‖)
    (hvalue : ‖U x - V x‖ ≤ ε)
    (hderiv : ‖fderiv ℝ U x - fderiv ℝ V x‖ ≤ ε)
    (hDV : ‖fderiv ℝ V x‖ ≤ L) :
    ‖fderiv ℝ (W ∘ U) x - fderiv ℝ (W ∘ V) x‖ ≤ (A + B * L) * ε := by
  rw [fderiv_comp x (hW (U x)) hU, fderiv_comp x (hW (V x)) hV]
  apply (ContinuousLinearMap.norm_comp_sub_comp_le _ _ _ _).trans
  have h1 := mul_le_mul hDW hderiv (norm_nonneg _) hA
  have h2 := mul_le_mul hLip hDV (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvalue hB) hL
  nlinarith

theorem c1_comp_sub_le_of_derivative_bounds {W : F → G} {U V : E → F} {x : E}
    (hW : Differentiable ℝ W) (hDW : Differentiable ℝ (fderiv ℝ W))
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    {A B L ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hfirst : ∀ y, ‖fderiv ℝ W y‖ ≤ A)
    (hsecond : ∀ y, ‖fderiv ℝ (fderiv ℝ W) y‖ ≤ B)
    (hvalue : ‖U x - V x‖ ≤ ε)
    (hderiv : ‖fderiv ℝ U x - fderiv ℝ V x‖ ≤ ε)
    (hDV : ‖fderiv ℝ V x‖ ≤ L) :
    max ‖W (U x) - W (V x)‖
      ‖fderiv ℝ (W ∘ U) x - fderiv ℝ (W ∘ V) x‖ ≤ (A + B * L) * ε := by
  have hv := (convex_univ : Convex ℝ (Set.univ : Set F)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hW y) (fun y _ => hfirst y) (Set.mem_univ (V x)) (Set.mem_univ (U x))
  have hd := (convex_univ : Convex ℝ (Set.univ : Set F)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hDW y) (fun y _ => hsecond y) (Set.mem_univ (V x)) (Set.mem_univ (U x))
  apply max_le
  · have h := hv.trans (mul_le_mul_of_nonneg_left hvalue hA)
    nlinarith [mul_nonneg (mul_nonneg hB hL) hε]
  · exact norm_fderiv_comp_sub_le hW hU hV hA hB hL (hfirst _) hd hvalue hderiv hDV

end DifferentialGeometry.Analysis
