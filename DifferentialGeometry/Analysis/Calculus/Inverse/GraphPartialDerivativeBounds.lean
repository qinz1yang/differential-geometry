import DifferentialGeometry.Analysis.Calculus.Inverse.ImplicitDerivativeBounds

set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace DifferentialGeometry.Analysis
variable {N E F K : Type*}
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

theorem norm_iteratedFDeriv_partial_along_graph_le
    (G : N × E → F) (g : E → N) (x : E) (m : ℕ)
    (L : K →L[ℝ] N × E) (hL : ‖L‖ ≤ 1) (C D : ℝ)
    (hG : ContDiffAt ℝ (m + 1 : ℕ) G (g x, x))
    (hg : ContDiffAt ℝ m g x)
    (hC : ∀ i, 1 ≤ i → i ≤ m + 1 → ‖iteratedFDeriv ℝ i G (g x, x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i g x‖ ≤ D ^ i)
    (hD1 : 1 ≤ D) :
    ‖iteratedFDeriv ℝ m (fun y => (fderiv ℝ G (g y, y)).comp L) x‖ ≤
      (m.factorial : ℝ) * C * D ^ m := by
  let T : ((N × E) →L[ℝ] F) →L[ℝ] K →L[ℝ] F :=
    (ContinuousLinearMap.compL ℝ K (N × E) F).flip L
  have hT : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    change ‖A.comp L‖ ≤ 1 * ‖A‖
    have h := (ContinuousLinearMap.opNorm_comp_le A L).trans
      (mul_le_mul_of_nonneg_left hL (norm_nonneg A))
    simpa only [mul_one, one_mul] using h
  have hdG : ContDiffAt ℝ m (fderiv ℝ G) (g x, x) :=
    hG.fderiv_right (by exact_mod_cast (le_refl (m + 1)))
  let H : N × E → K →L[ℝ] F := fun p => T (fderiv ℝ G p)
  have hH : ContDiffAt ℝ m H (g x, x) := T.contDiff.contDiffAt.comp _ hdG
  have hHjet (i : ℕ) (hi : i ≤ m) : ‖iteratedFDeriv ℝ i H (g x, x)‖ ≤ C := by
    have h := T.norm_iteratedFDeriv_comp_left
      (hdG.of_le (by exact_mod_cast hi)) le_rfl
    apply h.trans
    calc
      _ ≤ 1 * ‖iteratedFDeriv ℝ i (fderiv ℝ G) (g x, x)‖ :=
        mul_le_mul_of_nonneg_right hT (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ (i + 1) G (g x, x)‖ := by
        rw [one_mul, norm_iteratedFDeriv_fderiv]
      _ ≤ C := hC (i + 1) (by omega) (by omega)
  exact norm_iteratedFDeriv_graph_comp_le H g x m C D hH hg hHjet hD hD1

end DifferentialGeometry.Analysis
