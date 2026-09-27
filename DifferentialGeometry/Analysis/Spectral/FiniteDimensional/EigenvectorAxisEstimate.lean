import DifferentialGeometry.Analysis.Spectral.FiniteDimensional.LeastEigenvector
import Mathlib.Tactic.Linarith

noncomputable section
open Set Metric
open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem quadratic_form_error_bound
    (A : E →L[ℝ] E) (v : E) (κ ε : ℝ)
    (herror : ∀ x : E, ‖A x - κ • (x - ⟪v, x⟫_ℝ • v)‖ ≤ ε * ‖x‖)
    (x : E) (hx : ‖x‖ = 1) :
    |⟪A x, x⟫_ℝ - κ * (1 - ⟪v, x⟫_ℝ ^ 2)| ≤ ε := by
  have hid : ⟪A x - κ • (x - ⟪v, x⟫_ℝ • v), x⟫_ℝ =
      ⟪A x, x⟫_ℝ - κ * (1 - ⟪v, x⟫_ℝ ^ 2) := by
    simp only [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hx]
    ring
  rw [← hid]
  calc
    _ ≤ ‖A x - κ • (x - ⟪v, x⟫_ℝ • v)‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ ≤ ε * ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_right (herror x) (norm_nonneg x)
    _ = ε := by rw [hx]; ring

theorem abs_least_eigenvalue_le_axis_error
    (A : E →L[ℝ] E) (v : E) (hv : ‖v‖ = 1) {κ ε μ : ℝ} (hκ : 0 ≤ κ)
    (herror : ∀ x : E, ‖A x - κ • (x - ⟪v, x⟫_ℝ • v)‖ ≤ ε * ‖x‖)
    (w : E) (hw : ‖w‖ = 1) (heigen : A w = μ • w)
    (hmin : ∀ x : E, ‖x‖ = 1 → μ ≤ ⟪A x, x⟫_ℝ) : |μ| ≤ ε := by
  have heval : ⟪A w, w⟫_ℝ = μ := by
    rw [heigen, real_inner_smul_left, real_inner_self_eq_norm_sq, hw]
    ring
  have hlower := (abs_le.mp (quadratic_form_error_bound A v κ ε herror w hw)).1
  rw [heval] at hlower
  have hdot : |⟪v, w⟫_ℝ| ≤ 1 := by simpa only [hv, hw, mul_one] using abs_real_inner_le_norm v w
  have hdotSq : 0 ≤ 1 - ⟪v, w⟫_ℝ ^ 2 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hdot
    nlinarith
  have haxis := quadratic_form_error_bound A v κ ε herror v hv
  rw [real_inner_self_eq_norm_sq, hv] at haxis
  norm_num at haxis
  exact abs_le.mpr ⟨by nlinarith [mul_nonneg hκ hdotSq], (hmin v hv).trans (le_abs_self _ |>.trans haxis)⟩

theorem norm_eigenvector_orthogonal_component_le
    (A : E →L[ℝ] E) (v : E) {κ ε μ : ℝ} (hκ : 0 < κ)
    (herror : ∀ x : E, ‖A x - κ • (x - ⟪v, x⟫_ℝ • v)‖ ≤ ε * ‖x‖)
    (w : E) (hw : ‖w‖ = 1) (heigen : A w = μ • w) (hμ : |μ| ≤ ε) :
    ‖w - ⟪v, w⟫_ℝ • v‖ ≤ 2 * ε / κ := by
  have hnorm : ‖A w‖ ≤ ε := by
    rw [heigen, norm_smul, Real.norm_eq_abs, hw, mul_one]
    exact hμ
  have herr : ‖A w - κ • (w - ⟪v, w⟫_ℝ • v)‖ ≤ ε := by
    simpa only [hw, mul_one] using herror w
  have hbound := norm_sub_le (A w) (A w - κ • (w - ⟪v, w⟫_ℝ • v))
  rw [sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos hκ] at hbound
  apply (le_div_iff₀ hκ).mpr
  nlinarith

theorem eq_zero_of_eigenvector_orthogonal_to_axis
    (A : E →L[ℝ] E) (v : E) {κ ε μ : ℝ} (hκ : 0 < κ)
    (herror : ∀ x : E, ‖A x - κ • (x - ⟪v, x⟫_ℝ • v)‖ ≤ ε * ‖x‖)
    (hgap : |μ| + ε < κ) (x : E) (heigen : A x = μ • x) (horth : ⟪v, x⟫_ℝ = 0) :
    x = 0 := by
  have herr := herror x
  rw [horth, zero_smul, sub_zero] at herr
  have hbound := norm_sub_le (A x) (A x - κ • x)
  rw [sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos hκ] at hbound
  rw [heigen, norm_smul, Real.norm_eq_abs] at hbound
  rw [heigen] at herr
  have hn : ‖x‖ = 0 := by
    apply le_antisymm _ (norm_nonneg x)
    by_contra hn
    have hp : 0 < ‖x‖ := lt_of_not_ge hn
    nlinarith [mul_lt_mul_of_pos_right hgap hp]
  exact norm_eq_zero.mp hn

theorem eigenspace_eq_span_of_axis_error
    (A : E →L[ℝ] E) (v : E) {κ ε μ : ℝ} (hκ : 0 < κ)
    (herror : ∀ x : E, ‖A x - κ • (x - ⟪v, x⟫_ℝ • v)‖ ≤ ε * ‖x‖)
    (hgap : |μ| + ε < κ) (w : E) (hw : w ≠ 0) (heigen : A w = μ • w) :
    Module.End.eigenspace A.toLinearMap μ = Submodule.span ℝ {w} := by
  have hdot : ⟪v, w⟫_ℝ ≠ 0 := fun hz ↦
    hw (eq_zero_of_eigenvector_orthogonal_to_axis A v hκ herror hgap w heigen hz)
  apply le_antisymm
  · intro x hx
    have hx' : A x = μ • x := Module.End.mem_eigenspace_iff.mp hx
    let c : ℝ := ⟪v, x⟫_ℝ / ⟪v, w⟫_ℝ
    have hy : A (x - c • w) = μ • (x - c • w) := by
      rw [map_sub, map_smul, hx', heigen, smul_sub, smul_comm c μ]
    have horth : ⟪v, x - c • w⟫_ℝ = 0 := by
      rw [inner_sub_right, real_inner_smul_right]
      exact sub_eq_zero.mpr (div_mul_cancel₀ _ hdot).symm
    have hz := eq_zero_of_eigenvector_orthogonal_to_axis A v hκ herror hgap _ hy horth
    exact Submodule.mem_span_singleton.mpr ⟨c, (sub_eq_zero.mp hz).symm⟩
  · apply Submodule.span_le.mpr
    intro x hx
    rcases mem_singleton_iff.mp hx with rfl
    exact Module.End.mem_eigenspace_iff.mpr heigen

private theorem norm_sub_axis_le
    (v w : E) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hpos : 0 ≤ ⟪v, w⟫_ℝ) :
    ‖w - v‖ ≤ 2 * ‖w - ⟪v, w⟫_ℝ • v‖ := by
  have hdot : ⟪v, w⟫_ℝ ≤ 1 :=
    (le_abs_self _).trans (by simpa only [hv, hw, mul_one] using abs_real_inner_le_norm v w)
  have hsq : ‖w - ⟪v, w⟫_ℝ • v‖ ^ 2 = 1 - ⟪v, w⟫_ℝ ^ 2 := by
    have hcomm : ⟪w, v⟫_ℝ = ⟪v, w⟫_ℝ := real_inner_comm _ _
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hv, hw,
      real_inner_smul_right, hcomm, abs_of_nonneg hpos]
    ring
  have hd : ‖w - v‖ ^ 2 = 2 - 2 * ⟪v, w⟫_ℝ := by
    have hcomm : ⟪w, v⟫_ℝ = ⟪v, w⟫_ℝ := real_inner_comm _ _
    rw [norm_sub_sq_real, hv, hw, hcomm]
    ring
  nlinarith [norm_nonneg (w - v), norm_nonneg (w - ⟪v, w⟫_ℝ • v),
    mul_nonneg hpos (sub_nonneg.mpr hdot)]

theorem exists_least_eigenvector_close_to_axis
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (v : E) (hv : ‖v‖ = 1)
    {κ ε : ℝ} (hκ : 0 < κ) (hε : ε < κ / 2)
    (herror : ∀ x : E, ‖A x - κ • (x - ⟪v, x⟫_ℝ • v)‖ ≤ ε * ‖x‖) :
    ∃ (μ : ℝ) (w : E), ‖w‖ = 1 ∧ A w = μ • w ∧
      (∀ x : E, ‖x‖ = 1 → μ ≤ ⟪A x, x⟫_ℝ) ∧ |μ| ≤ ε ∧
      0 < ⟪v, w⟫_ℝ ∧ ‖w - v‖ ≤ 4 * ε / κ ∧
      Module.End.eigenspace A.toLinearMap μ = Submodule.span ℝ {w} := by
  have hvne : v ≠ 0 := fun hz ↦ by simp [hz] at hv
  let : Nontrivial E := nontrivial_of_ne v 0 hvne
  obtain ⟨μ, w₀, hw₀, heigen₀, hmin⟩ := exists_unit_least_eigenvector A hA
  have hμ := abs_least_eigenvalue_le_axis_error A v hv hκ.le herror w₀ hw₀ heigen₀ hmin
  have hgap : |μ| + ε < κ := by linarith
  obtain ⟨w, hw, heigen, hnonneg⟩ : ∃ w : E, ‖w‖ = 1 ∧ A w = μ • w ∧ 0 ≤ ⟪v, w⟫_ℝ := by
    by_cases h : 0 ≤ ⟪v, w₀⟫_ℝ
    · exact ⟨w₀, hw₀, heigen₀, h⟩
    · refine ⟨-w₀, by simpa using hw₀, ?_, ?_⟩
      · rw [map_neg, heigen₀, smul_neg]
      · rw [inner_neg_right]
        exact neg_nonneg.mpr (le_of_not_ge h)
  have hwne : w ≠ 0 := fun hz ↦ by simp [hz] at hw
  have hdot : ⟪v, w⟫_ℝ ≠ 0 := fun hz ↦
    hwne (eq_zero_of_eigenvector_orthogonal_to_axis A v hκ herror hgap w heigen hz)
  refine ⟨μ, w, hw, heigen, hmin, hμ, lt_of_le_of_ne hnonneg hdot.symm, ?_,
    eigenspace_eq_span_of_axis_error A v hκ herror hgap w hwne heigen⟩
  have hb := norm_eigenvector_orthogonal_component_le A v hκ herror w hw heigen hμ
  have hd := norm_sub_axis_le v w hv hw hnonneg
  calc
    ‖w - v‖ ≤ 2 * (2 * ε / κ) := hd.trans (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = 4 * ε / κ := by ring

end DifferentialGeometry.Analysis
