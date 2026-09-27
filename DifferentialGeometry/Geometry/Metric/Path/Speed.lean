import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)]
  [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]

theorem riemannianEDist_le_of_curve_speed_bound
    {γ : ℝ → M} {a b : ℝ} {C : ℝ≥0∞} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hC : ∀ t ∈ Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ ≤ C) :
    riemannianEDist I (γ a) (γ b) ≤ C * ENNReal.ofReal (b - a) := by
  apply (riemannianEDist_le_pathELength hγ rfl rfl hab).trans
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  calc
    _ ≤ ∫⁻ _t in Ioo a b, C := setLIntegral_mono' measurableSet_Ioo hC
    _ = _ := by rw [setLIntegral_const, Real.volume_Ioo]

end Manifold
