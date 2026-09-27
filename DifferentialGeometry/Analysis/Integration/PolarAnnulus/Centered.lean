import DifferentialGeometry.Analysis.Integration.PolarAnnulus
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Group.Measure

noncomputable section

open Set MeasureTheory

namespace DifferentialGeometry.Analysis

theorem integral_annulus_eq_circleMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (c : ℂ) {r R : ℝ} (hr : 0 < r) :
    (∫ z in {z : ℂ | dist z c ∈ Icc r R}, f z) =
      ∫ p in Icc (r, -Real.pi) (R, Real.pi), p.1 • f (circleMap c p.1 p.2) := by
  calc
    _ = ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, f (c + z) := by
      have h := (measurePreserving_add_left (volume : Measure ℂ) c).setIntegral_preimage_emb
        (MeasurableEquiv.addLeft c).measurableEmbedding f {z : ℂ | dist z c ∈ Icc r R}
      simpa only [preimage_ofPred_eq, dist_eq_norm, add_sub_cancel_left] using h.symm
    _ = ∫ p in Icc (r, -Real.pi) (R, Real.pi),
        p.1 • f (c + Complex.polarCoord.symm p) := integral_annulus_eq_polar _ hr
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro p hp
      simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]

end DifferentialGeometry.Analysis

end
