import DifferentialGeometry.Geometry.Comparison.ModelSide

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem modelSideNegCurvature_le_iff_angle_le {κ a b θ φ : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b)
    (hθ : θ ∈ Icc (0 : ℝ) Real.pi) (hφ : φ ∈ Icc (0 : ℝ) Real.pi) :
    modelSideNegCurvature κ a b θ ≤ modelSideNegCurvature κ a b φ ↔ θ ≤ φ := by
  constructor
  · intro h
    by_contra hn
    have hrev := modelSideNegCurvature_mono_angle hκ ha.le hb.le hφ.1 hθ.2 (le_of_not_ge hn)
    have heq := congrArg (comparisonAngleNegCurvature κ a b) (le_antisymm h hrev)
    rw [comparisonAngleNegCurvature_modelSide hκ ha hb hθ,
      comparisonAngleNegCurvature_modelSide hκ ha hb hφ] at heq
    exact hn heq.le
  · intro h
    exact modelSideNegCurvature_mono_angle hκ ha.le hb.le hθ.1 hφ.2 h

theorem comparisonAngleNegCurvature_le_iff_le_modelSide {κ a b c θ : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b)
    (hlower : |a - b| ≤ c) (hupper : c ≤ a + b)
    (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    comparisonAngleNegCurvature κ a b c ≤ θ ↔ c ≤ modelSideNegCurvature κ a b θ := by
  rw [← modelSideNegCurvature_le_iff_angle_le hκ ha hb
    (comparisonAngleNegCurvature_mem_Icc _ _ _ _) hθ,
    modelSideNegCurvature_comparisonAngle hκ ha hb hlower hupper]

end DifferentialGeometry.Geometry.Comparison.Toponogov
