import DifferentialGeometry.Geometry.Comparison.LowDimensionalProducts
import DifferentialGeometry.Geometry.Comparison.LineSplitting

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem exists_product_model_of_line_dimH_le_two
    (hsegments : ∀ x y : X, ∃ f : unitInterval → X,
      Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ 2)
    {γ : ℝ → X} (hγ : Isometry γ) (p : X) :
    (∃ F : X ≃ᵢ ℝ, ∀ x, F x = lineCoordinate γ x) ∨
    (∃ F : X ≃ᵢ WithLp 2 (ℝ × ℝ), (F p).snd = 0 ∧ ∀ x, (F x).fst = lineCoordinate γ x) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ F : X ≃ᵢ WithLp 2 (ℝ × Ici (0 : ℝ)),
      ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = lineCoordinate γ x) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ a ∈ Icc (0 : ℝ) L,
      ∃ F : X ≃ᵢ WithLp 2 (ℝ × Icc (0 : ℝ) L),
        ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = lineCoordinate γ x) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ F : X ≃ᵢ WithLp 2 (ℝ × AddCircle L),
      (F p).snd = 0 ∧ ∀ x, (F x).fst = lineCoordinate γ x) := by
  simpa only [lineSplitting_fst] using
    (lineSplitting hcomp hγ hsegments).exists_product_model_of_real_splitting_dimH_le_two
      hsegments hcomp hdim p

end DifferentialGeometry.Geometry.Comparison.Toponogov
