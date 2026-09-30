import DifferentialGeometry.Geometry.Comparison.OriginalFactorGeometry
import DifferentialGeometry.Geometry.Comparison.FactorGlobalModels
import DifferentialGeometry.Geometry.Comparison.EuclideanFactorDimension

set_option autoImplicit false

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace IsometryEquiv

variable {X Z : Type*} [MetricSpace X] [CompleteSpace X] [MetricSpace Z]

theorem exists_product_model_of_real_splitting_dimH_le_two
    (hsegments : ∀ x y : X, ∃ f : unitInterval → X,
      Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ 2)
    (e : X ≃ᵢ WithLp 2 (ℝ × Z)) (p : X) :
    (∃ F : X ≃ᵢ ℝ, ∀ x, F x = (e x).fst) ∨
    (∃ F : X ≃ᵢ WithLp 2 (ℝ × ℝ), (F p).snd = 0 ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ F : X ≃ᵢ WithLp 2 (ℝ × Ici (0 : ℝ)),
      ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ a ∈ Icc (0 : ℝ) L,
      ∃ F : X ≃ᵢ WithLp 2 (ℝ × Icc (0 : ℝ) L),
        ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ F : X ≃ᵢ WithLp 2 (ℝ × AddCircle L),
      (F p).snd = 0 ∧ ∀ x, (F x).fst = (e x).fst) := by
  have hd := e.dimH_real_factor_le (by norm_num : 1 ≤ (2 : ℕ))
    (e.symm (WithLp.toLp 2 (0, (e p).snd))) (e p).snd (by simp)
    (polynomial_nets_of_nonnegative_comparison
      (arbitrarily_short_curves_of_metric_segments hsegments) hcomp (by norm_num) hdim _)
  have hd' : dimH (univ : Set Z) ≤ 1 := by simpa using hd
  exact e.exists_product_model_of_dimH_factor_le_one hsegments hcomp hd' p

end IsometryEquiv
