import DifferentialGeometry.Geometry.Comparison.OneDimensionalRecognition
import DifferentialGeometry.Geometry.Comparison.FactorGeometry

set_option autoImplicit false

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace IsometryEquiv

variable {X E Y : Type*} [MetricSpace X] [MetricSpace E] [MetricSpace Y]

theorem singleton_or_pointed_interval_charts_l2_product_factor [CompleteSpace X] [Nonempty Y]
    (e : X ≃ᵢ WithLp 2 (E × Y)) (u : E)
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X)) (hdim : dimH (univ : Set Y) ≤ 1) :
    Nonempty (Y ≃ᵢ PUnit) ∨ ∀ p : Y, ∃ r : ℝ, ∃ hr : 0 < r,
      (∃ e : Ioo (-r) r ≃ᵢ ball p r, (e ⟨0, by constructor <;> linarith⟩ : Y) = p) ∨
      (∃ e : Ico (0 : ℝ) r ≃ᵢ ball p r, (e ⟨0, le_rfl, hr⟩ : Y) = p) := by
  let := e.completeSpace_l2_product_factor u
  exact singleton_or_pointed_interval_charts_of_dimH_le_one
    (e.exists_segment_l2_product_factor u hsegments)
    (fourPointComparison_l2_product_factor hcomp e u) hdim

end IsometryEquiv
