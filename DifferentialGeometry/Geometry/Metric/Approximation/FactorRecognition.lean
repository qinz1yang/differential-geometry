import DifferentialGeometry.Geometry.Metric.Approximation.FactorDimension
import DifferentialGeometry.Geometry.Comparison.FactorRecognition

set_option autoImplicit false

open Set Filter Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v w
variable {X : ℕ → Type u} {Y : Type v} {Z : Type w}
variable [∀ i, MetricSpace (X i)] [MetricSpace Y] [MetricSpace Z]
variable {p : ∀ i, X i} {q : Y}

theorem PointedGHConverges.singleton_or_pointed_interval_charts_factor
    (h : PointedGHConverges p q) {k n : ℕ} (hkn : k ≤ n) (hcodim : n - k ≤ 1)
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-(n : ℝ)) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set Y))
    (e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)) (z : Z) :
    Nonempty (Z ≃ᵢ PUnit) ∨ ∀ p : Z, ∃ r : ℝ, ∃ hr : 0 < r,
      (∃ e : Ioo (-r) r ≃ᵢ ball p r, (e ⟨0, by constructor <;> linarith⟩ : Z) = p) ∨
      (∃ e : Ico (0 : ℝ) r ≃ᵢ ball p r, (e ⟨0, le_rfl, hr⟩ : Z) = p) := by
  let := h.complete_space
  let : Nonempty Z := ⟨z⟩
  have hd := h.dimH_euclidean_factor_le hkn hcover e z
  have hd' : dimH (univ : Set Z) ≤ (n - k : ℕ) := by
    simpa only [ENNReal.ofReal_natCast] using hd
  exact e.singleton_or_pointed_interval_charts_l2_product_factor 0 hsegments hcomp
    (hd'.trans (by exact_mod_cast hcodim))

end GC.MetricGeometry
