import DifferentialGeometry.Geometry.Metric.Approximation.FactorDimension
import DifferentialGeometry.Geometry.Comparison.FactorEndpointRecognition

set_option autoImplicit false

open Set Filter Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v w
variable {X : ℕ → Type u} {Y : Type v} {Z : Type w}
variable [∀ i, MetricSpace (X i)] [MetricSpace Y] [MetricSpace Z]
variable {p : ∀ i, X i} {q : Y}

theorem PointedGHConverges.exists_interval_or_ray_product_of_factor_endpoint [Nontrivial Z]
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
    (e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)) {w : Z} (hend : ∀ x y : Z, dist x w + dist w y = dist x y → x = w ∨ y = w) :
    (∃ L : ℝ, 0 < L ∧ ∃ F : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Icc (0 : ℝ) L),
      ∀ x, (F x).fst = (e x).fst ∧ ((F x).snd : ℝ) = dist w (e x).snd) ∨
    (∃ F : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Ici (0 : ℝ)),
      ∀ x, (F x).fst = (e x).fst ∧ ((F x).snd : ℝ) = dist w (e x).snd) := by
  let := h.complete_space
  have hd := h.dimH_euclidean_factor_le hkn hcover e w
  have hd' : dimH (univ : Set Z) ≤ (n - k : ℕ) := by
    simpa only [ENNReal.ofReal_natCast] using hd
  exact e.exists_interval_or_ray_product_of_factor_endpoint 0 hsegments hcomp
    (hd'.trans (by exact_mod_cast hcodim)) hend

theorem PointedGHConverges.exists_interval_or_ray_product_of_factor_half_interval_chart [Nontrivial Z]
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
    (e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)) {w : Z} {r : ℝ} (hr : 0 < r) (f : Ico (0 : ℝ) r ≃ᵢ ball w r)
    (hf : (f ⟨0, le_rfl, hr⟩ : Z) = w) :
    (∃ L : ℝ, 0 < L ∧ ∃ F : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Icc (0 : ℝ) L),
      ∀ x, (F x).fst = (e x).fst ∧ ((F x).snd : ℝ) = dist w (e x).snd) ∨
    (∃ F : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Ici (0 : ℝ)),
      ∀ x, (F x).fst = (e x).fst ∧ ((F x).snd : ℝ) = dist w (e x).snd) := by
  apply h.exists_interval_or_ray_product_of_factor_endpoint hkn hcodim hcover hsegments hcomp e
  exact metric_endpoint_of_pointed_half_interval_chart
    (e.exists_segment_l2_product_factor 0 hsegments) hr f hf

end GC.MetricGeometry
