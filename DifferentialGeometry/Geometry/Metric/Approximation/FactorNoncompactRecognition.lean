import DifferentialGeometry.Geometry.Comparison.FactorNoncompactRecognition
import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionFactorGeometry

set_option autoImplicit false

open Set Filter Metric
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v w
variable {X : ℕ → Type u} {Y : Type v} {Z : Type w}
variable [∀ i, MetricSpace (X i)] [MetricSpace Y] [MetricSpace Z]
variable {p : ∀ i, X i} {q : Y}

theorem PointedGHConverges.exists_line_or_ray_product_of_noncompact_factor
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
    (e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z))
    (hnot : ¬ IsCompact (univ : Set Z)) :
    (∃ F : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × ℝ),
      (F q).snd = 0 ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ F : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Ici (0 : ℝ)),
      ((F q).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) := by
  let := h.complete_space
  have hd := h.dimH_euclidean_factor_le hkn hcover e (e q).snd
  have hd' : dimH (univ : Set Z) ≤ (n - k : ℕ) := by
    simpa only [ENNReal.ofReal_natCast] using hd
  exact e.exists_line_or_ray_product_of_noncompact_factor hsegments hcomp
    (hd'.trans (by exact_mod_cast hcodim)) hnot q

theorem PointedGHConverges.exists_line_or_ray_product_of_growing_local_geometry
    [∀ i, CompleteSpace (X i)] [ProperSpace Y]
    (h : PointedGHConverges p q) {κ ρ : ℕ → ℝ} {n k : ℕ} (hn : 1 ≤ n)
    (hcodim : n - k ≤ 1)
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hdim : ∀ i, dimH (ball (p i) (ρ i)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (p i) (ρ i),
      ∃ Ω : Set (X i), IsOpen Ω ∧ fourPointComparison (κ i) Ω ∧ z ∈ Ω)
    (e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z))
    (hnot : ¬ IsCompact (univ : Set Z)) :
    (∃ F : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × ℝ),
      (F q).snd = 0 ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ F : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Ici (0 : ℝ)),
      ((F q).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) := by
  have hcover := polynomial_covering_of_growing_local_geometry p hn hcurves hκ hκzero hρ hdim hlocal
  have hkn := h.euclidean_rank_le_of_polynomial_covering hcover e (e q).snd
  exact h.exists_line_or_ray_product_of_noncompact_factor hkn hcodim hcover
    (h.exists_metric_segment_of_source_curves hcurves)
    (h.fourPointComparison_zero_of_eventual_comparison hκ hκzero (fun R hR =>
      eventual_fourPointComparison_of_growing_local_geometry p hcurves hκ hρ hdim hlocal hR)) e hnot

end GC.MetricGeometry
