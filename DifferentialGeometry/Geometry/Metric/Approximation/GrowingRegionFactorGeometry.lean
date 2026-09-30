import DifferentialGeometry.Geometry.Metric.Approximation.GrowingPolynomialCovering
import DifferentialGeometry.Geometry.Metric.Approximation.FactorSplitting

set_option autoImplicit false

open Set Metric Real Filter
open scoped Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u v w
variable {X : ℕ → Type u} {Y : Type v} {Z : Type w}
variable [∀ i, MetricSpace (X i)] [∀ i, CompleteSpace (X i)] [MetricSpace Y] [MetricSpace Z]
variable {p : ∀ i, X i} {q : Y}

theorem PointedGHConverges.euclidean_factor_dimension_of_growing_local_geometry
    (h : PointedGHConverges p q) {κ ρ : ℕ → ℝ} {n k : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hdim : ∀ i, dimH (ball (p i) (ρ i)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (p i) (ρ i),
      ∃ Ω : Set (X i), IsOpen Ω ∧ fourPointComparison (κ i) Ω ∧ z ∈ Ω)
    (e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)) (z : Z) :
    k ≤ n ∧ dimH (univ : Set Z) ≤ ENNReal.ofReal ((n - k : ℕ) : ℝ) := by
  have hcover := polynomial_covering_of_growing_local_geometry p hn hcurves hκ hκzero hρ hdim hlocal
  have hkn := h.euclidean_rank_le_of_polynomial_covering hcover e z
  exact ⟨hkn, h.dimH_euclidean_factor_le hkn hcover e z⟩

theorem PointedGHConverges.exists_pointed_euclidean_of_growing_local_geometry [ProperSpace Y]
    (h : PointedGHConverges p q) {κ ρ : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hdim : ∀ i, dimH (ball (p i) (ρ i)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (p i) (ρ i),
      ∃ Ω : Set (X i), IsOpen Ω ∧ fourPointComparison (κ i) Ω ∧ z ∈ Ω)
    (e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin n) × Z)) (z : Z)
    (hq : e q = WithLp.toLp 2 (0, z)) :
    ∃ f : Y ≃ᵢ EuclideanSpace ℝ (Fin n), f q = 0 := by
  exact h.exists_pointed_isometryEquiv_euclidean
    (polynomial_covering_of_growing_local_geometry p hn hcurves hκ hκzero hρ hdim hlocal)
    (h.exists_metric_segment_of_source_curves hcurves) e z hq

theorem PointedGHConverges.exists_line_factor_of_growing_local_geometry [ProperSpace Y]
    (h : PointedGHConverges p q) {κ ρ : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hdim : ∀ i, dimH (ball (p i) (ρ i)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (p i) (ρ i),
      ∃ Ω : Set (X i), IsOpen Ω ∧ fourPointComparison (κ i) Ω ∧ z ∈ Ω)
    {γ : ℝ → Y} (hγ : Isometry γ) :
    ∃ (Z : Type v) (m : MetricSpace Z), letI := m
      ∃ (z : Z) (e : Y ≃ᵢ WithLp 2 (ℝ × Z)),
        (∀ t, e (γ t) = WithLp.toLp 2 (t, z)) ∧
        ProperSpace Z ∧ CompleteSpace Z ∧ fourPointComparison 0 (univ : Set Z) ∧
        (∀ a b : Z, ∃ f : Icc (0 : ℝ) 1 → Z,
          Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        dimH (univ : Set Z) ≤ ENNReal.ofReal ((n - 1 : ℕ) : ℝ) := by
  exact h.exists_isometryEquiv_real_prod_dimH_le hn
    (polynomial_covering_of_growing_local_geometry p hn hcurves hκ hκzero hρ hdim hlocal)
    (h.fourPointComparison_zero_of_eventual_comparison hκ hκzero (fun R hR =>
      eventual_fourPointComparison_of_growing_local_geometry p hcurves hκ hρ hdim hlocal hR))
    (h.exists_metric_segment_of_source_curves hcurves) hγ

end GC.MetricGeometry
