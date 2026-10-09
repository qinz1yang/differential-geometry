import DifferentialGeometry.Geometry.Metric.Approximation.ApproximateFactorCompactness
import DifferentialGeometry.Geometry.Metric.Approximation.ApproximateSources
import DifferentialGeometry.Geometry.Metric.Approximation.ProductApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.PointedIsometry

open Filter
open scoped Topology

namespace GC.MetricGeometry.PointedGHConverges

universe u v w z
variable {X : ℕ → Type u} {E : Type v} {Z : ℕ → Type w} {Y : Type z}
variable [∀ i, MetricSpace (X i)] [MetricSpace E] [∀ i, MetricSpace (Z i)]
variable [MetricSpace Y] [ProperSpace E] [ProperSpace Y]
variable {p : ∀ i, X i} {a : E} {q : Y} {b : ∀ i, Z i} {δ : ℕ → ℝ}

theorem exists_product_isometry_of_approximate_products
    (h : PointedGHConverges p q)
    (f : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace W ∧ CompleteSpace W ∧
        PointedGHConverges (fun i => b (φ i)) w ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        ∃ e : Y ≃ᵢ WithLp 2 (E × W), e q = WithLp.toLp 2 (a, w) := by
  obtain ⟨W, m, w, φ, hφ, hp, hc, hz, hx⟩ :=
    h.exists_factor_limit_of_approximate_products f hδ
  let := m
  let := hp
  let := hc
  have hprod := hz.l2Product a
  have hsource : PointedGHConverges (fun i => p (φ i)) (WithLp.toLp 2 (a, w)) :=
    hprod.of_approximate_sources (fun i => f (φ i)) (hδ.comp hφ.tendsto_atTop)
  obtain ⟨e, he⟩ := hx.exists_isometryEquiv hsource
  exact ⟨W, m, w, φ, hφ, hp, hc, hz, hx, e, he⟩

end GC.MetricGeometry.PointedGHConverges
