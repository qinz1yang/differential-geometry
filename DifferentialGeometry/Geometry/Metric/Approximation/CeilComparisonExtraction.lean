import DifferentialGeometry.Geometry.Metric.Approximation.ComparisonLimit

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u
variable {X : ℕ → Type u} [∀ i, MetricSpace (X i)]

theorem exists_geodesic_pointedGHConverges_of_ceil_covering_and_comparison
    (p : ∀ i, X i) (n : ℕ) (B : ℝ → ℝ)
    (hB : ∀ R : ℝ, 0 < R → 0 ≤ B R)
    (hcover : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η →
      ∀ᶠ i in atTop, ∃ F : Finset (X i), F.card ≤ (1 + Nat.ceil (B R / η)) ^ n ∧
        (∀ x ∈ F, dist x (p i) ≤ R) ∧
        ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    (hcurves : ∀ i, ∀ a b : X i, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {κ : ℕ → ℝ} (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0))
    (hcompare : ∀ R : ℝ, 0 < R →
      ∀ᶠ i in atTop, fourPointComparison (κ i) (Metric.ball (p i) R)) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        dimH (univ : Set Y) ≤ n ∧ fourPointComparison 0 (univ : Set Y) ∧
        (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        (∀ a b z v : Y, ∀ t ∈ Icc (0 : ℝ) 1,
          dist a z = t * dist a b → dist z b = (1 - t) * dist a b →
          (1 - t) * dist v a ^ 2 + t * dist v b ^ 2 -
            t * (1 - t) * dist a b ^ 2 ≤ dist v z ^ 2) ∧
        ∀ R : ℝ, 0 < R → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ T : Finset Y,
          (T.card : ℝ) ≤ (2 + 4 * B (R + 1)) ^ n * δ ^ (-(n : ℝ)) ∧
          (∀ y ∈ T, dist y q ≤ R) ∧
          ∀ y : Y, dist y q ≤ R → ∃ z ∈ T, dist y z < δ := by
  have hnets : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N I : ℕ, ∀ i : ℕ, I ≤ i →
      ∃ F : Finset (X i), F.card ≤ N ∧ (∀ x ∈ F, dist x (p i) ≤ R) ∧
        ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η := by
    intro R hR η hη
    obtain ⟨I, hI⟩ := eventually_atTop.mp (hcover R hR η hη)
    exact ⟨(1 + Nat.ceil (B R / η)) ^ n, I, hI⟩
  obtain ⟨Y, m, q, φ, hφ, hproper, hconv⟩ :=
    exists_pointedGHConverges_of_eventual_finite_nets p hnets
  let := m
  let := hproper
  have hcover' (R : ℝ) (hR : 0 < R) (η : ℝ) (hη : 0 < η) :=
    hφ.tendsto_atTop.eventually (hcover R hR η hη)
  have hdim := hconv.dimH_le_of_ceil_covering n B hB (fun R hR η hη _ => hcover' R hR η hη)
  have hcomp : fourPointComparison 0 (univ : Set Y) :=
    hconv.fourPointComparison_zero_of_eventual_comparison (fun i => hκ (φ i))
      (hκzero.comp hφ.tendsto_atTop)
      (fun R hR => hφ.tendsto_atTop.eventually (hcompare R hR))
  refine ⟨Y, m, q, φ, hφ, inferInstance, hproper, hconv, hdim, hcomp,
    hconv.exists_metric_segment_of_source_curves (fun i => hcurves (φ i)), ?_, ?_⟩
  · intro a b z v t ht haz hzb
    exact quadratic_side_comparison_of_fourPointComparison hcomp
      (mem_univ a) (mem_univ b) (mem_univ z) (mem_univ v) ht haz hzb
  · intro R hR δ hδ hδone
    exact hconv.exists_internal_finset_net_of_ceil_covering n hR hδ hδone
      (hB (R + 1) (by linarith)) (hcover' (R + 1) (by linarith) (δ / 4) (by positivity))

end GC.MetricGeometry
