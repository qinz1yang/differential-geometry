import DifferentialGeometry.Geometry.Metric.Approximation.ComparisonLimit
import DifferentialGeometry.Geometry.Comparison.LineSplitting

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v
variable {X : ℕ → Type u} {Y : Type v}
variable [∀ i, MetricSpace (X i)] [MetricSpace Y]
variable {p : ∀ i, X i} {q : Y} {κ : ℕ → ℝ}

theorem PointedGHConverges.exists_isometryEquiv_real_prod [ProperSpace Y]
    (h : PointedGHConverges p q) (hκ : ∀ i, 0 ≤ κ i)
    (hκzero : Tendsto κ atTop (𝓝 0))
    (hcompare : ∀ R : ℝ, 0 < R →
      ∀ᶠ i in atTop, fourPointComparison (κ i) (Metric.ball (p i) R))
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    {γ : ℝ → Y} (hγ : Isometry γ) :
    ∃ (Z : Type v) (m : MetricSpace Z), letI := m
      ∃ (z : Z) (e : Y ≃ᵢ WithLp 2 (ℝ × Z)),
        (∀ t, e (γ t) = WithLp.toLp 2 (t, z)) ∧
        ProperSpace Z ∧ CompleteSpace Z ∧ fourPointComparison 0 (univ : Set Z) ∧
        (∀ a b : Z, ∃ f : Icc (0 : ℝ) 1 → Z,
          Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        dimH (univ : Set Z) ≤ dimH (univ : Set Y) :=
  DifferentialGeometry.Geometry.Comparison.Toponogov.exists_isometryEquiv_real_prod
    (h.fourPointComparison_zero_of_eventual_comparison hκ hκzero hcompare) hγ hsegments

theorem exists_pointedGHConverges_with_line_splitting
    (p : ∀ i, X i) {d : ℝ} (hd : 0 ≤ d)
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-d) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    (hcurves : ∀ i, ∀ a b : X i, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0))
    (hcompare : ∀ R : ℝ, 0 < R →
      ∀ᶠ i in atTop, fourPointComparison (κ i) (Metric.ball (p i) R)) :
    ∃ (Y : Type) (m : MetricSpace Y), letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        dimH (univ : Set Y) ≤ ENNReal.ofReal d ∧
        fourPointComparison 0 (univ : Set Y) ∧
        (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y,
          Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        (∀ γ : ℝ → Y, Isometry γ →
          ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
            ∃ (z : Z) (e : Y ≃ᵢ WithLp 2 (ℝ × Z)),
              (∀ t, e (γ t) = WithLp.toLp 2 (t, z)) ∧
              ProperSpace Z ∧ CompleteSpace Z ∧ fourPointComparison 0 (univ : Set Z) ∧
              (∀ a b : Z, ∃ f : Icc (0 : ℝ) 1 → Z,
                Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
                ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
              dimH (univ : Set Z) ≤ ENNReal.ofReal d) := by
  obtain ⟨Y, m, q, φ, hφ, hproper, hconv, hdim, hcomp, hsegments, _⟩ :=
    exists_geodesic_pointedGHConverges_of_covering_and_comparison p hd hcover hcurves
      hκ hκzero hcompare
  let := m
  let := hproper
  refine ⟨Y, m, q, φ, hφ, hproper, hconv, hdim, hcomp, hsegments, ?_⟩
  intro γ hγ
  obtain ⟨Z, mZ, z, e, halign, hp, hc, hfour, hseg, hdimZ⟩ :=
    DifferentialGeometry.Geometry.Comparison.Toponogov.exists_isometryEquiv_real_prod
      hcomp hγ hsegments
  exact ⟨Z, mZ, z, e, halign, hp, hc, hfour, hseg, hdimZ.trans hdim⟩

end GC.MetricGeometry
