import DifferentialGeometry.Geometry.Metric.Approximation.FactorDimension
import DifferentialGeometry.Geometry.Metric.Approximation.LineSplitting

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v w
variable {X : ℕ → Type u} {Y : Type v} {Z : Type w}
variable [∀ i, MetricSpace (X i)] [MetricSpace Y] [MetricSpace Z]
variable {p : ∀ i, X i} {q : Y}

theorem PointedGHConverges.euclidean_rank_le_of_polynomial_covering
    (h : PointedGHConverges p q) {k n : ℕ}
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-(n : ℝ)) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    (e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)) (z : Z) : k ≤ n := by
  have hdim := h.dimH_le_of_polynomial_covering (by positivity : 0 ≤ (n : ℝ)) hcover
  have hk := (e.euclidean_rank_le_dimH z).trans hdim
  simpa only [ENNReal.ofReal_natCast, Nat.cast_le] using hk

theorem PointedGHConverges.exists_pointed_isometryEquiv_euclidean
    (h : PointedGHConverges p q) {k : ℕ}
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-(k : ℝ)) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)) (z : Z)
    (hq : e q = WithLp.toLp 2 (0, z)) :
    ∃ f : Y ≃ᵢ EuclideanSpace ℝ (Fin k), f q = 0 :=
  e.exists_pointed_isometryEquiv_euclidean_of_splitting q z hq hsegments
    (h.exists_polynomial_nets_at hcover q)

theorem PointedGHConverges.exists_isometryEquiv_real_prod_dimH_le [ProperSpace Y]
    (h : PointedGHConverges p q) {n : ℕ} (hn : 1 ≤ n)
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-(n : ℝ)) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    (hs : fourPointComparison 0 (univ : Set Y))
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
        dimH (univ : Set Z) ≤ ENNReal.ofReal ((n - 1 : ℕ) : ℝ) := by
  obtain ⟨Z, m, z, e, halign, hp, hc, hfour, hseg, _⟩ :=
    DifferentialGeometry.Geometry.Comparison.Toponogov.exists_isometryEquiv_real_prod hs hγ hsegments
  exact ⟨Z, m, z, e, halign, hp, hc, hfour, hseg, h.dimH_real_factor_le hn hcover e z⟩

theorem exists_pointedGHConverges_with_line_factor_dimension
    (p : ∀ i, X i) {n : ℕ} (hn : 1 ≤ n)
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-(n : ℝ)) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    (hcurves : ∀ i, ∀ a b : X i, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {κ : ℕ → ℝ} (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0))
    (hcompare : ∀ R : ℝ, 0 < R →
      ∀ᶠ i in atTop, fourPointComparison (κ i) (Metric.ball (p i) R)) :
    ∃ (Y : Type) (m : MetricSpace Y), letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        dimH (univ : Set Y) ≤ ENNReal.ofReal (n : ℝ) ∧
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
              dimH (univ : Set Z) ≤ ENNReal.ofReal ((n - 1 : ℕ) : ℝ)) := by
  obtain ⟨Y, m, q, φ, hφ, hproper, hconv, hdim, hcomp, hsegments, _⟩ :=
    exists_geodesic_pointedGHConverges_of_covering_and_comparison p (by positivity) hcover hcurves
      hκ hκzero hcompare
  let := m
  let := hproper
  have hcoverφ : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X (φ i)), (F.card : ℝ) ≤ C * η ^ (-(n : ℝ)) ∧
          (∀ x ∈ F, dist x (p (φ i)) ≤ R) ∧
          ∀ x : X (φ i), dist x (p (φ i)) ≤ R → ∃ y ∈ F, dist x y ≤ η := by
    intro R hR
    obtain ⟨C, hC, hc⟩ := hcover R hR
    exact ⟨C, hC, fun η hη hηone => hφ.tendsto_atTop.eventually (hc η hη hηone)⟩
  exact ⟨Y, m, q, φ, hφ, hproper, hconv, hdim, hcomp, hsegments,
    fun γ hγ => hconv.exists_isometryEquiv_real_prod_dimH_le hn hcoverφ hcomp hsegments hγ⟩

end GC.MetricGeometry
