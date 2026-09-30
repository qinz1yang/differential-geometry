import DifferentialGeometry.Geometry.Metric.Approximation.ControlledProductLimit
import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionFactorGeometry
import DifferentialGeometry.Geometry.Comparison.FactorGeometry

set_option autoImplicit false

open Set Metric Real Filter
open scoped Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u v w
variable {X : ℕ → Type u} {Y : Type v} {Z : ℕ → Type w}
variable [∀ i, MetricSpace (X i)] [∀ i, CompleteSpace (X i)] [MetricSpace Y] [ProperSpace Y]
variable [∀ i, MetricSpace (Z i)] {p : ∀ i, X i} {q : Y} {b : ∀ i, Z i}

theorem PointedGHConverges.exists_controlled_product_of_growing_local_geometry
    (h : PointedGHConverges p q) {κ ρ δ : ℕ → ℝ} {n k : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hdim : ∀ i, dimH (ball (p i) (ρ i)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (p i) (ρ i),
      ∃ Ω : Set (X i), IsOpen Ω ∧ fourPointComparison (κ i) Ω ∧ z ∈ Ω)
    (f : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    k ≤ n ∧ dimH (univ : Set Y) ≤ n ∧ fourPointComparison 0 (univ : Set Y) ∧
    (∀ a b : Y, ∃ c : Icc (0 : ℝ) 1 → Y, Continuous c ∧
      c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (c s) (c t) = dist a b * dist s t) ∧
    ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace W ∧ CompleteSpace W ∧
        PointedGHConverges (fun i => b (φ i)) w ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        fourPointComparison 0 (univ : Set W) ∧
        (∀ a b : W, ∃ c : Icc (0 : ℝ) 1 → W, Continuous c ∧
          c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (c s) (c t) = dist a b * dist s t) ∧
        dimH (univ : Set W) ≤ ENNReal.ofReal ((n - k : ℕ) : ℝ) ∧
        ∃ e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × W),
          e q = WithLp.toLp 2 (0, w) ∧
          ∃ R ε : ℕ → ℝ, Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
            ∃ g : ∀ i, PointedBallApprox (p (φ i)) q (R i) (ε i),
              ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
                ∀ x : BallCarrier (p (φ i)) (R i), dist x.val (p (φ i)) ≤ S →
                  dist (((f (φ i)).toFun x.val).fst) ((e ((g i).toFun x)).fst) < η := by
  have hcover := polynomial_covering_of_growing_local_geometry p hn hcurves hκ hκzero hρ hdim hlocal
  have hdimY : dimH (univ : Set Y) ≤ n := by
    simpa only [ENNReal.ofReal_natCast] using
      h.dimH_le_of_polynomial_covering (by positivity : 0 ≤ (n : ℝ)) hcover
  have hcomp := h.fourPointComparison_zero_of_eventual_comparison hκ hκzero (fun R hR =>
    eventual_fourPointComparison_of_growing_local_geometry p hcurves hκ hρ hdim hlocal hR)
  have hseg := h.exists_metric_segment_of_source_curves hcurves
  obtain ⟨W, m, w, φ, hφ, hp, hc, hz, hx, e, he, R, ε, hR, heps, g, hg⟩ :=
    h.exists_controlled_product_limit_of_approximate_products f hδ
  let := m
  have hkn := h.euclidean_rank_le_of_polynomial_covering hcover e w
  have hdimW := h.dimH_euclidean_factor_le hkn hcover e w
  exact ⟨hkn, hdimY, hcomp, hseg, W, m, w, φ, hφ, hp, hc, hz, hx,
    fourPointComparison_l2_product_factor hcomp e 0,
    e.exists_segment_l2_product_factor 0 hseg, hdimW, e, he, R, ε, hR, heps, g, hg⟩

theorem PointedGHConverges.exists_controlled_product_of_reciprocal_local_geometry
    (h : PointedGHConverges p q) {δ : ℕ → ℝ} {n k : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hdim : ∀ i, dimH (ball (p i) ((δ i)⁻¹)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (p i) ((δ i)⁻¹),
      ∃ Ω : Set (X i), IsOpen Ω ∧ fourPointComparison (δ i) Ω ∧ z ∈ Ω)
    (f : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    k ≤ n ∧ dimH (univ : Set Y) ≤ n ∧ fourPointComparison 0 (univ : Set Y) ∧
    (∀ a b : Y, ∃ c : Icc (0 : ℝ) 1 → Y, Continuous c ∧
      c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (c s) (c t) = dist a b * dist s t) ∧
    ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace W ∧ CompleteSpace W ∧
        PointedGHConverges (fun i => b (φ i)) w ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        fourPointComparison 0 (univ : Set W) ∧
        (∀ a b : W, ∃ c : Icc (0 : ℝ) 1 → W, Continuous c ∧
          c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (c s) (c t) = dist a b * dist s t) ∧
        dimH (univ : Set W) ≤ ENNReal.ofReal ((n - k : ℕ) : ℝ) ∧
        ∃ e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × W),
          e q = WithLp.toLp 2 (0, w) ∧
          ∃ R ε : ℕ → ℝ, Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
            ∃ g : ∀ i, PointedBallApprox (p (φ i)) q (R i) (ε i),
              ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
                ∀ x : BallCarrier (p (φ i)) (R i), dist x.val (p (φ i)) ≤ S →
                  dist (((f (φ i)).toFun x.val).fst) ((e ((g i).toFun x)).fst) < η := by
  have hpos (i : ℕ) : 0 < δ i := (f i).error_pos
  have hwithin : Tendsto δ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδ, Eventually.of_forall hpos⟩
  have hradius : Tendsto (fun i => (δ i)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hwithin
  exact h.exists_controlled_product_of_growing_local_geometry hn hcurves
    (fun i => (hpos i).le) hδ hradius hdim hlocal f hδ

theorem PointedGHConverges.exists_controlled_product_of_eventual_reciprocal_local_geometry
    (h : PointedGHConverges p q) (I : ℕ) {δ : ℕ → ℝ} {n k : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hdim : ∀ i, dimH (ball (p i) ((δ i)⁻¹)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (p i) ((δ i)⁻¹),
      ∃ Ω : Set (X i), IsOpen Ω ∧ fourPointComparison (δ i) Ω ∧ z ∈ Ω)
    (f : ∀ i, I ≤ i → KleinerLottApprox (p i) (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    k ≤ n ∧ dimH (univ : Set Y) ≤ n ∧ fourPointComparison 0 (univ : Set Y) ∧
    (∀ a b : Y, ∃ c : Icc (0 : ℝ) 1 → Y, Continuous c ∧
      c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (c s) (c t) = dist a b * dist s t) ∧
    ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ ∃ hφI : ∀ i, I ≤ φ i, ProperSpace W ∧ CompleteSpace W ∧
        PointedGHConverges (fun i => b (φ i)) w ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        fourPointComparison 0 (univ : Set W) ∧
        (∀ a b : W, ∃ c : Icc (0 : ℝ) 1 → W, Continuous c ∧
          c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (c s) (c t) = dist a b * dist s t) ∧
        dimH (univ : Set W) ≤ ENNReal.ofReal ((n - k : ℕ) : ℝ) ∧
        ∃ e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × W),
          e q = WithLp.toLp 2 (0, w) ∧
          ∃ R ε : ℕ → ℝ, Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
            ∃ g : ∀ i, PointedBallApprox (p (φ i)) q (R i) (ε i),
              ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
                ∀ x : BallCarrier (p (φ i)) (R i), dist x.val (p (φ i)) ≤ S →
                  dist (((f (φ i) (hφI i)).toFun x.val).fst) ((e ((g i).toFun x)).fst) < η := by
  have hshift : StrictMono (fun j : ℕ => j + I) := by
    intro a b hab
    exact Nat.add_lt_add_right hab I
  have hs : PointedGHConverges (fun j => p (j + I)) q := h.subsequence hshift
  obtain ⟨hkn, hdimY, hcompY, hsegY, W, m, w, ψ, hψ, hp, hc, hz, hx,
      hcompW, hsegW, hdimW, e, he, R, ε, hR, heps, g, hg⟩ :=
    hs.exists_controlled_product_of_reciprocal_local_geometry hn
      (fun j => hcurves (j + I)) (fun j => hdim (j + I)) (fun j => hlocal (j + I))
      (fun j => f (j + I) (by omega)) (hδ.comp hshift.tendsto_atTop)
  let := m
  let φ : ℕ → ℕ := fun i => ψ i + I
  have hφ : StrictMono φ := hshift.comp hψ
  have hφI (i : ℕ) : I ≤ φ i := by dsimp [φ]; omega
  exact ⟨hkn, hdimY, hcompY, hsegY, W, m, w, φ, hφ, hφI,
    hp, hc, hz, hx, hcompW, hsegW, hdimW, e, he, R, ε, hR, heps, g, hg⟩

end GC.MetricGeometry
