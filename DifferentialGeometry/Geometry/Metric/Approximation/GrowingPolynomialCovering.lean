import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionGeometry
import DifferentialGeometry.Topology.MetricSpace.CeilCoveringBound

set_option autoImplicit false

open Set Metric Real Filter
open scoped Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u
variable {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, CompleteSpace (X i)]

theorem eventual_polynomial_nets_of_growing_local_geometry
    (p : ∀ i, X i) {κ ρ : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hdim : ∀ i, dimH (ball (p i) (ρ i)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (p i) (ρ i),
      ∃ Ω : Set (X i), IsOpen Ω ∧ fourPointComparison (κ i) Ω ∧ z ∈ Ω)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∀ᶠ i in atTop, ∃ T : Finset (X i),
      (T.card : ℝ) ≤ (2 + 4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R)) ^ n *
        ε ^ (-(n : ℝ)) ∧
      (∀ x ∈ T, dist x (p i) ≤ R) ∧
      ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ T, dist x y ≤ ε := by
  filter_upwards [eventual_internal_nets_of_growing_local_geometry p hn hcurves hκ hκzero
    hρ hdim hlocal hR hε] with i hi
  obtain ⟨T, hcard, hT, hnet⟩ := hi
  refine ⟨T, ?_, fun x hx => hT hx, fun x hx => ?_⟩
  · have hB : 0 ≤ 4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R) := by positivity
    exact (show (T.card : ℝ) ≤
      ((1 + Nat.ceil (4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R) / ε)) ^ n : ℕ) by
        exact_mod_cast hcard).trans (ceil_covering_bound_le_polynomial hB hε hεone n)
  · obtain ⟨y, hy, hxy⟩ := hnet x hx
    exact ⟨y, hy, hxy.le⟩

theorem polynomial_covering_of_growing_local_geometry
    (p : ∀ i, X i) {κ ρ : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hdim : ∀ i, dimH (ball (p i) (ρ i)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (p i) (ρ i),
      ∃ Ω : Set (X i), IsOpen Ω ∧ fourPointComparison (κ i) Ω ∧ z ∈ Ω) :
    ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ᶠ i in atTop, ∃ T : Finset (X i), (T.card : ℝ) ≤ C * ε ^ (-(n : ℝ)) ∧
          (∀ x ∈ T, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ T, dist x y ≤ ε := by
  intro R hR
  refine ⟨(2 + 4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R)) ^ n, by positivity, ?_⟩
  intro ε hε hεone
  exact eventual_polynomial_nets_of_growing_local_geometry p hn hcurves hκ hκzero hρ
    hdim hlocal hR hε hεone

end GC.MetricGeometry
