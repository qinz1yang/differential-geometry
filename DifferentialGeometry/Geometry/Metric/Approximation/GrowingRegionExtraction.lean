import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionGeometry
import DifferentialGeometry.Geometry.Metric.Approximation.CeilComparisonExtraction

set_option autoImplicit false

open Set Metric Real Filter
open scoped Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u
variable {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, CompleteSpace (X i)]

theorem exists_pointed_limit_of_growing_local_geometry
    (p : ∀ i, X i) {κ ρ : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hdim : ∀ i, dimH (ball (p i) (ρ i)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (p i) (ρ i),
      ∃ Ω : Set (X i), IsOpen Ω ∧ fourPointComparison (κ i) Ω ∧ z ∈ Ω) :
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
          (T.card : ℝ) ≤
            (2 + 16 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * (R + 1))) ^ n *
              δ ^ (-(n : ℝ)) ∧
          (∀ y ∈ T, dist y q ≤ R) ∧
          ∀ y : Y, dist y q ≤ R → ∃ z ∈ T, dist y z < δ := by
  let B : ℝ → ℝ := fun R => 4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R)
  have hB : ∀ R : ℝ, 0 < R → 0 ≤ B R := by
    intro R hR
    dsimp [B]
    positivity
  have hcover : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η →
      ∀ᶠ i in atTop, ∃ F : Finset (X i), F.card ≤ (1 + Nat.ceil (B R / η)) ^ n ∧
        (∀ x ∈ F, dist x (p i) ≤ R) ∧
        ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η := by
    intro R hR η hη
    filter_upwards [eventual_internal_nets_of_growing_local_geometry p hn hcurves hκ hκzero
      hρ hdim hlocal hR hη] with i hi
    obtain ⟨T, hcard, hT, hnet⟩ := hi
    refine ⟨T, hcard, fun x hx => hT hx, fun x hx => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    exact ⟨y, hy, hxy.le⟩
  obtain ⟨Y, m, q, φ, hφ, hcomplete, hproper, hconv, hdimY, hcomp, hsegments, hside, hnets⟩ :=
    exists_geodesic_pointedGHConverges_of_ceil_covering_and_comparison p n B hB hcover hcurves
      hκ hκzero (fun R hR =>
        eventual_fourPointComparison_of_growing_local_geometry p hcurves hκ hρ hdim hlocal hR)
  let := m
  refine ⟨Y, m, q, φ, hφ, hcomplete, hproper, hconv, hdimY, hcomp, hsegments, hside, ?_⟩
  intro R hR δ hδ hδone
  obtain ⟨T, hcard, hT, hnet⟩ := hnets R hR δ hδ hδone
  refine ⟨T, ?_, hT, hnet⟩
  have heq : 2 + 4 * B (R + 1) =
      2 + 16 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * (R + 1)) := by
    dsimp [B]
    ring
  rwa [heq] at hcard

theorem exists_pointed_limit_of_growing_intrinsic_local_geometry
    (p : ∀ i, X i) {κ ρ : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hρpos : ∀ i, 0 < ρ i)
    (hdim : ∀ i, dimH (ball (p i) (ρ i)) ≤ n)
    (hlocal : ∀ i, ∀ z : ball (p i) (ρ i), ∃ Ω : Set (ball (p i) (ρ i)),
      @IsOpen (ball (p i) (ρ i))
        (intrinsicBallMetricSpace (hcurves i) (p i) (hρpos i)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball (p i) (ρ i))
        (intrinsicBallMetricSpace (hcurves i) (p i) (hρpos i)) (κ i) Ω ∧ z ∈ Ω) :
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
          (T.card : ℝ) ≤
            (2 + 16 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * (R + 1))) ^ n *
              δ ^ (-(n : ℝ)) ∧
          (∀ y ∈ T, dist y q ≤ R) ∧
          ∀ y : Y, dist y q ≤ R → ∃ z ∈ T, dist y z < δ := by
  apply exists_pointed_limit_of_growing_local_geometry p hn hcurves hκ hκzero hρ hdim
  intro i z hz
  exact (exists_local_fourPointComparison_intrinsicBall_iff (hcurves i) (p i)
    (hρpos i) ⟨z, hz⟩).mp (hlocal i ⟨z, hz⟩)

end GC.MetricGeometry
