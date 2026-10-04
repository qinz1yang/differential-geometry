import DifferentialGeometry.Geometry.Comparison.RiemannianCovering
import DifferentialGeometry.Geometry.Metric.Approximation.CeilComparisonExtraction
import Mathlib.Order.Filter.AtTopBot.Tendsto

set_option autoImplicit false
open Set Metric Filter DifferentialGeometry
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, T2Space (TangentBundle I (X i))]
  [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

theorem eventual_internal_nets_of_growing_sectional_lower_bound
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) {κ ρ : ℕ → ℝ}
    (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hsec : ∀ i, ∀ y ∈ ball (p i) (ρ i), SectionalBoundedBelowAt (g i) y (-κ i))
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∃ T : Finset (X i),
      T.card ≤ (1 + ⌈4 * (2 : ℝ) ^ 2 * Real.sqrt (Module.finrank ℝ E) *
        Real.sinh (2 * R) / ε⌉₊) ^ Module.finrank ℝ E ∧
      (T : Set (X i)) ⊆ closedBall (p i) R ∧
      ∀ x ∈ closedBall (p i) R, ∃ y ∈ T, dist x y < ε := by
  filter_upwards [hκzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hρ.eventually (eventually_gt_atTop (8 * R))] with i hki hri
  exact exists_closedBall_net_of_sectional_lower_bound (g i) (hmetric i) (p i)
    hki.le hR hε (fun y hy => hsec i y (ball_subset_ball hri.le hy))

theorem exists_pointed_limit_of_growing_sectional_lower_bound
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) {κ ρ : ℕ → ℝ}
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hsec : ∀ i, ∀ y ∈ ball (p i) (ρ i), SectionalBoundedBelowAt (g i) y (-κ i)) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        dimH (univ : Set Y) ≤ Module.finrank ℝ E ∧ fourPointComparison 0 (univ : Set Y) ∧
        (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        (∀ a b z v : Y, ∀ t ∈ Icc (0 : ℝ) 1,
          dist a z = t * dist a b → dist z b = (1 - t) * dist a b →
          (1 - t) * dist v a ^ 2 + t * dist v b ^ 2 -
            t * (1 - t) * dist a b ^ 2 ≤ dist v z ^ 2) ∧
        ∀ R : ℝ, 0 < R → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ T : Finset Y,
          (T.card : ℝ) ≤
            (2 + 64 * Real.sqrt (Module.finrank ℝ E) * Real.sinh (2 * (R + 1))) ^
              Module.finrank ℝ E * δ ^ (-(Module.finrank ℝ E : ℝ)) ∧
          (∀ y ∈ T, dist y q ≤ R) ∧
          ∀ y : Y, dist y q ≤ R → ∃ z ∈ T, dist y z < δ := by
  let B : ℝ → ℝ := fun R =>
    4 * (2 : ℝ) ^ 2 * Real.sqrt (Module.finrank ℝ E) * Real.sinh (2 * R)
  have hB : ∀ R : ℝ, 0 < R → 0 ≤ B R := by
    intro R hR
    dsimp [B]
    positivity
  have hcover : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η →
      ∀ᶠ i in atTop, ∃ F : Finset (X i),
        F.card ≤ (1 + Nat.ceil (B R / η)) ^ Module.finrank ℝ E ∧
        (∀ x ∈ F, dist x (p i) ≤ R) ∧
        ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η := by
    intro R hR η hη
    filter_upwards [eventual_internal_nets_of_growing_sectional_lower_bound
      g hmetric p hκzero hρ hsec hR hη] with i hi
    obtain ⟨T, hcard, hT, hnet⟩ := hi
    refine ⟨T, hcard, fun x hx => hT hx, fun x hx => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    exact ⟨y, hy, hxy.le⟩
  have hcurves := fun i (a b : X i) (ε : ℝ) (hε : 0 < ε) =>
    DifferentialGeometry.Geometry.Metric.exists_arbitrarily_short_riemannian_curve
      (g i) (hmetric i) a b hε
  have hcompare : ∀ R : ℝ, 0 < R →
      ∀ᶠ i in atTop, fourPointComparison (κ i) (ball (p i) R) := by
    intro R _
    filter_upwards [hρ.eventually (eventually_gt_atTop (8 * R))] with i hri
    exact fourPointComparison_of_sectional_lower_bound_on_eight_ball
      (g i) (hmetric i) (p i) (hκ i)
      (fun y hy => hsec i y (ball_subset_ball hri.le hy))
  obtain ⟨Y, m, q, φ, hφ, hcomplete, hproper, hconv, hdimY, hcomp, hsegments, hside, hnets⟩ :=
    exists_geodesic_pointedGHConverges_of_ceil_covering_and_comparison
      p (Module.finrank ℝ E) B hB hcover hcurves hκ hκzero hcompare
  let := m
  refine ⟨Y, m, q, φ, hφ, hcomplete, hproper, hconv, hdimY, hcomp, hsegments, hside, ?_⟩
  intro R hR δ hδ hδone
  obtain ⟨T, hcard, hT, hnet⟩ := hnets R hR δ hδ hδone
  refine ⟨T, ?_, hT, hnet⟩
  have heq : 2 + 4 * B (R + 1) =
      2 + 64 * Real.sqrt (Module.finrank ℝ E) * Real.sinh (2 * (R + 1)) := by
    dsimp [B]
    ring
  rwa [heq] at hcard

end GC.MetricGeometry
