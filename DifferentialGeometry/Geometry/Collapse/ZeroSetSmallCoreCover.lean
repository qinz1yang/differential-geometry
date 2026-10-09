import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Topology.MetricSpace.ZeroSetSmallCoreCover

/-!
# LC64 on a closed Riemannian manifold

The metric kernel `Metric.exists_zero_set_small_core_cover`
(`Topology/MetricSpace/ZeroSetSmallCoreCover.lean`) applied to the distance of a smooth metric `g`
on a compact connected manifold (`inducedMetricSpace g`). The scale `ρ` is any positive function
continuous for the manifold topology and the radius assignment `r` is fixed once between `T ρ` and
`U ρ`; the set `Z` is arbitrary (in the application, the LC16 zero stratum). All balls are
`g`-balls and all distances are `g`-distances; no metric structure occurs in the statement.
-/

set_option autoImplicit false
noncomputable section
open Bundle Set
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **LC64 for a smooth metric on a compact connected manifold.** Finitely many maximal
candidate centers (LC62) with disjoint `g`-balls meeting `Z`, the neighboring radius and
scale-ratio bounds on the closed `g`-balls of ten radii, the cover of `Z` by five-radius balls and,
under the closed annular exclusion at every selected center, the cover by the open tenth-radius
`g`-balls. -/
theorem exists_zero_set_small_core_cover_riemannianBallOf [T3Space M] [ConnectedSpace M]
    [CompactSpace M] (g : SmoothRiemannianMetric I M) (Z : Set M) (r ρ : M → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ p, 0 < ρ p) {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U)
    (hlower : ∀ p, T * ρ p ≤ r p) (hupper : ∀ p, r p ≤ U * ρ p) :
    ∃ J : Set M, J.Finite ∧
      (∀ i ∈ J, (riemannianBallOf g i (r i) ∩ Z).Nonempty ∧
        ∀ q, (riemannianBallOf g q (r q) ∩ Z).Nonempty →
          riemannianBallOf g i (r i) ⊆ riemannianBallOf g q (r q) → r q ≤ 2 * r i) ∧
      J.PairwiseDisjoint (fun i => riemannianBallOf g i (r i)) ∧
      (∀ i ∈ J, ∀ q, (riemannianEDistOf (I := I) g i q).toReal ≤ 10 * r i →
        r q ≤ 20 * r i ∧ T / 20 ≤ r i / ρ q) ∧
      Z ⊆ ⋃ i ∈ J, riemannianBallOf g i (5 * r i) ∧
      ((∀ i ∈ J, ∀ z ∈ Z, ¬ (r i / 10 ≤ (riemannianEDistOf (I := I) g i z).toReal ∧
          (riemannianEDistOf (I := I) g i z).toReal ≤ 10 * r i)) →
        Z ⊆ ⋃ i ∈ J, riemannianBallOf g i (r i / 10)) := by
  let := inducedMetricSpace g
  have h := Metric.exists_zero_set_small_core_cover Z r ρ hρ hρpos hT hTU hlower hupper
  simp only [inducedMetricSpace_ball g, inducedMetricSpace_dist g] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
