import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianExtraction
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Aligned

set_option autoImplicit false
open Set Metric Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem PointedRiemannianSeq.eventually_internal_nets_of_sectional_lower_bound
    (X : PointedRiemannianSeq.{u, uE, uH} I)
    (hcomplete : ∀ i, MetricComplete (X.obj i))
    (hconn : ∀ i, ConnectedSpace (X.obj i).M)
    {κ ρ : ℕ → ℝ}
    (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (X.obj i).metric (X.obj i).basepoint (ρ i),
      SectionalBoundedBelowAt (X.obj i).metric y (-κ i))
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    let : ∀ i, MetricSpace (X.obj i).M := fun i =>
      (properMetricOn (X.obj i) (hcomplete i) (hconn i)).alignedMetricSpace (X.obj i)
    ∀ᶠ i in atTop, ∃ T : Finset (X.obj i).M,
      T.card ≤ (1 + ⌈4 * (2 : ℝ) ^ 2 * Real.sqrt (Module.finrank ℝ E) *
        Real.sinh (2 * R) / ε⌉₊) ^ Module.finrank ℝ E ∧
      (T : Set (X.obj i).M) ⊆ closedBall (X.obj i).basepoint R ∧
      ∀ x ∈ closedBall (X.obj i).basepoint R, ∃ y ∈ T, dist x y < ε := by
  let P := fun i => properMetricOn (X.obj i) (hcomplete i) (hconn i)
  let : ∀ i, MetricSpace (X.obj i).M := fun i => (P i).alignedMetricSpace (X.obj i)
  have : ∀ i, ProperSpace (X.obj i).M := fun i => (P i).properSpace_aligned (X.obj i)
  have : ∀ i, CompleteSpace (X.obj i).M := fun i => inferInstance
  have hmetric (i : ℕ) (a b : (X.obj i).M) :
      riemannianEDistOf (X.obj i).metric a b = ENNReal.ofReal (dist a b) := (P i).realizes a b
  have hsec' (i : ℕ) (y : (X.obj i).M) (hy : y ∈ ball (X.obj i).basepoint (ρ i)) :
      SectionalBoundedBelowAt (X.obj i).metric y (-κ i) := by
    apply hsec i y
    change riemannianEDistOf (X.obj i).metric (X.obj i).basepoint y < ENNReal.ofReal (ρ i)
    rw [hmetric, dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff (dist_nonneg.trans_lt hy)).mpr hy
  exact eventual_internal_nets_of_growing_sectional_lower_bound
    (fun i => (X.obj i).metric) hmetric (fun i => (X.obj i).basepoint) hκzero hρ hsec' hR hε

theorem PointedRiemannianSeq.exists_pointed_limit_of_sectional_lower_bound
    (X : PointedRiemannianSeq.{u, uE, uH} I)
    (hcomplete : ∀ i, MetricComplete (X.obj i))
    (hconn : ∀ i, ConnectedSpace (X.obj i).M)
    {κ ρ : ℕ → ℝ}
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (X.obj i).metric (X.obj i).basepoint (ρ i),
      SectionalBoundedBelowAt (X.obj i).metric y (-κ i)) :
    let : ∀ i, MetricSpace (X.obj i).M := fun i =>
      (properMetricOn (X.obj i) (hcomplete i) (hconn i)).alignedMetricSpace (X.obj i)
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => (X.obj (φ i)).basepoint) q ∧
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
  let P := fun i => properMetricOn (X.obj i) (hcomplete i) (hconn i)
  let : ∀ i, MetricSpace (X.obj i).M := fun i => (P i).alignedMetricSpace (X.obj i)
  have : ∀ i, ProperSpace (X.obj i).M := fun i => (P i).properSpace_aligned (X.obj i)
  have : ∀ i, CompleteSpace (X.obj i).M := fun i => inferInstance
  have hmetric (i : ℕ) (a b : (X.obj i).M) :
      riemannianEDistOf (X.obj i).metric a b = ENNReal.ofReal (dist a b) := (P i).realizes a b
  have hsec' (i : ℕ) (y : (X.obj i).M) (hy : y ∈ ball (X.obj i).basepoint (ρ i)) :
      SectionalBoundedBelowAt (X.obj i).metric y (-κ i) := by
    apply hsec i y
    change riemannianEDistOf (X.obj i).metric (X.obj i).basepoint y < ENNReal.ofReal (ρ i)
    rw [hmetric, dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff (dist_nonneg.trans_lt hy)).mpr hy
  exact exists_pointed_limit_of_growing_sectional_lower_bound
    (fun i => (X.obj i).metric) hmetric (fun i => (X.obj i).basepoint) hκ hκzero hρ hsec'

end DifferentialGeometry.CheegerGromovCompactness
