import DifferentialGeometry.Geometry.Metric.Approximation.UniformPairedPacket
import DifferentialGeometry.Geometry.Comparison.RiemannianFourPoint
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Aligned

set_option autoImplicit false

open Set Metric Filter
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

open scoped Manifold ContDiff ENNReal
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian

universe u v

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, SigmaCompactSpace (X i)]
  [∀ i, CompleteSpace (X i)] {Y : Type v} [MetricSpace Y]
  {ι : Type*} [Finite ι]

theorem exists_uniform_lifted_packet_of_growing_sectional_lower_bound
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {p : ∀ i, X i} {x : Y} (hconv : PointedGHConverges p x)
    {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop atTop)
    (hsec : ∀ i, ∀ y ∈ ball (p i) (ρ i), SectionalBoundedBelowAt (g i) y (-((ρ i)⁻¹ ^ 2)))
    (c : Option (ι × Bool) → Y) (hc : Function.Injective c)
    (hq : dist (c none) x < 1 / 4) {δ : ℝ} (hδ : 0 < δ)
    (hpacket : PairedComparisonPacket (δ / 2) {c none}
      (fun j => c (some (j, true))) (fun j => c (some (j, false)))) :
    ∃ a A r R : ℝ, 0 < a ∧ a ≤ A ∧ 0 < r ∧ r < 1 / 4 ∧ 2 < R ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
        256 * R < ρ i ∧ ∃ ε : ℝ, 0 < ε ∧ ε < η ∧
        ∃ f : PointedBallApprox (p i) x R ε,
        ∃ z : Option (ι × Bool) → BallCarrier (p i) R,
          Function.Injective z ∧
          (∀ j, dist (f.toFun (z j)) (c j) < η) ∧
          (∀ j k, |dist (z j).val (z k).val - dist (c j) (c k)| < η) ∧
          dist (z none).val (p i) < 1 / 2 ∧
          (∀ j, (z j).val ∈ ball (p i) R) ∧
          ball (z none).val (2 * r) ⊆ ball (p i) R ∧
          fourPointComparison 1 (ball (p i) R) ∧
          PairedComparisonPacket δ (ball (z none).val (2 * r))
            (fun j => (z (some (j, true))).val) (fun j => (z (some (j, false))).val) ∧
          (∀ w ∈ ball (z none).val (2 * r), ∀ j,
            dist w (z (some j)).val ∈ Icc a A) ∧
          IsComplete (closedBall (z none).val r) := by
  have hcompare (R : ℝ) (hR : 0 < R) :
      ∀ᶠ i in atTop, fourPointComparison 1 (ball (p i) R) := by
    filter_upwards [hρ.eventually (eventually_gt_atTop (256 * R)),
      hρ.eventually (eventually_gt_atTop 1)] with i hi hione
    apply fourPointComparison_of_sectional_lower_bound_on_eight_ball
      (g i) (hmetric i) (p i) (by norm_num)
    intro y hy
    have hcurv := hsec i y (ball_subset_ball (show 8 * R ≤ ρ i by linarith) hy)
    apply hcurv.mono
    have hinv : (ρ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hione.le
    have hpow : (ρ i)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (by linarith)) hinv
    linarith
  obtain ⟨a, A, r, R, ha, haA, hr, hrquarter, hR, hpacket'⟩ :=
    hconv.exists_uniform_lifted_packet hcompare c hc hq hδ hpacket
  refine ⟨a, A, r, R, ha, haA, hr, hrquarter, hR, ?_⟩
  intro η hη
  exact (hρ.eventually (eventually_gt_atTop (256 * R))).and (hpacket' η hη)

end GC.MetricGeometry

namespace DifferentialGeometry.CheegerGromovCompactness

open GC.MetricGeometry
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian

universe u v uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {Y : Type v} [MetricSpace Y] {ι : Type*} [Finite ι]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem PointedRiemannianSeq.exists_uniform_lifted_packet_of_sectional_lower_bound
    (X : PointedRiemannianSeq.{u, uE, uH} I)
    (hcomplete : ∀ i, MetricComplete (X.obj i))
    (hconn : ∀ i, ConnectedSpace (X.obj i).M)
    {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (X.obj i).metric (X.obj i).basepoint (ρ i),
      SectionalBoundedBelowAt (X.obj i).metric y (-((ρ i)⁻¹ ^ 2)))
    {x : Y} (c : Option (ι × Bool) → Y) (hc : Function.Injective c)
    (hq : dist (c none) x < 1 / 4) {δ : ℝ} (hδ : 0 < δ)
    (hpacket : PairedComparisonPacket (δ / 2) {c none}
      (fun j => c (some (j, true))) (fun j => c (some (j, false)))) :
    let : ∀ i, MetricSpace (X.obj i).M := fun i =>
      (properMetricOn (X.obj i) (hcomplete i) (hconn i)).alignedMetricSpace (X.obj i)
    PointedGHConverges (fun i => (X.obj i).basepoint) x →
    ∃ a A r R : ℝ, 0 < a ∧ a ≤ A ∧ 0 < r ∧ r < 1 / 4 ∧ 2 < R ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
        256 * R < ρ i ∧ ∃ ε : ℝ, 0 < ε ∧ ε < η ∧
        ∃ f : PointedBallApprox (X.obj i).basepoint x R ε,
        ∃ z : Option (ι × Bool) → BallCarrier (X.obj i).basepoint R,
          Function.Injective z ∧
          (∀ j, dist (f.toFun (z j)) (c j) < η) ∧
          (∀ j k, |dist (z j).val (z k).val - dist (c j) (c k)| < η) ∧
          dist (z none).val (X.obj i).basepoint < 1 / 2 ∧
          (∀ j, (z j).val ∈ ball (X.obj i).basepoint R) ∧
          ball (z none).val (2 * r) ⊆ ball (X.obj i).basepoint R ∧
          fourPointComparison 1 (ball (X.obj i).basepoint R) ∧
          PairedComparisonPacket δ (ball (z none).val (2 * r))
            (fun j => (z (some (j, true))).val) (fun j => (z (some (j, false))).val) ∧
          (∀ w ∈ ball (z none).val (2 * r), ∀ j,
            dist w (z (some j)).val ∈ Icc a A) ∧
          IsComplete (closedBall (z none).val r) := by
  let P := fun i => properMetricOn (X.obj i) (hcomplete i) (hconn i)
  let : ∀ i, MetricSpace (X.obj i).M := fun i => (P i).alignedMetricSpace (X.obj i)
  have : ∀ i, ProperSpace (X.obj i).M := fun i => (P i).properSpace_aligned (X.obj i)
  have : ∀ i, CompleteSpace (X.obj i).M := fun i => inferInstance
  dsimp only
  intro hconv
  have hmetric (i : ℕ) (a b : (X.obj i).M) :
      riemannianEDistOf (X.obj i).metric a b = ENNReal.ofReal (dist a b) := (P i).realizes a b
  have hsec' (i : ℕ) (y : (X.obj i).M) (hy : y ∈ ball (X.obj i).basepoint (ρ i)) :
      SectionalBoundedBelowAt (X.obj i).metric y (-((ρ i)⁻¹ ^ 2)) := by
    apply hsec i y
    change riemannianEDistOf (X.obj i).metric (X.obj i).basepoint y < ENNReal.ofReal (ρ i)
    rw [hmetric, dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff (dist_nonneg.trans_lt hy)).mpr hy
  exact exists_uniform_lifted_packet_of_growing_sectional_lower_bound
    (fun i => (X.obj i).metric) hmetric hconv hρ hsec' c hc hq hδ hpacket

end DifferentialGeometry.CheegerGromovCompactness
