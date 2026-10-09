import DifferentialGeometry.Geometry.Collapse.RankStrata
import DifferentialGeometry.Geometry.Metric.Approximation.LowDimensionalRankApplications
import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianSequence
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

/-!
# Riemannian rank strata and actual low-dimensional limit consumers

Pointwise tensor scaling agrees with the metric used to assign the finite strata.
The actual limit binding uses the delivered X71 theorem. Local collapse from curvature and
volume still needs the separate LC08 and LC09 model producers.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff ENNReal Topology
open GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

theorem riemannian_scaledSplittingRank_binding {M : Type u} [m : MetricSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y, riemannianEDistOf g x y = ENNReal.ofReal (dist x y))
    (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p) (β : ℕ → ℝ) (p : M) :
    (∀ x y, riemannianEDistOf
      (scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ p)) 2) g) x y =
      ENNReal.ofReal (@dist M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))).toDist x y)) ∧
      scaledSplittingRank.{u, v} ρ hρ β p ≤ 3 := by
  refine ⟨?_, scaledSplittingRank_le ρ hρ β p⟩
  intro x y
  rw [edistOf_scale, hmetric, MetricSpace.rescale_dist,
    Real.sqrt_sq (inv_pos.mpr (hρ p)).le, ← ENNReal.ofReal_mul (inv_pos.mpr (hρ p)).le]

theorem exists_uniform_scaled_rank_bound_of_model :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 10 ∧
      ∀ (M : Type u) (m : MetricSpace M) (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p)
        (p : M) (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∃ γ : Icc (0 : ℝ) 1 → C, Continuous γ ∧
        γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (γ s) (γ t) = dist x y * dist s t) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
      ∀ (σ : ℝ) (β : ℕ → ℝ), σ ≤ η → β 3 ≤ η →
      @KleinerLottApprox M C (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p c σ →
      @scaledSplittingRank.{u, u} M m ρ hρ β p ≤ 2 := by
  obtain ⟨η, hη, hηsmall, hex⟩ := exists_uniform_rank_bound_of_model.{u, v, u}
  refine ⟨η, hη, hηsmall, ?_⟩
  intro M m ρ hρ p C mC hc c hseg hdim hcomp σ β hσ hβ f
  exact @hex M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p C mC hc c
    hseg hdim hcomp σ β hσ hβ f

end DifferentialGeometry.Geometry.Collapse

namespace DifferentialGeometry.CheegerGromovCompactness

universe u v uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem PointedRiemannianSeq.exists_low_dimensional_limit_with_rank_exclusion
    (X : PointedRiemannianSeq.{u, uE, uH} I)
    (hcomplete : ∀ i, MetricComplete (X.obj i))
    (hconn : ∀ i, ConnectedSpace (X.obj i).M)
    (hdimE : Module.finrank ℝ E ≤ 2) {κ ρ : ℕ → ℝ}
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (X.obj i).metric (X.obj i).basepoint (ρ i),
      SectionalBoundedBelowAt (X.obj i).metric y (-κ i)) :
    let : ∀ i, MetricSpace (X.obj i).M := fun i =>
      (properMetricOn (X.obj i) (hcomplete i) (hconn i)).alignedMetricSpace (X.obj i)
    ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
      ∃ (q : Y) (a : ℕ → ℕ), StrictMono a ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => (X.obj (a i)).basepoint) q ∧
        dimH (univ : Set Y) ≤ 2 ∧ fourPointComparison 0 (univ : Set Y) ∧
        (∀ x y : Y, ∃ γ : Icc (0 : ℝ) 1 → Y, Continuous γ ∧
          γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (γ s) (γ t) = dist x y * dist s t) ∧
        ∃ η : ℝ, 0 < η ∧ η < 1 / 10 ∧
          ∀ β : ℝ, β ≤ η → ¬ HasEuclideanSplitting.{0, v} q 3 β := by
  let : ∀ i, MetricSpace (X.obj i).M := fun i =>
    (properMetricOn (X.obj i) (hcomplete i) (hconn i)).alignedMetricSpace (X.obj i)
  obtain ⟨Y, mY, q, a, ha, hc, hp, hconv, hdim, hcomp, hseg, hquad, hnet⟩ :=
    X.exists_pointed_limit_of_sectional_lower_bound hcomplete hconn hκ hκzero hρ hsec
  let := mY
  let := hc
  have hdim' : dimH (univ : Set Y) ≤ 2 :=
    hdim.trans (by exact_mod_cast hdimE)
  obtain ⟨η, hη, hηsmall, hex⟩ :=
    exists_uniform_three_splitting_exclusion_of_model_itself.{0, v}
  exact ⟨Y, mY, q, a, ha, hc, hp, hconv, hdim', hcomp, hseg,
    η, hη, hηsmall, hex Y q hseg hdim' hcomp⟩

end DifferentialGeometry.CheegerGromovCompactness
