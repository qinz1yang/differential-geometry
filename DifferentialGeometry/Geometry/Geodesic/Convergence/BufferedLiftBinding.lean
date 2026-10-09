import DifferentialGeometry.Geometry.Geodesic.Convergence.BufferedLiftFlow

/-!
# Reference-buffer geometry for the same actual pullback flow

The reference metric controls the buffered balls while the original pullback metric controls the
source flow. Their separation is essential when the source pullback metric is not complete.
-/

set_option autoImplicit false

noncomputable section

open Set Bundle
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T3Space N]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem bufferedReferenceLift_eq_geodesicFlow
    (hRef h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (hNorm : IsMetricNorm g) (j : PartialDiffeomorph I I N M ∞) (n : N) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 10)
    (hcpt : IsCompact (riemannianClosedBallOf hRef n 10))
    (hsrc : riemannianClosedBallOf hRef n 10 ⊆ j.source)
    (hlower : ∀ x ∈ riemannianClosedBallOf hRef n 10, ∀ v : TangentSpace I x,
      (1 - lam) ^ 2 * hRef.inner x v v ≤
        g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x v))
    (hupper : ∀ x ∈ riemannianClosedBallOf hRef n 10, ∀ v : TangentSpace I x,
      g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x v) ≤
        (1 + lam) ^ 2 * hRef.inner x v v)
    (hmetric : ∀ x ∈ j.source, ∀ v w : TangentSpace I x,
      h.inner x v w =
        g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x w))
    {q : N} (hq : q ∈ riemannianBallOf hRef n 3)
    {w : TangentSpace I (j q)} (hw : w ∈ inwardMinimizingDirections g hNorm (j n) (j q)) :
    let alpha := fun s => j.symm (intrinsicGeodesic g hNorm (j q) w s)
    let p : TangentBundle I N := ⟨q, mfderiv I I (j.symm : M → N) (j q) w⟩
    ∀ t ∈ Icc 0 (dist (j n) (j q)), (p, t) ∈ h.geodesicFlowDomain ∧
      h.geodesicFlow p t = DifferentialGeometry.velocityLift alpha t := by
  have hqSource : q ∈ j.source := hsrc (by
    change riemannianEDistOf hRef n q ≤ ENNReal.ofReal 10
    exact le_of_lt (lt_trans hq (by norm_num)))
  let alpha := fun s => j.symm (intrinsicGeodesic g hNorm (j q) w s)
  have hinit : DifferentialGeometry.velocityLift (I := I) alpha 0 =
      (⟨q, mfderiv I I (j.symm : M → N) (j q) w⟩ : TangentBundle I N) := by
    obtain ⟨hbase, hvel⟩ := inverseIntrinsicGeodesic_velocityLift_zero g hNorm j q hqSource w
    apply TotalSpace.ext hbase
    exact heq_of_eq hvel
  have hflow := inverseIntrinsicGeodesic_eq_geodesicFlow_on_interval h g hNorm j hmetric
    (j q) w dist_nonneg (fun t ht => by
      obtain ⟨x, hx, heq⟩ := intrinsicMinimizingGeodesic_mem_buffered_image
        hRef g hNorm j n hlam0 hlam hcpt hsrc hlower hupper hq hw ht
      apply heq ▸ j.map_source (hsrc ?_)
      change riemannianEDistOf hRef n x ≤ ENNReal.ofReal 10
      exact le_of_lt (lt_trans hx (by norm_num)))
  dsimp only at hflow ⊢
  rw [hinit] at hflow
  exact hflow

private instance realFinrankPositive : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem realMetricNorm : IsMetricNorm (euclideanMetric (E := ℝ)) := by
  intro x v
  rw [← ofReal_norm, euclideanMetric_inner, real_inner_self_eq_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]

private instance realRiemannianContinuous :
    IsContinuousRiemannianBundle ℝ (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) :=
  realMetricNorm.isContinuousRiemannianBundle

theorem realReferenceLift_geodesicFlow (q : ℝ) (hq : q ∈ Metric.ball 0 3)
    (w : TangentSpace 𝓘(ℝ, ℝ) q)
    (hw : w ∈ inwardMinimizingDirections (euclideanMetric (E := ℝ)) realMetricNorm 0 q) :
    let g := euclideanMetric (E := ℝ)
    let j := (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph
    let alpha := fun s => j.symm (intrinsicGeodesic g realMetricNorm q w s)
    let p : TangentBundle 𝓘(ℝ, ℝ) ℝ := ⟨q, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (j.symm : ℝ → ℝ) q w⟩
    ∀ t ∈ Icc 0 (dist (0 : ℝ) q), (p, t) ∈ g.geodesicFlowDomain ∧
      g.geodesicFlow p t = DifferentialGeometry.velocityLift alpha t := by
  let g := euclideanMetric (E := ℝ)
  let j := (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph
  have hd (x y : ℝ) : riemannianEDistOf g x y = ENNReal.ofReal (dist x y) := by
    rw [riemannianEDistOf_eq_riemannianEDist g realMetricNorm,
      ← IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)), edist_dist]
  have hball : riemannianClosedBallOf g 0 10 = Metric.closedBall (0 : ℝ) 10 := by
    ext x
    change riemannianEDistOf g 0 x ≤ ENNReal.ofReal 10 ↔ dist x 0 ≤ 10
    rw [hd]
    simpa only [dist_comm] using
      (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 10))
  have hqr : q ∈ riemannianBallOf g 0 3 := by
    change riemannianEDistOf g 0 q < ENNReal.ofReal 3
    rw [hd]
    apply ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.2
    simpa only [Metric.mem_ball, dist_comm] using hq
  have hmetric (x : ℝ) (hx : x ∈ j.source) (v u : TangentSpace 𝓘(ℝ, ℝ) x) :
      g.inner x v u = g.inner (j x) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (j : ℝ → ℝ) x v)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (j : ℝ → ℝ) x u) := by
    change g.inner x v u = g.inner x (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id x v)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id x u)
    rw [mfderiv_id]
    rfl
  have hsource : riemannianClosedBallOf g 0 10 ⊆ j.source := fun x hx => by trivial
  exact bufferedReferenceLift_eq_geodesicFlow g g g realMetricNorm j 0
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num) (hball ▸ isCompact_closedBall 0 10) hsource
    (fun x hx v => by rw [← hmetric x (hsource hx)]; simp)
    (fun x hx v => by rw [← hmetric x (hsource hx)]; simp) hmetric hqr hw

end DifferentialGeometry.Geometry.Riemannian.Geodesic
