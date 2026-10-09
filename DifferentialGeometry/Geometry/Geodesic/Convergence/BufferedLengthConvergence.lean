import DifferentialGeometry.Geometry.Metric.Convergence.Metric.MapDistance
import DifferentialGeometry.Geometry.Geodesic.Convergence.MetricUnitCompactness

/-!
# Actual segment lengths under the original buffered pullback maps

Uniform native distance transfer retains the original maps and metrics. Continuity controls
moving original source points and gives the corresponding intrinsic reference length limit.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  {M : ℕ → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem bufferedPullback_lengths_tendsto
    (hSeq : ℕ → SmoothRiemannianMetric I N) (hInf hRef : SmoothRiemannianMetric I N)
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (j : ∀ i, PartialDiffeomorph I I N (M i) ∞) (n : N)
    (hcpt : IsCompact (riemannianClosedBallOf hInf n 10))
    (hconv : MetricCPConvergenceOn (riemannianClosedBallOf hInf n 10) 0 hSeq hInf hRef)
    (hsrc : ∀ᶠ i in atTop, riemannianClosedBallOf hInf n 10 ⊆ (j i).source)
    (hmetric : ∀ᶠ i in atTop, ∀ x ∈ riemannianClosedBallOf hInf n 10,
      ∀ v : TangentSpace I x, (hSeq i).inner x v v =
        (g i).inner (j i x) (mfderiv I I (j i : N → M i) x v)
          (mfderiv I I (j i : N → M i) x v))
    (qSeq : ℕ → N) {q : N} (hq : q ∈ riemannianBallOf hInf n 3)
    (hqSeq : Tendsto qSeq atTop (𝓝 q)) :
    Tendsto (fun i => (riemannianEDistOf (g i) (j i n) (j i (qSeq i))).toReal)
      atTop (𝓝 (riemannianEDistOf hInf n q).toReal) := by
  have hd : Tendsto (fun i => riemannianEDistOf hInf n (qSeq i))
      atTop (𝓝 (riemannianEDistOf hInf n q)) :=
    (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist hInf n).tendsto q
      |>.comp hqSeq
  have hsmall : ∀ᶠ i in atTop, qSeq i ∈ riemannianClosedBallOf hInf n 3 :=
    (hd.eventually (gt_mem_nhds hq)).mono (fun i hi => hi.le)
  have hreference := (ENNReal.continuousAt_toReal (ne_top_of_lt hq)).tendsto.comp hd
  rw [Metric.tendsto_nhds] at hreference ⊢
  intro epsilon hepsilon
  have herror := hconv.eventually_uniform_edist_toReal_of_pullback g j n
    (rho := 3) (by norm_num) (by norm_num) hcpt hsrc hmetric (half_pos hepsilon)
  filter_upwards [herror, hsmall, hreference (epsilon / 2) (half_pos hepsilon)]
    with i hi hqi hri
  have hn : n ∈ riemannianClosedBallOf hInf n 3 := by
    change riemannianEDistOf hInf n n ≤ ENNReal.ofReal 3
    rw [riemannianEDistOf_self]
    exact bot_le
  have herr := hi n hn (qSeq i) hqi
  rw [Real.dist_eq] at hri ⊢
  change |(riemannianEDistOf hInf n (qSeq i)).toReal -
    (riemannianEDistOf hInf n q).toReal| < epsilon / 2 at hri
  exact lt_of_le_of_lt (abs_sub_le _ (riemannianEDistOf hInf n (qSeq i)).toReal _)
    (by linarith)

private theorem realMetricNorm : IsMetricNorm (euclideanMetric (E := ℝ)) := by
  intro x v
  rw [← ofReal_norm, euclideanMetric_inner, real_inner_self_eq_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]

theorem realIdentity_buffered_lengths_tendsto :
    let g := euclideanMetric (E := ℝ)
    Tendsto (fun _i : ℕ => (riemannianEDistOf g (0 : ℝ) 1).toReal)
      atTop (𝓝 (riemannianEDistOf g (0 : ℝ) 1).toReal) := by
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
  apply bufferedPullback_lengths_tendsto (fun _i : ℕ => g) g g (fun _i : ℕ => g)
    (fun _i : ℕ => j) (0 : ℝ) (hball ▸ isCompact_closedBall 0 10)
  · intro epsilon hepsilon
    exact ⟨0, fun _i _hi => by rw [metricDerivNormSupOn_self]; exact hepsilon⟩
  · exact Eventually.of_forall (fun _i x _hx => by trivial)
  · exact Eventually.of_forall (fun _i x _hx v => by
      change g.inner x v v = g.inner x (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id x v)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id x v)
      rw [mfderiv_id]
      rfl)
  · change riemannianEDistOf g (0 : ℝ) 1 < ENNReal.ofReal 3
    rw [hd]
    norm_num [Real.dist_eq]
  · exact tendsto_const_nhds

end DifferentialGeometry.Geometry.Riemannian.Geodesic
