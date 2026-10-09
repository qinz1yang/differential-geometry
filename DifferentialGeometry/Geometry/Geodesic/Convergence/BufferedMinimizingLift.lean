import DifferentialGeometry.Geometry.Metric.Comparison.BufferedEmbedding
import DifferentialGeometry.Geometry.Collapse.RiemannianOutwardPoint
import DifferentialGeometry.Geometry.Collapse.SublevelCore.Defs
import DifferentialGeometry.Geometry.Metric.Euclidean

/-!
# Actual minimizing segments lift inside a buffered source ball

The same partial diffeomorphism and its two metric bounds control every point of the original
intrinsic minimizing geodesic. No confinement or lifted-curve hypothesis is needed.
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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [CompleteSpace M] in
private theorem edistOf_eq_ofReal_dist (g : SmoothRiemannianMetric I M)
    (hNorm : IsMetricNorm g) (x y : M) : riemannianEDistOf g x y = ENNReal.ofReal (dist x y) := by
  rw [riemannianEDistOf_eq_riemannianEDist g hNorm,
    ← IsRiemannianManifold.out (I := I), edist_dist]

theorem intrinsicMinimizingGeodesic_mem_buffered_image
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (hNorm : IsMetricNorm g) (j : PartialDiffeomorph I I N M ∞) (n : N) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 10)
    (hcpt : IsCompact (riemannianClosedBallOf h n 10))
    (hsrc : riemannianClosedBallOf h n 10 ⊆ j.source)
    (hlower : ∀ x ∈ riemannianClosedBallOf h n 10, ∀ v : TangentSpace I x,
      (1 - lam) ^ 2 * h.inner x v v ≤
        g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x v))
    (hupper : ∀ x ∈ riemannianClosedBallOf h n 10, ∀ v : TangentSpace I x,
      g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x v) ≤
        (1 + lam) ^ 2 * h.inner x v v)
    {q : N} (hq : q ∈ riemannianBallOf h n 3)
    {w : TangentSpace I (j q)} (hw : w ∈ inwardMinimizingDirections g hNorm (j n) (j q))
    {t : ℝ} (ht : t ∈ Icc 0 (dist (j n) (j q))) :
    intrinsicGeodesic g hNorm (j q) w t ∈ (j : N → M) '' riemannianBallOf h n 4 := by
  have hlam1 : lam < 1 := by linarith
  have hm : 0 < 1 - lam := by linarith
  have hp : 0 ≤ 1 + lam := by linarith
  have hq10 : riemannianEDistOf h n q < ENNReal.ofReal 10 :=
    lt_trans hq (by norm_num)
  have hqfin : riemannianEDistOf h n q ≠ ⊤ := ne_top_of_lt hq10
  have hq3 : (riemannianEDistOf h n q).toReal < 3 := by
    have hh := (ENNReal.toReal_lt_toReal hqfin ENNReal.ofReal_ne_top).2 hq
    simpa using hh
  have hrad := riemannianEDistOf_map_le_of_buffered h g j n
    (by norm_num : (0 : ℝ) < 10) hlam0 hsrc hupper hq10
  rw [edistOf_eq_ofReal_dist g hNorm] at hrad
  have hlength : dist (j n) (j q) ≤ (1 + lam) * (riemannianEDistOf h n q).toReal := by
    have hh := ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hqfin) |>.2 hrad
    simpa only [ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hp] using hh
  have hlength33 : dist (j n) (j q) < 33 / 10 := by
    have hh := mul_lt_mul_of_pos_left hq3 (by linarith : 0 < 1 + lam)
    linarith
  let gamma := intrinsicGeodesic g hNorm (j q) w
  have hnear : dist (j n) (gamma t) ≤ dist (j n) (j q) := by
    have hh := dist_intrinsicGeodesic_le_mul g hNorm (j q) w ht.2
    rw [hw.1, Real.sqrt_one, one_mul, hw.2, dist_comm (gamma t) (j n)] at hh
    exact hh.trans (by linarith [ht.1])
  have hnear33 : dist (j n) (gamma t) < 33 / 10 := hnear.trans_lt hlength33
  have hcover := riemannianBallOf_subset_image_ball_of_buffered h g j n
    hlam1 hcpt hsrc hlower
  have hcovered : gamma t ∈ riemannianBallOf g (j n) ((1 - lam) * 10) := by
    change riemannianEDistOf g (j n) (gamma t) < ENNReal.ofReal ((1 - lam) * 10)
    rw [edistOf_eq_ofReal_dist g hNorm]
    apply ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.2
    linarith
  obtain ⟨x, hx, heq⟩ := hcover hcovered
  have hxfin : riemannianEDistOf h n x ≠ ⊤ := ne_top_of_lt hx
  have hxlower := le_riemannianEDistOf_map_of_buffered h g j n hlam1 hcpt hsrc hlower hx
  rw [heq, edistOf_eq_ofReal_dist g hNorm] at hxlower
  have hxreal : (1 - lam) * (riemannianEDistOf h n x).toReal ≤ dist (j n) (gamma t) := by
    have hh := ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hxfin) ENNReal.ofReal_ne_top |>.2 hxlower
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm.le,
      ENNReal.toReal_ofReal dist_nonneg] using hh
  have hx4 : (riemannianEDistOf h n x).toReal < 4 := by
    nlinarith [ENNReal.toReal_nonneg (a := riemannianEDistOf h n x)]
  refine ⟨x, ?_, heq⟩
  change riemannianEDistOf h n x < ENNReal.ofReal 4
  exact (ENNReal.toReal_lt_toReal hxfin ENNReal.ofReal_ne_top).1 (by simpa using hx4)

theorem intrinsicMinimizingGeodesic_buffered_inverse
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (hNorm : IsMetricNorm g) (j : PartialDiffeomorph I I N M ∞) (n : N) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 10)
    (hcpt : IsCompact (riemannianClosedBallOf h n 10))
    (hsrc : riemannianClosedBallOf h n 10 ⊆ j.source)
    (hlower : ∀ x ∈ riemannianClosedBallOf h n 10, ∀ v : TangentSpace I x,
      (1 - lam) ^ 2 * h.inner x v v ≤
        g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x v))
    (hupper : ∀ x ∈ riemannianClosedBallOf h n 10, ∀ v : TangentSpace I x,
      g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x v) ≤
        (1 + lam) ^ 2 * h.inner x v v)
    {q : N} (hq : q ∈ riemannianBallOf h n 3)
    {w : TangentSpace I (j q)} (hw : w ∈ inwardMinimizingDirections g hNorm (j n) (j q))
    {t : ℝ} (ht : t ∈ Icc 0 (dist (j n) (j q))) :
    let y := intrinsicGeodesic g hNorm (j q) w t
    j.symm y ∈ riemannianBallOf h n 4 ∧ j.symm y ∈ j.source ∧ j (j.symm y) = y := by
  obtain ⟨x, hx, heq⟩ := intrinsicMinimizingGeodesic_mem_buffered_image
    h g hNorm j n hlam0 hlam hcpt hsrc hlower hupper hq hw ht
  have hxs : x ∈ j.source := hsrc (by
    change riemannianEDistOf h n x ≤ ENNReal.ofReal 10
    exact le_of_lt (lt_trans hx (by norm_num)))
  have hleft : j.symm (intrinsicGeodesic g hNorm (j q) w t) = x :=
    (congrArg (j.symm : M → N) heq.symm).trans (j.left_inv hxs)
  exact ⟨hleft.symm ▸ hx, hleft.symm ▸ hxs, (congrArg (j : N → M) hleft).trans heq⟩

private instance realFinrankPositive : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem realMetricNorm : IsMetricNorm (euclideanMetric (E := ℝ)) := by
  intro x v
  rw [← ofReal_norm, euclideanMetric_inner, real_inner_self_eq_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]

private instance realRiemannianContinuous :
    IsContinuousRiemannianBundle ℝ (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) :=
  realMetricNorm.isContinuousRiemannianBundle

theorem realBuffered_minimizing_lift {q : ℝ} (hq : q ∈ Metric.ball 0 3)
    {w : TangentSpace 𝓘(ℝ, ℝ) q}
    (hw : w ∈ inwardMinimizingDirections (euclideanMetric (E := ℝ)) realMetricNorm 0 q)
    {t : ℝ} (ht : t ∈ Icc 0 (dist (0 : ℝ) q)) :
    let g := euclideanMetric (E := ℝ)
    let j := (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph
    let y := intrinsicGeodesic g realMetricNorm q w t
    j.symm y ∈ riemannianBallOf g 0 4 ∧ j.symm y ∈ j.source ∧ j (j.symm y) = y := by
  let g := euclideanMetric (E := ℝ)
  let j := (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph
  have hball : riemannianClosedBallOf g 0 10 = Metric.closedBall (0 : ℝ) 10 := by
    ext x
    change riemannianEDistOf g 0 x ≤ ENNReal.ofReal 10 ↔ dist x 0 ≤ 10
    rw [edistOf_eq_ofReal_dist g realMetricNorm]
    simpa only [dist_comm] using
      (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 10))
  have hsource : riemannianClosedBallOf g 0 10 ⊆ j.source := fun x hx => by trivial
  have heq (x : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) x) :
      g.inner (j x) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (j : ℝ → ℝ) x v)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (j : ℝ → ℝ) x v) = g.inner x v v := by
    change g.inner x (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id x v)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id x v) = g.inner x v v
    rw [mfderiv_id]
    rfl
  have hqr : q ∈ riemannianBallOf g 0 3 := by
    change riemannianEDistOf g 0 q < ENNReal.ofReal 3
    rw [edistOf_eq_ofReal_dist g realMetricNorm]
    apply ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.2
    simpa only [Metric.mem_ball, dist_comm] using hq
  exact intrinsicMinimizingGeodesic_buffered_inverse g g realMetricNorm j 0
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num) (hball ▸ isCompact_closedBall 0 10) hsource
    (fun x hx v => by rw [heq]; simp) (fun x hx v => by rw [heq]; simp) hqr hw ht

end DifferentialGeometry.Geometry.Riemannian.Geodesic
