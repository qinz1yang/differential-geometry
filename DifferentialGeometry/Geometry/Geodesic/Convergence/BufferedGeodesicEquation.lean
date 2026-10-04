import DifferentialGeometry.Geometry.Geodesic.Convergence.BufferedMinimizingLift
import DifferentialGeometry.Geometry.Geodesic.Naturality.LocalIsometry.Germ

/-!
# The original inverse lift satisfies the actual pullback geodesic equation

The inverse local-isometry identity follows from the same partial diffeomorphism's right inverse.
Buffered minimizing segments therefore satisfy the source equation throughout their interval,
without a complete source metric or a separate lifted-geodesic hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T3Space N]
  [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [CompleteSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
theorem metric_identity_of_partialDiffeomorph_inverse
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (j : PartialDiffeomorph I I N M ∞)
    (hmetric : ∀ x ∈ j.source, ∀ v w : TangentSpace I x,
      h.inner x v w =
        g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x w))
    (y : M) (hy : y ∈ j.target) (v w : TangentSpace I y) :
    g.inner y v w = h.inner (j.symm y)
      (mfderiv I I (j.symm : M → N) y v) (mfderiv I I (j.symm : M → N) y w) := by
  have hpoint : j (j.symm y) = y := j.right_inv hy
  have heq : (fun z : M => j (j.symm z)) =ᶠ[𝓝 y] id :=
    j.toOpenPartialHomeomorph.eventually_right_inverse hy
  have hd (u : TangentSpace I y) :
      mfderiv I I (j : N → M) (j.symm y) (mfderiv I I (j.symm : M → N) y u) = u := by
    have hc := mfderiv_comp_apply y
      (j.mdifferentiableAt (by simp) (j.map_target hy))
      (j.symm.mdifferentiableAt (by simp) hy) u
    have hh := congrArg (fun L : TangentSpace I y →L[ℝ] TangentSpace I y => L u)
      (heq.mfderiv_eq (I := I) (I' := I))
    rw [mfderiv_id] at hh
    exact hc.symm.trans hh
  calc
    g.inner y v w = g.inner (j (j.symm y)) v w :=
      congrArg (fun x : M => g.inner x v w) hpoint.symm
    _ = g.inner (j (j.symm y))
        (mfderiv I I (j : N → M) (j.symm y) (mfderiv I I (j.symm : M → N) y v))
        (mfderiv I I (j : N → M) (j.symm y) (mfderiv I I (j.symm : M → N) y w)) := by
      exact congrArg₂ (fun v' w' : E => g.inner (j (j.symm y)) v' w')
        (hd v).symm (hd w).symm
    _ = _ := (hmetric (j.symm y) (j.map_target hy) _ _).symm

theorem intrinsicGeodesic_inverse_isGeodesicAt
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (hNorm : IsMetricNorm g) (j : PartialDiffeomorph I I N M ∞)
    (hmetric : ∀ x ∈ j.source, ∀ v w : TangentSpace I x,
      h.inner x v w =
        g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x w))
    (p : M) (v : TangentSpace I p) {t : ℝ}
    (ht : intrinsicGeodesic g hNorm p v t ∈ j.target) :
    IsGeodesicAt h (fun s => j.symm (intrinsicGeodesic g hNorm p v s)) t := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact isGeodesicAt_map_of_local_isometry_on g h j.open_target
    (fun y => j.symm.isLocalDiffeomorphAt I I ∞ y.property)
    (metric_identity_of_partialDiffeomorph_inverse h g j hmetric) ht
    (DifferentialGeometry.Geometry.isGeodesicAt_of_isGeodesicOn g univ_mem
      ((intrinsicGeodesic_isGeodesic g hNorm p v).isGeodesicOn univ)
      (intrinsicGeodesic_contMDiff g hNorm p v).continuous.continuousOn)

theorem intrinsicMinimizingGeodesic_buffered_isGeodesicAt
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
    (hmetric : ∀ x ∈ j.source, ∀ v w : TangentSpace I x,
      h.inner x v w =
        g.inner (j x) (mfderiv I I (j : N → M) x v) (mfderiv I I (j : N → M) x w))
    {q : N} (hq : q ∈ riemannianBallOf h n 3)
    {w : TangentSpace I (j q)} (hw : w ∈ inwardMinimizingDirections g hNorm (j n) (j q))
    {t : ℝ} (ht : t ∈ Icc 0 (dist (j n) (j q))) :
    IsGeodesicAt h (fun s => j.symm (intrinsicGeodesic g hNorm (j q) w s)) t := by
  obtain ⟨x, hx, heq⟩ := intrinsicMinimizingGeodesic_mem_buffered_image
    h g hNorm j n hlam0 hlam hcpt hsrc hlower hupper hq hw ht
  have hxs : x ∈ j.source := hsrc (by
    change riemannianEDistOf h n x ≤ ENNReal.ofReal 10
    exact le_of_lt (lt_trans hx (by norm_num)))
  exact intrinsicGeodesic_inverse_isGeodesicAt h g hNorm j hmetric (j q) w
    (heq ▸ j.map_source hxs)

private instance realFinrankPositive : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem realMetricNorm : IsMetricNorm (euclideanMetric (E := ℝ)) := by
  intro x v
  rw [← ofReal_norm, euclideanMetric_inner, real_inner_self_eq_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]

private instance realRiemannianContinuous :
    IsContinuousRiemannianBundle ℝ (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) :=
  realMetricNorm.isContinuousRiemannianBundle

theorem realInverse_isGeodesicAt (q : ℝ) (w : TangentSpace 𝓘(ℝ, ℝ) q) (t : ℝ) :
    let g := euclideanMetric (E := ℝ)
    let j := (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph
    IsGeodesicAt g (fun s => j.symm (intrinsicGeodesic g realMetricNorm q w s)) t := by
  let g := euclideanMetric (E := ℝ)
  let j := (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph
  apply intrinsicGeodesic_inverse_isGeodesicAt g g realMetricNorm j
  · intro x hx v w'
    change g.inner x v w' = g.inner x (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id x v)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id x w')
    rw [mfderiv_id]
    rfl
  · trivial

end DifferentialGeometry.Geometry.Riemannian.Geodesic
