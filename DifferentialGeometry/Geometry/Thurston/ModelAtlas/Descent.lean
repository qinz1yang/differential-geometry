import DifferentialGeometry.Geometry.Thurston.ModelAtlas.Composition
import DifferentialGeometry.Geometry.Metric.Quotient

set_option autoImplicit false
noncomputable section
open DifferentialGeometry
open scoped Manifold ContDiff Topology

namespace GC.Geometry

variable {E F G H H' H'' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {K : ModelWithCorners ℝ G H''}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]

theorem ModelAtlas.of_surjective_localDiffeomorph
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (hmetric : ∀ x (v w : TangentSpace I x),
      h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) = g.inner x v w) :
    ModelAtlas h g := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨e, hx, he⟩ := hf x
  refine ⟨e, ?_, ?_⟩
  · rw [he hx]
    exact e.map_source hx
  · intro z hz v w
    have heq : f =ᶠ[𝓝 z] e :=
      Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hz) (fun q hq => he hq)
    have hd : (mfderiv I J f z : E →L[ℝ] F) = mfderiv I J e z :=
      heq.mfderiv_eq
    rw [← he hz, ← hd]
    exact hmetric z v w

theorem ModelAtlas.descend
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    {k : SmoothRiemannianMetric K P} (hg : ModelAtlas g k)
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (hmetric : ∀ x (v w : TangentSpace I x),
      h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) = g.inner x v w) :
    ModelAtlas h k :=
  (ModelAtlas.of_surjective_localDiffeomorph g h hf hsurj hmetric).trans hg


theorem CompleteModelAtlas.descend
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [SigmaCompactSpace M] [T2Space N] [SigmaCompactSpace N]
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    {k : SmoothRiemannianMetric K P} (hg : CompleteModelAtlas g k)
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) (hcover : IsCoveringMap f)
    (hsurj : Function.Surjective f) (hpull : localPullMetric h f hf = g) :
    CompleteModelAtlas h k := by
  refine ⟨RiemannianMetricComplete.of_coveringMap_localPullMetric
    g h hf hcover hsurj hpull hg.1, hg.2.descend hf hsurj ?_⟩
  intro x v w
  rw [← hpull, localPullMetric_inner]

variable {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem ModelAtlas.descendedMetric
    [FiniteDimensional ℝ E] [T2Space M] [T2Space Q]
    {g : SmoothRiemannianMetric I M} {k : SmoothRiemannianMetric K P}
    (hg : ModelAtlas g k) (f : M → Q) (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f) (hcompat : metricFiberCompatible g f hf) :
    ModelAtlas (DifferentialGeometry.descendedMetric g f hf hsurj hcompat) k := by
  apply hg.descend hf hsurj
  intro x v w
  have hp := congrArg (fun m : SmoothRiemannianMetric I M => m.inner x v w)
    (localPullMetric_descendedMetric g f hf hsurj hcompat)
  simpa only [localPullMetric_inner] using hp

theorem CompleteModelAtlas.descendedMetric
    [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    [T2Space Q] [SigmaCompactSpace Q]
    {g : SmoothRiemannianMetric I M} {k : SmoothRiemannianMetric K P}
    (hg : CompleteModelAtlas g k) (f : M → Q) (hf : IsLocalDiffeomorph I I ∞ f)
    (hcover : IsCoveringMap f) (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf) :
    CompleteModelAtlas (DifferentialGeometry.descendedMetric g f hf hsurj hcompat) k :=
  hg.descend hf hcover hsurj (localPullMetric_descendedMetric g f hf hsurj hcompat)

end GC.Geometry
