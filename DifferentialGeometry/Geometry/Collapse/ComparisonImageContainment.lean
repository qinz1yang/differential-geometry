import DifferentialGeometry.Geometry.Metric.Approximation.BufferedImageContainment
import DifferentialGeometry.Geometry.Metric.RiemannianShortCurves
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# LFR10, containment clause, for actual Riemannian targets

Blueprint 207A, LFR10 (A:25488–25555). Binding of
`GC.MetricGeometry.eventually_ball_subset_image_of_distortion` to complete smooth Riemannian
targets in the aligned block of W3-F1 (`g i`, `hmetric`): the almost minimizing curves are
`exists_arbitrarily_short_riemannian_curve`. The source is any proper metric space carrying a
manifold structure (the finite model of LFR14 is a data input here); the comparison maps are local
diffeomorphisms on the source ball (the first step of LFR10's proof), which supplies continuity and
the open image.

The embedding clause of LFR10 (injectivity) is not proved here: it needs LFR09 (uniform short
joining geodesics, blocked) and LFR08 (ported separately).
-/

set_option autoImplicit false

open Set Filter Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Metric

/-- A local homeomorphism on an open set has open image of that set. -/
theorem isOpen_image_of_isLocalHomeomorphOn {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {s : Set X} (hf : IsLocalHomeomorphOn f s) (hs : IsOpen s) :
    IsOpen (f '' s) := by
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨e, hxe, hfe⟩ := hf x hx
  refine ⟨e '' (e.source ∩ s), ?_, e.isOpen_image_source_inter hs, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hz.2, by rw [hfe]⟩
  · exact ⟨x, ⟨hxe, hx⟩, by rw [hfe]⟩

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type*} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, T2Space (TangentBundle I (X i))]
  [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **LFR10, containment clause, Riemannian binding.** Complete smooth Riemannian targets
`(X i, g i)` with their distance (`hmetric`), a proper source `N` with a manifold structure, maps
`f i : N → X i` with `f i p = q i` that are eventually local homeomorphisms on `B(p,R)` (for
instance local diffeomorphisms) and whose distortion on `B(p,R)` tends to zero: for every `r < R`,
eventually `B(q i, r) ⊆ f i (B(p, R))`. -/
theorem eventually_riemannian_ball_subset_image_of_distortion
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {N : Type*} [MetricSpace N] [ProperSpace N] (f : ∀ i, N → X i) (p : N) (q : ∀ i, X i)
    (hp : ∀ i, f i p = q i) {R : ℝ}
    (hloc : ∀ᶠ i in atTop, IsLocalHomeomorphOn (f i) (ball p R))
    (hdist : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball p R, ∀ y ∈ ball p R,
      |dist (f i x) (f i y) - dist x y| < ε)
    {r : ℝ} (hr : r < R) : ∀ᶠ i in atTop, ball (q i) r ⊆ f i '' ball p R :=
  GC.MetricGeometry.eventually_ball_subset_image_of_distortion f p q hp
    (hloc.mono fun _ h => h.continuousOn)
    (hloc.mono fun _ h => isOpen_image_of_isLocalHomeomorphOn h isOpen_ball) hdist
    (fun i a b _ hη => exists_arbitrarily_short_riemannian_curve (g i) (hmetric i) a b hη) hr

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- The same with `C^n` local diffeomorphisms `f i : N → X i` from a manifold source
(`n ≠ 0` is not needed: local diffeomorphisms are local homeomorphisms). -/
theorem eventually_riemannian_ball_subset_image_of_localDiffeomorph
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} {n : WithTop ℕ∞}
    {N : Type*} [MetricSpace N] [ProperSpace N] [ChartedSpace H' N]
    (f : ∀ i, N → X i) (p : N) (q : ∀ i, X i) (hp : ∀ i, f i p = q i) {R : ℝ}
    (hloc : ∀ᶠ i in atTop, IsLocalDiffeomorphOn I' I n (f i) (ball p R))
    (hdist : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball p R, ∀ y ∈ ball p R,
      |dist (f i x) (f i y) - dist x y| < ε)
    {r : ℝ} (hr : r < R) : ∀ᶠ i in atTop, ball (q i) r ⊆ f i '' ball p R :=
  eventually_riemannian_ball_subset_image_of_distortion g hmetric f p q hp
    (hloc.mono fun _ h => h.isLocalHomeomorphOn) hdist hr

end DifferentialGeometry.Geometry.Metric
