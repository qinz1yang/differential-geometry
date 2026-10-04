import DifferentialGeometry.Geometry.Thurston.ModelAtlas.Composition
import DifferentialGeometry.Geometry.Metric.Pullback.Local

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

theorem ModelAtlas.pullback_of_localDiffeomorph
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    {k : SmoothRiemannianMetric K P} (hh : ModelAtlas h k)
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f)
    (hmetric : ∀ x (v w : TangentSpace I x),
      h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) = g.inner x v w) :
    ModelAtlas g k := by
  intro x
  obtain ⟨d, hx, hd⟩ := hf x
  obtain ⟨e, he, hmodel⟩ := hh (f x)
  let c := e.trans d.symm
  refine ⟨c, ?_, ?_⟩
  · change x ∈ d.source ∩ d ⁻¹' e.target
    refine ⟨hx, ?_⟩
    change d x ∈ e.target
    rwa [← hd hx]
  · intro y hy v w
    have heq : (f ∘ c) =ᶠ[𝓝 y] e :=
      Filter.eventuallyEq_of_mem (c.open_source.mem_nhds hy) (by
        intro z hz
        change f (d.symm (e z)) = e z
        have hzD : e z ∈ d.target := hz.2
        exact (hd (d.symm.map_source hzD)).trans (d.toPartialEquiv.right_inv hzD))
    have hder (u : TangentSpace K y) :
        mfderiv I J f (c y) (mfderiv K I c y u) = mfderiv K J e y u := by
      rw [← mfderiv_comp_apply y (hf.contMDiff.mdifferentiableAt (by decide))
        (c.mdifferentiableAt (by decide) hy)]
      exact congrArg (fun L : G →L[ℝ] F => L u) heq.mfderiv_eq
    rw [← hmetric, hder, hder]
    have hpoint : f (c y) = e y := heq.eq_of_nhds
    erw [hpoint]
    exact hmodel y hy.1 v w

theorem ModelAtlas.localPullMetric [FiniteDimensional ℝ E] [T2Space M]
    {h : SmoothRiemannianMetric J N} {k : SmoothRiemannianMetric K P}
    (hh : ModelAtlas h k) (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) :
    ModelAtlas (DifferentialGeometry.localPullMetric h f hf) k := by
  apply hh.pullback_of_localDiffeomorph hf
  intro x v w
  exact (localPullMetric_inner h f hf x v w).symm

end GC.Geometry
