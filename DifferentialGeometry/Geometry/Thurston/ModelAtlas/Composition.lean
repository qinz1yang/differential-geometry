import DifferentialGeometry.Geometry.Thurston.ModelAtlas

namespace GC.Geometry
open DifferentialGeometry
open scoped Manifold ContDiff
set_option autoImplicit false
noncomputable section
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

theorem ModelAtlas.trans
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    {k : SmoothRiemannianMetric K P} (hg : ModelAtlas g h) (hh : ModelAtlas h k) :
    ModelAtlas g k := by
  intro x
  obtain ⟨e, hx, he⟩ := hg x
  obtain ⟨d, hy, hd⟩ := hh (e.symm x)
  refine ⟨d.trans e, ⟨hx, hy⟩, ?_⟩
  intro z hz v w
  have hder (u : TangentSpace K z) :
      mfderiv K I (d.trans e) z u =
        mfderiv J I e (d z) (mfderiv K J d z u) :=
    mfderiv_comp_apply z (e.mdifferentiableAt (by decide) hz.2)
      (d.mdifferentiableAt (by decide) hz.1) u
  exact (congrArg₂ (fun a b : TangentSpace I (e (d z)) => g.inner (e (d z)) a b)
      (hder v) (hder w)).trans
    ((he (d z) hz.2 _ _).trans (hd z hz.1 v w))

theorem CompleteModelAtlas.trans [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    {k : SmoothRiemannianMetric K P} (hg : CompleteModelAtlas g h)
    (hh : ModelAtlas h k) : CompleteModelAtlas g k :=
  ⟨hg.1, hg.2.trans hh⟩

end
end GC.Geometry
