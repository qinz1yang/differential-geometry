import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.CompletenessPullback
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

namespace GC.Geometry
open DifferentialGeometry
open scoped Manifold ContDiff
set_option autoImplicit false
noncomputable section
variable {E F G H H' H'' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {K : ModelWithCorners ℝ G H''}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]

def ModelAtlas (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) : Prop :=
  ∀ x : M, ∃ e : PartialDiffeomorph J I N M ∞, x ∈ e.target ∧
    ∀ y ∈ e.source, ∀ v w : TangentSpace J y,
      g.inner (e y) (mfderiv J I e y v) (mfderiv J I e y w) = h.inner y v w

omit [FiniteDimensional ℝ E] in
theorem ModelAtlas.refl (g : SmoothRiemannianMetric I M) : ModelAtlas g g := by
  intro x
  refine ⟨(Diffeomorph.refl I M ∞).toPartialDiffeomorph, Set.mem_univ x, ?_⟩
  intro y hy v w
  change g.inner y (mfderiv I I id y v) (mfderiv I I id y w) = _
  rw [mfderiv_id]
  rfl

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in

theorem ModelAtlas.pullback [T2Space M] [T2Space N]
    {g : SmoothRiemannianMetric J N} {h : SmoothRiemannianMetric K P}
    (hg : ModelAtlas g h) (f : M ≃ₘ⟮I, J⟯ N) :
    ModelAtlas (Diffeomorph.pullbackMetricCross g f) h := by
  intro x
  obtain ⟨e, hx, he⟩ := hg (f x)
  let d := e.trans f.symm.toPartialDiffeomorph
  refine ⟨d, ?_, ?_⟩
  · change x ∈ Set.univ ∩ (f.symm.symm ⁻¹' e.target)
    exact ⟨Set.mem_univ x, hx⟩
  · intro y hy v w
    have hyE : y ∈ e.source := hy.1
    have hd : MDifferentiableAt K I d y := d.mdifferentiableAt (by decide) hy
    have hcomp : (f : M → N) ∘ d = e := by
      funext z
      exact f.apply_symm_apply (e z)
    have hder (u : TangentSpace K y) :
        mfderiv I J f (d y) (mfderiv K I d y u) = mfderiv K J e y u := by
      rw [← mfderiv_comp_apply y (f.mdifferentiable (by decide) (d y)) hd, hcomp]
    rw [Diffeomorph.pullbackMetricCross_inner, hder, hder]
    change g.inner (f (f.symm (e y))) _ _ = _
    rw [f.apply_symm_apply]
    exact he y hyE v w

def CompleteModelAtlas [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric J N) : Prop :=
  RiemannianMetricComplete g ∧ ModelAtlas g h

omit [FiniteDimensional ℝ G] in
theorem CompleteModelAtlas.pullback
    [T2Space M] [SigmaCompactSpace M] [T2Space N] [SigmaCompactSpace N]
    {g : SmoothRiemannianMetric J N} {h : SmoothRiemannianMetric K P}
    (hg : CompleteModelAtlas g h) (f : M ≃ₘ⟮I, J⟯ N) :
    CompleteModelAtlas (Diffeomorph.pullbackMetricCross g f) h :=
  ⟨DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_pullbackMetricCross hg.1 f,
    hg.2.pullback f⟩

end
end GC.Geometry
