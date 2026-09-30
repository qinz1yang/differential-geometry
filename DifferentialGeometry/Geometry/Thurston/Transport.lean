import DifferentialGeometry.Geometry.Thurston.Atlas
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross

set_option autoImplicit false
noncomputable section
open DifferentialGeometry
open scoped Manifold ContDiff
namespace GC.Geometry
variable {E F H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
  [T2Space M] [T2Space N]

omit [FiniteDimensional ℝ F] [T2Space N] in
theorem CoordinateModelAtlas.pullback {g : SmoothRiemannianMetric J N}
    {k : CoordinateModel} (hg : CoordinateModelAtlas g k) (f : M ≃ₘ⟮I, J⟯ N) :
    CoordinateModelAtlas (Diffeomorph.pullbackMetricCross g f) k := by
  intro x
  obtain ⟨e, hx, he⟩ := hg (f x)
  let d := e.trans f.symm.toPartialDiffeomorph
  refine ⟨d, ⟨Set.mem_univ x, hx⟩, ?_⟩
  intro y hy v w
  have hd : MDifferentiableAt (𝓡 3) I d y := d.mdifferentiableAt (by decide) hy
  have hcomp : (f : M → N) ∘ d = e := by
    funext z
    exact f.apply_symm_apply (e z)
  have hder (u : TangentSpace (𝓡 3) y) :
      mfderiv I J f (d y) (mfderiv (𝓡 3) I d y u) = mfderiv (𝓡 3) J e y u := by
    rw [← mfderiv_comp_apply y (f.mdifferentiable (by decide) (d y)) hd, hcomp]
  rw [Diffeomorph.pullbackMetricCross_inner, hder, hder]
  change g.inner (f (f.symm (e y))) _ _ = _
  rw [f.apply_symm_apply]
  exact he y hy.1 v w

omit [FiniteDimensional ℝ F] in
theorem HasThurstonAtlas.pullback {g : SmoothRiemannianMetric J N}
    {k : ThurstonModel} (hg : HasThurstonAtlas g k) (f : M ≃ₘ⟮I, J⟯ N) :
    HasThurstonAtlas (Diffeomorph.pullbackMetricCross g f) k := by
  cases k <;> first | exact ModelAtlas.pullback hg f | exact CoordinateModelAtlas.pullback hg f

variable [SigmaCompactSpace M] [SigmaCompactSpace N]

def GeometricStructure.pullback [I.Boundaryless] (G : GeometricStructure J N)
    (f : M ≃ₘ⟮I, J⟯ N) : GeometricStructure I M where
  model := G.model
  metric := Diffeomorph.pullbackMetricCross G.metric f
  complete := DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_pullbackMetricCross
    G.complete f
  atlas := G.atlas.pullback f
  hyperbolic_finite_volume := by
    intro hk
    rw [Integral.Measure.riemannianVolumeMeasure_pullback_cross]
    let : MeasurableSpace M := borel M
    let : MeasurableSpace N := borel N
    let : BorelSpace M := ⟨rfl⟩
    let : BorelSpace N := ⟨rfl⟩
    rw [MeasureTheory.Measure.map_apply f.symm.continuous.measurable MeasurableSet.univ]
    exact G.hyperbolic_finite_volume hk

end GC.Geometry
