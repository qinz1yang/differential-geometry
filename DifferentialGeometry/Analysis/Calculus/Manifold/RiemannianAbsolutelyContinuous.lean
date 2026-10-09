import DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
import DifferentialGeometry.Geometry.Metric.ChartLipschitz
import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous

open Bundle Function Set
open scoped Manifold Interval

namespace AbsolutelyContinuousOnInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

theorem manifold {gamma : ℝ → M} {a b : ℝ}
    (h : AbsolutelyContinuousOnInterval gamma a b) :
    Manifold.absolutelyContinuousOnInterval I gamma a b := by
  have hcont : ContinuousOn gamma (uIcc a b) :=
    (uniformContinuousOn_of_absolutelyContinuousOnInterval h).continuousOn
  constructor
  · exact hcont
  intro p c d hsub hmaps
  obtain ⟨C, hchart⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_lipschitzOnWith_extChartAt_of_isCompact
      (I := I) p (isCompact_uIcc.image_of_continuousOn (hcont.mono hsub))
      (by simpa only [extChartAt_source] using mapsTo_iff_image_subset.mp hmaps)
  exact hchart.comp_absolutelyContinuousOnInterval (fun t ht => mem_image_of_mem gamma ht)
    (AbsolutelyContinuousOnInterval.mono (f := gamma) h hsub)

end AbsolutelyContinuousOnInterval
