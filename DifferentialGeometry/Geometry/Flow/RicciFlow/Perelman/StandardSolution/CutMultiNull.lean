import DifferentialGeometry.Geometry.Measure.ManifoldRademacher
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CostChartLipComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.BranchUpper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Conjugate.MeasureZero

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem lCost_nondiff_null_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau : ℝ) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K)
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      {y : M | ¬ MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
        (fun z : M ↦ lCost S T x z tau) y} = 0 := by
  apply DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_nondiff_null
    (I := I) g (fun z : M ↦ lCost S T x z tau)
  intro p
  exact lCost_chart_lip_of_rm (I := I) S hS K T hg x tau
    htau hreg hRm p

theorem lCutMulti_null_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau : ℝ) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K)
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      (lCutMulti S T x tau) = 0 := by
  classical
  refine measure_mono_null ?_
    (measure_union_null
      (lCost_nondiff_null_of_rm S hS K T hg x tau htau hreg hRm g)
      (lConjugateImage_null S hS T x tau g))
  rintro y ⟨Z, hZcut, W, hWne, hWmin, hend, rfl⟩
  have hZmin : (Z, tau) ∈ lMinDomain S T x :=
    ((mem_lCutDomain S T x tau Z).1 hZcut).1
  by_cases hZconj : IsLConjugate S T x Z tau
  · exact Or.inr ⟨Z, hZconj, rfl⟩
  by_cases hWconj : IsLConjugate S T x W tau
  · exact Or.inr ⟨W, hWconj, hend⟩
  · exact Or.inl <|
      lCost_nondiff_two_of_rm (I := I) S hS K T x
        hZmin hWmin hZconj hWconj hWne.symm hend.symm hRm

end DifferentialGeometry.PDE.RicciFlow

end
