import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CutAlternativeComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CutMultiNull

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

theorem lCut_null_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau rho : ℝ) (htau : 0 < tau) (htr : tau < rho)
    (hreg : Icc (T - rho) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - rho) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K)
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      (lCutImage S T x tau) = 0 := by
  have hsub : Icc (T - tau) T ⊆ Icc (T - rho) T := by
    intro t ht
    exact ⟨(sub_le_sub_left htr.le T).trans ht.1, ht.2⟩
  have hregTau : Icc (T - tau) T ⊆ D.regular := fun t ht ↦
    hreg (hsub ht)
  have hRmTau : ∀ t ∈ Icc (T - tau) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K := fun t ht y ↦
    hRm t (hsub ht) y
  rw [lCut_split_of_rm S hS K T hg x tau rho htr hreg hRm]
  exact measure_union_null
    (DifferentialGeometry.PDE.RicciFlow.Perelman.lCutConj_null S hS T x tau g)
    (lCutMulti_null_of_rm S hS K T hg x tau htau hregTau hRmTau g)

end DifferentialGeometry.PDE.RicciFlow

end
