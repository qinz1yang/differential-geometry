import DifferentialGeometry.Geometry.Geodesic.Chart.TransitionMap
import DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Chart.GramChristoffel
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartTransitionJacobianEntry (α β : M) (x : E)
    (i a : Fin (Module.finrank ℝ E)) : ℝ :=
  (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
    (chartTransitionAt (I := I) α β x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) a)) i

omit [IsManifold I ∞ M] in
@[simp] lemma chartTransitionJacobianEntry_def (α β : M) (x : E)
    (i a : Fin (Module.finrank ℝ E)) :
    chartTransitionJacobianEntry (I := I) α β x i a =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
        (chartTransitionAt (I := I) α β x
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) a)) i := rfl

theorem chartTransitionJacobianEntry_mul_sum [I.Boundaryless]
    (α β : M) {y : E} (hy : y ∈ chartTransitionSource (I := I) α β)
    (c i : Fin (Module.finrank ℝ E)) :
    ∑ a : Fin (Module.finrank ℝ E),
        chartTransitionJacobianEntry (I := I) α β y a i *
        chartTransitionJacobianEntry (I := I) β α
          (chartTransitionMap (I := I) α β y) c a =
      (if c = i then (1 : ℝ) else 0) := by
  classical
  have hcomp := chartTransitionAt_comp_chartTransitionAt (I := I) α β hy
  have happly :
      (chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y))
          (chartTransitionAt (I := I) α β y ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) =
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i := by
    have := congrArg (fun L : E →L[ℝ] E => L ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) hcomp
    simpa using this
  have hexpand :
      chartTransitionAt (I := I) α β y ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) =
        ∑ a : Fin (Module.finrank ℝ E),
          chartTransitionJacobianEntry (I := I) α β y a i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) a := by
    conv_lhs => rw [← (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).sum_repr
      (chartTransitionAt (I := I) α β y ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))]
    rfl
  rw [hexpand, map_sum] at happly
  have hcoord : (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
      (∑ a, chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y)
          (chartTransitionJacobianEntry (I := I) α β y a i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) a)) c =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) c :=
    congrArg (fun w => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w c) happly
  have hlhs :
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
        (∑ a, chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y)
            (chartTransitionJacobianEntry (I := I) α β y a i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) a)) c =
      ∑ a, chartTransitionJacobianEntry (I := I) α β y a i *
        chartTransitionJacobianEntry (I := I) β α
          (chartTransitionMap (I := I) α β y) c a := by
    rw [map_sum]
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [map_smul, map_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul, chartTransitionJacobianEntry_def]
  rw [hlhs] at hcoord
  rw [hcoord]
  have hrepr : (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) c =
      (if c = i then (1 : ℝ) else 0) := by
    rw [(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr_self i, Finsupp.single_apply]
    by_cases h : c = i
    · subst h; simp
    · rw [if_neg (fun hh : i = c => h hh.symm), if_neg h]
  exact hrepr

theorem chartTransitionJacobianEntry_reverse_mul_sum [I.Boundaryless]
    (α β : M) {y : E} (hy : y ∈ chartTransitionSource (I := I) α β)
    (b i : Fin (Module.finrank ℝ E)) :
    ∑ m : Fin (Module.finrank ℝ E),
        chartTransitionJacobianEntry (I := I) α β y b m *
        chartTransitionJacobianEntry (I := I) β α
          (chartTransitionMap (I := I) α β y) m i =
      (if b = i then (1 : ℝ) else 0) := by
  classical
  have hcomp := chartTransitionAt_reverse_comp (I := I) α β hy
  have happly :
      (chartTransitionAt (I := I) α β y)
          (chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y)
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) =
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i := by
    have := congrArg (fun L : E →L[ℝ] E => L ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) hcomp
    simpa using this
  have hexpand :
      chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y)
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) =
        ∑ m : Fin (Module.finrank ℝ E),
          chartTransitionJacobianEntry (I := I) β α
            (chartTransitionMap (I := I) α β y) m i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m := by
    conv_lhs => rw [← (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).sum_repr
      (chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β y)
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))]
    rfl
  rw [hexpand, map_sum] at happly
  have hcoord : (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
      (∑ m, chartTransitionAt (I := I) α β y
          (chartTransitionJacobianEntry (I := I) β α
            (chartTransitionMap (I := I) α β y) m i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m)) b =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) b :=
    congrArg (fun w => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr w b) happly
  have hlhs :
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
        (∑ m, chartTransitionAt (I := I) α β y
            (chartTransitionJacobianEntry (I := I) β α
              (chartTransitionMap (I := I) α β y) m i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m)) b =
      ∑ m, chartTransitionJacobianEntry (I := I) α β y b m *
        chartTransitionJacobianEntry (I := I) β α
          (chartTransitionMap (I := I) α β y) m i := by
    rw [map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [map_smul, map_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul, chartTransitionJacobianEntry_def]
    ring
  rw [hlhs] at hcoord
  rw [hcoord]
  rw [(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr_self i, Finsupp.single_apply]
  by_cases h : b = i
  · subst h; simp
  · rw [if_neg (fun hh : i = b => h hh.symm), if_neg h]

lemma chartTransitionJacobianEntry_forward_reverse_collapse [I.Boundaryless]
    (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source)
    (a d : Fin (Module.finrank ℝ E)) :
    ∑ l : Fin (Module.finrank ℝ E),
        chartTransitionJacobianEntry (I := I) α β (extChartAt I α p) a l *
        chartTransitionJacobianEntry (I := I) β α
          (chartTransitionMap (I := I) α β (extChartAt I α p)) l d =
      (if a = d then (1 : ℝ) else 0) := by
  have hx_source : extChartAt I α p ∈ chartTransitionSource (I := I) α β :=
    extChartAt_mem_chartTransitionSource (I := I) α β hp_α hp_β
  exact chartTransitionJacobianEntry_reverse_mul_sum (I := I) α β hx_source a d

lemma chartTransitionJacobianEntry_reverse_forward_collapse [I.Boundaryless]
    (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source)
    (c i : Fin (Module.finrank ℝ E)) :
    ∑ a : Fin (Module.finrank ℝ E),
        chartTransitionJacobianEntry (I := I) α β (extChartAt I α p) a i *
        chartTransitionJacobianEntry (I := I) β α
          (chartTransitionMap (I := I) α β (extChartAt I α p)) c a =
      (if c = i then (1 : ℝ) else 0) := by
  have hx_source : extChartAt I α p ∈ chartTransitionSource (I := I) α β :=
    extChartAt_mem_chartTransitionSource (I := I) α β hp_α hp_β
  exact chartTransitionJacobianEntry_mul_sum (I := I) α β hx_source c i

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
