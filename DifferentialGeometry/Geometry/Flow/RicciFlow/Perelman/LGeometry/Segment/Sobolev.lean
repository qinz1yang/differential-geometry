import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.Sobolev
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter MeasureTheory Set
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Interval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M] {D : RealTimeInterval}

theorem isFiniteActionLCurve.exists_timeH1_chart_partition
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (Ω : Set (M × ℝ))
    (gamma : ℝ → M) (hgamma : isFiniteActionLCurve S T Ω (a ^ 2) (b ^ 2) gamma)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (p : Fin m → M)
      (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      t 0 = a ∧ Monotone t ∧ t (Fin.last m) = b ∧
      (∀ i, MapsTo (squareReparametrization gamma)
        (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source) ∧
      (∀ i, EqOn (u i).toFun
        (fun r ↦ extChartAt I (p i) (squareReparametrization gamma (t i.castSucc + r)))
        (Icc 0 (partitionIntervalLength t i))) ∧
      ∀ i, (u i).deriv =ᵐ[timeMeasure (partitionIntervalLength t i)]
        deriv (fun r ↦ extChartAt I (p i) (squareReparametrization gamma (t i.castSucc + r))) := by
  have hAC : let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace;
      AbsolutelyContinuousOnInterval (squareReparametrization gamma) a b := by
    let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace
    exact AbsolutelyContinuousOnInterval.comp_sq ha hab hgamma.1
  have hLag : IntervalIntegrable
      (lRegularizedLagrangian S T (squareReparametrization gamma)) volume a b :=
    (intervalIntegrable_lRegularizedLagrangian_squareReparametrization_iff
      S T gamma a b ha (ha.trans hab)).mpr hgamma.2.2.1
  exact exists_timeH1_chart_partition_of_intervalIntegrable_lRegularizedLagrangian S hMet hSc T a b hab
    (squareReparametrization gamma) hAC hLag hreg

end DifferentialGeometry.PDE.RicciFlow.Perelman
