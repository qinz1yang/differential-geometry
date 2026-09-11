import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.Sobolev
import DifferentialGeometry.Topology.Manifold.CurveChart.Subdivision
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Curve.Partition

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

theorem exists_timeH1_chart_partition_of_intervalIntegrable_lRegularizedLagrangian
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) (hab : a ≤ b) (alpha : ℝ → M)
    (hAC : let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace;
      AbsolutelyContinuousOnInterval alpha a b)
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (p : Fin m → M)
      (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      t 0 = a ∧ Monotone t ∧ t (Fin.last m) = b ∧
      (∀ i, MapsTo alpha (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source) ∧
      (∀ i, EqOn (u i).toFun (fun r ↦ extChartAt I (p i) (alpha (t i.castSucc + r)))
        (Icc 0 (partitionIntervalLength t i))) ∧
      ∀ i, (u i).deriv =ᵐ[timeMeasure (partitionIntervalLength t i)]
        deriv (fun r ↦ extChartAt I (p i) (alpha (t i.castSucc + r))) := by
  let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace
  have hc : ContinuousOn alpha (Icc a b) :=
    (uniformContinuousOn_of_absolutelyContinuousOnInterval hAC).continuousOn.mono Icc_subset_uIcc
  obtain ⟨q, hq0, hqmono, ⟨m, hqm⟩, hpieces⟩ := Geometry.exists_chart_subdivision (H := H) hab hc
  let t : Fin (m + 1) → ℝ := fun i ↦ (q i).1
  have htmono : Monotone t := fun i j hij ↦ hqmono hij
  have ht0 : t 0 = a := congrArg Subtype.val hq0
  have htlast : t (Fin.last m) = b := congrArg Subtype.val (hqm m le_rfl)
  choose p hp using fun i : Fin m ↦ hpieces i
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ := htmono Fin.castSucc_lt_succ.le
  have hsub (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc a b := by
    intro s hs
    exact ⟨(q i.castSucc).property.1.trans hs.1, hs.2.trans (q i.succ).property.2⟩
  have hsrc (i : Fin m) : MapsTo alpha
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source := by
    simpa only [t, Fin.val_castSucc, Fin.val_succ] using hp i
  have hACi (i : Fin m) : AbsolutelyContinuousOnInterval alpha (t i.castSucc) (t i.succ) :=
    hAC.mono (by simpa only [uIcc_of_le (hseg i), uIcc_of_le hab] using hsub i)
  choose u hu using fun i : Fin m ↦
    exists_timeH1_extChartAt_of_intervalIntegrable_lRegularizedLagrangian
      S hMet hSc T (t i.castSucc) (t i.succ) (hseg i) alpha (p i) (hACi i) (hsrc i)
      (hLag.mono_set (by simpa only [uIcc_of_le (hseg i), uIcc_of_le hab] using hsub i))
      (fun s hs ↦ hreg s (hsub i hs))
  exact ⟨m, t, p, u, ht0, htmono, htlast, hsrc, fun i ↦ (hu i).1, fun i ↦ (hu i).2⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
