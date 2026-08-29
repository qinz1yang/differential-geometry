import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionNodeSplice
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionLocalMin

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [T2Space M] in
omit [CompactSpace M] in
theorem lNodeAct_min
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T : Real) (t : Fin 3 → Real) (htmono : Monotone t)
    (p : Fin 2 → M) (gamma : Real → M)
    (u : (i : Fin 2) → timeH1 E (lSegLen t i))
    (hsrc : ∀ i, MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (lSegLen t i)))
    (hreg : ∀ s ∈ Icc (t 0) (t (Fin.last 2)), T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta (t 0) = gamma (t 0) →
      delta (t (Fin.last 2)) = gamma (t (Fin.last 2)) →
      lRegAction S T gamma (t 0) (t (Fin.last 2)) ≤
        lRegAction S T delta (t 0) (t (Fin.last 2)))
    (v : (i : Fin 2) → timeH1 E (lSegLen t i))
    (hvtar : ∀ i, MapsTo (v i).toFun
      (Icc (0 : Real) (lSegLen t i)) (extChartAt I (p i)).target)
    (hv0 : (extChartAt I (p 0)).symm ((v 0).toFun 0) = gamma (t 0))
    (hv2 : (extChartAt I (p 1)).symm
      ((v 1).toFun (lSegLen t 1)) = gamma (t (Fin.last 2)))
    (hvnode : (extChartAt I (p 0)).symm
        ((v 0).toFun (lSegLen t 0)) =
      (extChartAt I (p 1)).symm ((v 1).toFun 0)) :
    (∑ i : Fin 2, lChartAct S T (t i.castSucc) (p i) (u i)) ≤
      ∑ i : Fin 2, lChartAct S T (t i.castSucc) (p i) (v i) := by
  obtain ⟨gammaV, hgammaV, hsrcV, hrepV, hV0, hV2, alpha, _w,
      halpha, halpha0, halpha2, _hsrcA, _hrepA, _hw, _hunif, hact⟩ :=
    lNode_c1_dense (I := I) S hMet hSc T t htmono p v hvtar hvnode hreg
  have hneg : Tendsto
      (fun n ↦ -lRegAction S T (alpha n) (t 0) (t (Fin.last 2))) atTop
      (nhds (-lRegAction S T gammaV (t 0) (t (Fin.last 2)))) :=
    continuousAt_neg.tendsto.comp hact
  have hglobal : lRegAction S T gamma (t 0) (t (Fin.last 2)) ≤
      lRegAction S T gammaV (t 0) (t (Fin.last 2)) := by
    have hlim := le_of_tendsto' hneg fun n ↦ neg_le_neg
      (hmin (alpha n) (halpha n)
        ((halpha0 n).trans (hV0.trans hv0))
        ((halpha2 n).trans (hV2.trans hv2)))
    linarith
  rw [lRegAction_chart_sum S hMet hSc T (t 0) (t (Fin.last 2))
    t htmono rfl rfl p gamma u hsrc hrep hreg] at hglobal
  rw [lRegAction_chart_sum S hMet hSc T (t 0) (t (Fin.last 2))
    t htmono rfl rfl p gammaV v hsrcV hrepV hreg] at hglobal
  exact hglobal

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
