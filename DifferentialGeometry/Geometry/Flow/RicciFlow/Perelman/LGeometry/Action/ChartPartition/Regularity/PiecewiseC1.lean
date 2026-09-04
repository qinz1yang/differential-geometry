import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.LocalMinimality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.VelocityRegularity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [CompactSpace M] in
theorem lRegAction_minimizer_chart_piece_contDiffOn_one
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (ht : StrictMono t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i, MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegAction S T gamma a b ≤ lRegAction S T delta a b) :
    ∀ i, ContDiffOn Real 1 (u i).toFun
      (Icc (0 : Real) (partitionIntervalLength t i)) := by
  classical
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  intro i
  have hpos : t i.castSucc < t i.succ :=
    ht Fin.castSucc_lt_succ
  have hL : 0 < partitionIntervalLength t i := by
    simpa only [partitionIntervalLength] using sub_pos.mpr hpos
  have hleft : a ≤ t i.castSucc := by
    rw [← ht0]
    exact ht.monotone (Fin.zero_le _)
  have hright : t i.succ ≤ b := by
    rw [← htlast]
    exact ht.monotone (Fin.le_last _)
  have hshift : MapsTo (fun r : Real ↦ t i.castSucc + r)
      (Icc (0 : Real) (partitionIntervalLength t i))
      (Icc (t i.castSucc) (t i.succ)) := by
    intro r hr
    change r ∈ Icc (0 : Real) (t i.succ - t i.castSucc) at hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hregi : ∀ r ∈ Icc (0 : Real) (partitionIntervalLength t i),
      T - (t i.castSucc + r) ^ 2 ∈ D.regular := by
    intro r hr
    exact hreg (t i.castSucc + r)
      ⟨hleft.trans (hshift hr).1, (hshift hr).2.trans hright⟩
  have hchart : MapsTo (u i).toFun (Icc (0 : Real) (partitionIntervalLength t i))
      (interior (extChartAt I (p i)).target) := by
    rw [(isOpen_extChartAt_target (I := I) (p i)).interior_eq]
    intro r hr
    rw [hrep i hr]
    exact (extChartAt I (p i)).map_source (by
      simpa only [extChartAt_source] using hsrc i (hshift hr))
  have hlocal : IsLocalMinOn
      (lChartAction S T (t i.castSucc) (p i))
      (sameTimeEnds (u i)) (u i) :=
    lChartAction_isLocalMinOn_of_lRegAction_minimizer S hS.smoothMetric hSc T a b t ht.monotone
      ht0 htlast p gamma hgamma u hsrc hrep hreg hmin i hpos
  exact (lChartAction_minimizer_contDiffOn_one S hS T (t i.castSucc) (p i) hL
    (u i) hregi hchart hlocal).choose_spec.2.2.1

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
