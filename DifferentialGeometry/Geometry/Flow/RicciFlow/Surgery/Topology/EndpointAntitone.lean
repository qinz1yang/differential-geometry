import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.VolumeGrowth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.VolumeContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

open Set Filter MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow

universe u

variable {P : OrientedThreeStage.{u}} {a b : ℝ}

theorem OrientedThreeStage.ClosedSlab.antitoneOn_exp_mul_volume
    (G : P.ClosedSlab a b) (K : ℝ)
    (hscalar : ∀ t ∈ Icc a b, ∀ x : P.Carrier,
      -K ≤ metricScalarAt (G.flow.base.metric t) x) :
    AntitoneOn
      (fun t : ℝ => Real.exp (-K * t) *
        (riemannianVolumeMeasure (𝓡 3) P.Carrier (G.flow.base.metric t) univ).toReal)
      (Icc a b) := by
  let F : ℝ → ℝ := fun t => Real.exp (-K * t) *
    (riemannianVolumeMeasure (𝓡 3) P.Carrier (G.flow.base.metric t) univ).toReal
  have hcontV := SolutionOn.continuousOn_volume G.flow G.equation
  have hcont : ContinuousOn F (Icc a b) := by
    exact ContinuousOn.mul (Real.continuous_exp.comp_continuousOn
      ((continuous_const.mul continuous_id).continuousOn)) hcontV
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hcont
  · intro t ht
    have hti : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have hreg : t ∈ (RealTimeInterval.closed a b G.lt.le).regular :=
      ⟨hti.1, hti.2⟩
    exact (G.flow.hasDerivAt_exp_mul_volume G.equation K hreg).hasDerivWithinAt
  · intro t ht
    have hti : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    apply integral_nonpos
    intro x
    have hbound := hscalar t (by exact ⟨hti.1.le, hti.2.le⟩) x
    have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (-K * t)).le
    change Real.exp (-K * t) * (-K) -
      metricScalarAt (G.flow.base.metric t) x * Real.exp (-K * t) ≤ 0
    nlinarith

theorem OrientedThreeStage.ClosedSlab.exp_mul_volume_le_endpoint
    (G : P.ClosedSlab a b) (K : ℝ)
    (hscalar : ∀ t ∈ Icc a b, ∀ x : P.Carrier,
      -K ≤ metricScalarAt (G.flow.base.metric t) x) :
    ∀ t ∈ Icc a b,
      Real.exp (-K * t) *
          (riemannianVolumeMeasure (𝓡 3) P.Carrier (G.flow.base.metric t) univ).toReal ≤
        Real.exp (-K * a) *
          (riemannianVolumeMeasure (𝓡 3) P.Carrier (G.flow.base.metric a) univ).toReal := by
  intro t ht
  exact G.antitoneOn_exp_mul_volume K hscalar ⟨le_rfl, G.lt.le⟩ ⟨ht.1, ht.2⟩ ht.1

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
