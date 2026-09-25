import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic

noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

namespace FlowSequence

def terminalCurvatureRescale (X : FlowSequence.{u})
    (x : ∀ i, (X.term i).M)
    (hQ : ∀ i, 0 < (X.term i).S.scalar 0 (x i))
    (hzero : ∀ i, (0 : ℝ) ∈ (X.interval i).carrier) : FlowSequence.{u} where
  interval i := parabolicInterval (X.interval i) 0 ((X.term i).S.scalar 0 (x i)) (hzero i)
  term i := {
    M := (X.term i).M
    topology := (X.term i).topology
    charted := (X.term i).charted
    smooth := (X.term i).smooth
    sigmaCompact := (X.term i).sigmaCompact
    t2 := (X.term i).t2
    t2TangentBundle := (X.term i).t2TangentBundle
    basepoint := x i
    S := parabolicSolution (X.term i).S 0 ((X.term i).S.scalar 0 (x i)) (hQ i) (hzero i)
    isSolution := parabolicSolution_isSolutionOn (X.term i).S (X.term i).isSolution _ _ _ _ }

@[simp] theorem terminalCurvatureRescale_metric (X : FlowSequence.{u})
    (x : ∀ i, (X.term i).M) (hQ : ∀ i, 0 < (X.term i).S.scalar 0 (x i))
    (hzero : ∀ i, (0 : ℝ) ∈ (X.interval i).carrier) (i : ℕ) (t : ℝ) :
    ((X.terminalCurvatureRescale x hQ hzero).term i).S.base.metric t =
      scaleMetric ((X.term i).S.scalar 0 (x i)) (hQ i)
        ((X.term i).S.base.metric (t / (X.term i).S.scalar 0 (x i))) := by
  simp only [terminalCurvatureRescale, parabolicSolution, parabolicFamily, parabolicTime, zero_add]
  rfl

@[simp] theorem terminalCurvatureRescale_basepoint (X : FlowSequence.{u})
    (x : ∀ i, (X.term i).M) (hQ : ∀ i, 0 < (X.term i).S.scalar 0 (x i))
    (hzero : ∀ i, (0 : ℝ) ∈ (X.interval i).carrier) (i : ℕ) :
    ((X.terminalCurvatureRescale x hQ hzero).term i).basepoint = x i := rfl

end FlowSequence

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
