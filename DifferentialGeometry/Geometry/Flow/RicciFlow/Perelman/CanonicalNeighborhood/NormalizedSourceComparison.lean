import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedRescaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedReindexing
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.ScalarRescaling

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_terminal_rescaled_source_comparison
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (L : PointedRiemannianManifold.{u, 0, 0} I3)
    (maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
    (conv : MetricConvergenceData maps)
    (hcanonical : ∀ i, conv.domain i = CanonicalMetricCompactness.canonicalSourceData maps i)
    (W : TopologicalSpace.Opens L.M) (x : ℕ → W)
    {R : ℝ} (hR : 0 < R)
    (hQ : ∀ n, 2 ≤ metricScalarAt L.metric (x n : L.M))
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf (L.metric.restrictOpen W) (x n)
      (4 * R / Real.sqrt (metricScalarAt L.metric (x n : L.M))))) :
    ∃ k : ℕ → ℕ, ∃ hk : StrictMono k,
      ∃ hq : ∀ n, 1 ≤ (X.term (f (k n))).S.scalar 0
        (maps.partialDiffeomorph (k n) (x n : L.M)),
      let q : ℕ → ℝ := fun n => (X.term (f (k n))).S.scalar 0
        (maps.partialDiffeomorph (k n) (x n : L.M))
      let G := fun n => scaleMetric (q n) (lt_of_lt_of_le zero_lt_one (hq n))
        (L.metric.restrictOpen W)
      let Y := (X.reindex (f ∘ k) (hf.comp hk)).terminalCurvatureRescale
        (fun n => maps.partialDiffeomorph (k n) (x n : L.M)) hq
      let H := fun n => (Y.term n).S.base.metric 0
      let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) W ⟨x 0⟩
      let F := fun n => inc.trans (maps.partialDiffeomorph (k n))
      Tendsto (fun n => q n / metricScalarAt L.metric (x n : L.M)) atTop (𝓝 1) ∧
      ∀ n, IsCompact (riemannianClosedBallOf (G n) (x n) R) ∧
        riemannianClosedBallOf (G n) (x n) R ⊆ (F n).source ∧
        (∀ y ∈ riemannianClosedBallOf (G n) (x n) R, ∀ v : TangentSpace I3 y,
          (1 - 1 / ((n : ℝ) + 2)) * (G n).inner y v v ≤
            (H n).inner (F n y) (mfderiv I3 I3 (F n) y v) (mfderiv I3 I3 (F n) y v) ∧
          (H n).inner (F n y) (mfderiv I3 I3 (F n) y v) (mfderiv I3 I3 (F n) y v) ≤
            (1 + 1 / ((n : ℝ) + 2)) * (G n).inner y v v) ∧
        riemannianClosedBallOf (H n) (F n (x n)) (R / 4) ⊆
          (F n) '' riemannianClosedBallOf (G n) (x n) R ∧
        (∀ y ∈ riemannianClosedBallOf (G n) (x n) (R / 8),
          ∀ z ∈ riemannianClosedBallOf (G n) (x n) (R / 8),
            Real.sqrt (1 - 1 / ((n : ℝ) + 2)) * metricDistance (G n) y z ≤
              metricDistance (H n) (F n y) (F n z) ∧
            metricDistance (H n) (F n y) (F n z) ≤
              Real.sqrt (1 + 1 / ((n : ℝ) + 2)) * metricDistance (G n) y z) := by
  obtain ⟨k, hk, hq, hcomp⟩ := exists_scalar_rescaled_source_comparison
    (X.toFlowSequence.atTime 0) f L maps conv hcanonical W x hR hQ hcompact
  refine ⟨k, hk, hq, ?_⟩
  dsimp only
  simpa only [NormalizedSequence.terminalCurvatureRescale, FlowSequence.terminalCurvatureRescale,
    NormalizedSequence.reindex, parabolicSolution_metric, parabolicTime_zero, Function.comp_apply,
    metricDistance, FlowSequence.atTime, PointedFlowData.atTime, SolutionOn.scalar,
    SolutionFamily.scalar, metricScalarAt, parabolicSolution, parabolicFamily, parabolicTime,
    zero_add, zero_div, SolutionOn.family_metric] using! hcomp

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
