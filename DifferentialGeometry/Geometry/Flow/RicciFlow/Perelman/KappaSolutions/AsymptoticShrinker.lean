import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Defs

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

theorem exists_backward_slice_asymptotic_shrinker
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) ∧
        (∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         ConnectedSpace L.M ∧
         (∃ x : L.M, metricScalarAt (I := I) L.metric x ≠ 0) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯, gradientRicciSoliton (I := I) L.metric f 1) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
