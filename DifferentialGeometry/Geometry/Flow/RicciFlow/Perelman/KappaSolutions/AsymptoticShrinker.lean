import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceNormalized
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTimeRestriction

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem exists_backward_slice_asymptotic_shrinker
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
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
  classical
  have hc : ancientTimeInterval.carrier = D.carrier := hF.carrier_eq.symm
  have hr : ancientTimeInterval.regular = D.regular := hF.regular_eq.symm
  let G := F.timeRestrict ancientTimeInterval hc.subset hr.subset
  have hG : IsAncientKappaSolution kappa G := hF.timeRestrict hc hr
  choose q hq using fun i => exists_redLength_le_half_finrank_of_ancient G hG G.basepoint (htau i)
  obtain ⟨L, phi, hphi, Phi, C, hcanonical, href, hcomplete, hconnected,
    hpos, _hcone, f, hsol, _hmass, _hpotential⟩ :=
    exists_backward_slice_normalized_shrinker_of_reducedLength_bound
      G hG G.basepoint tau htau hescape q hq
  exact ⟨q, L, phi, hphi, Phi, C, hcanonical, href, hcomplete, hconnected,
    ⟨L.basepoint, (hpos L.basepoint).ne'⟩, f, hsol.2.1⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
