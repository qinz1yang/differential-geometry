import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimThreeBounded
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PreliminaryCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactPointedLimit


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

attribute [local instance] terminalTrichotomyInhabited
  terminalTrichotomyLocallyPathConnected
  terminalTrichotomySemilocallySimplyConnected

private local instance fixedKappaCompactnessC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} (I := I3) D) : IsManifold I3 1 F.M :=
  IsManifold.of_le (I := I3) (M := F.M) (n := ∞) (by decide)


theorem exists_fixed_kappa_compactness_of_rankOne
    (X : PointedFlowSeq.{u, 0, 0} (I := I3))
    (hD : X.D = ancientTimeInterval) {κ : ℝ}
    (hsource : ∀ i, KLim (I := I3) κ (X.term i))
    (hbase : ∀ i, PointedFlowScalarAtBase (I := I3) (X.term i) 1)
    (hnoEmbedding : ∀ f : SphereAntipodalQuotient → EuclideanSpace ℝ (Fin 3),
      ¬ _root_.Topology.IsEmbedding f) :
    ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I3) X (L.atTime (I := I3) 0) phi,
        KLim (I := I3) κ L ∧ PointedFlowScalarAtBase (I := I3) L 1 ∧
        (∀ t : ℝ, t ≤ 0 →
          ∃ C : MetricConvergenceData (I := I3) (Phi.atTime (L := L) t),
            ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I3) (Phi.atTime (L := L) t) k) ∧
        (∀ a b : ℝ, a ≤ b → b ≤ 0 → ∀ K : Set L.M, IsCompact K →
          ∀ order : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
            Nonempty (MetricComparisonOn
              (fun t => L.S.base.metric t) (fun t => (X.term (phi i)).S.base.metric t)
              (Phi.map i) K (Icc a b) order ε)) ∧
        ((∀ _P : TerminalSurfaceProduct (I := I3) (L.S.base.metric 0),
            BddAbove (Set.range (L.S.scalar 0))) →
          IsAncientKappaSolution (I := I3) κ L) := by
  obtain ⟨L, phi, hphi, Phi, hL, hbaseL, hcanonical, hmixed⟩ :=
    exists_preliminary_klim_compactness X hD hsource hbase
  refine ⟨L, phi, hphi, Phi, hL, hbaseL, hcanonical, hmixed, fun hrankOne => ?_⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  exact hL.isAncientKappaSolution_of_rankOne L hdim hnoEmbedding hrankOne


theorem klim_pointedLimit_noncompact {X : PointedFlowSeq.{u, 0, 0} (I := I3)}
    {L : PointedFlowData.{u, 0, 0} (I := I3) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I3) X (L.atTime (I := I3) 0) phi)
    (hconnected : ∀ i : ℕ, ConnectedSpace (X.term i).M)
    (hnoncompact : ∀ i : ℕ, NoncompactSpace (X.term i).M) :
    NoncompactSpace L.M :=
  pointedLimit_noncompact_of_connected_noncompact_sources
    (Phi.atTime (L := L) 0) (fun k => hconnected (phi k)) (fun k => hnoncompact (phi k))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
