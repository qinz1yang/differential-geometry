import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimFixedKappaCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RankOneTerminalBounded


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

section General

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance threeDimBoundedTopology : TopologicalSpace F.M := F.topology
local instance threeDimBoundedCharted : ChartedSpace H F.M := F.charted
local instance threeDimBoundedSmooth : IsManifold I ∞ F.M := F.smooth
local instance threeDimBoundedT2 : T2Space F.M := F.t2
local instance threeDimBoundedSigma : SigmaCompactSpace F.M := F.sigmaCompact

attribute [local instance] terminalTrichotomyInhabited
  terminalTrichotomyLocallyPathConnected
  terminalTrichotomySemilocallySimplyConnected


theorem KLim.rankOne_branch {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (hdim : Module.finrank ℝ E = 3) :
    ∀ _P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0),
      BddAbove (Set.range (F.S.scalar 0)) :=
  fun P => hK.rankOne_terminal_scalar_bddAbove hdim P


theorem KLim.three_terminal_scalar_bddAbove {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoEmbedding : ∀ f : SphereAntipodalQuotient → EuclideanSpace ℝ (Fin 3),
      ¬ _root_.Topology.IsEmbedding f) :
    BddAbove (Set.range (F.S.scalar 0)) :=
  KLim.three_terminal_scalar_bddAbove_of_rankOne F hK hdim hnoEmbedding
    (hK.rankOne_branch F hdim)


theorem KLim.scalar_bounded {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoEmbedding : ∀ f : SphereAntipodalQuotient → EuclideanSpace ℝ (Fin 3),
      ¬ _root_.Topology.IsEmbedding f) :
    ∃ C : ℝ, PointedFlowScalarBounded (I := I) F C :=
  KLim.scalar_bounded_of_rankOne F hK hdim hnoEmbedding (hK.rankOne_branch F hdim)


theorem KLim.isAncientKappaSolution {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoEmbedding : ∀ f : SphereAntipodalQuotient → EuclideanSpace ℝ (Fin 3),
      ¬ _root_.Topology.IsEmbedding f) :
    IsAncientKappaSolution (I := I) kappa F :=
  KLim.isAncientKappaSolution_of_rankOne F hK hdim hnoEmbedding (hK.rankOne_branch F hdim)

end General

section FixedKappa

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  terminalTrichotomyInhabited terminalTrichotomyLocallyPathConnected
  terminalTrichotomySemilocallySimplyConnected


theorem exists_fixed_kappa_compactness
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
        IsAncientKappaSolution (I := I3) κ L := by
  obtain ⟨L, phi, hphi, Phi, hKL, hbaseL, hconv, hcmp, himp⟩ :=
    exists_fixed_kappa_compactness_of_rankOne X hD hsource hbase hnoEmbedding
  refine ⟨L, phi, hphi, Phi, hKL, hbaseL, hconv, hcmp, himp ?_⟩
  intro P
  exact hKL.rankOne_terminal_scalar_bddAbove finrank_euclideanSpace_fin P

end FixedKappa

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
