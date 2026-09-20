import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSurfaceFixedCover
import DifferentialGeometry.Topology.Covering.SimplyConnectedCover

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance ancientSimplyConnectedSurfaceSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

private local instance ancientSimplyConnectedSurfaceSphereConnected :
    ConnectedSpace SphereTwo := by
  have hdim : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    norm_num [finrank_euclideanSpace_fin]
  exact Subtype.connectedSpace
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank hdim)
      (0 : EuclideanSpace ℝ (Fin 3)) zero_le_one)

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance ancientSimplyConnectedSurfaceTopology : TopologicalSpace F.M := F.topology
private local instance ancientSimplyConnectedSurfaceCharted : ChartedSpace H F.M := F.charted
private local instance ancientSimplyConnectedSurfaceSmooth : IsManifold I ∞ F.M := F.smooth
private local instance ancientSimplyConnectedSurfaceC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
private local instance ancientSimplyConnectedSurfaceT2 : T2Space F.M := F.t2
private local instance ancientSimplyConnectedSurfaceSigma : SigmaCompactSpace F.M := F.sigmaCompact

private local instance ancientSimplyConnectedSurfaceLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

theorem ancientKappaSurface_simplyConnected_fixed_round_diffeomorph
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 2) (hsimply : SimplyConnectedSpace F.M) :
    let _ : CompactSpace F.M := ancientKappaSurface_compact F hF hdim
    let T := surfaceArea (F.S.family.metric 0) /
      totalScalarCurvature (F.S.family.metric 0)
    0 < T ∧ ∃ e : SphereTwo ≃ₘ⟮𝓡 2, I⟯ F.M,
      ∀ (t : ℝ), t ≤ 0 → ∀ (x : SphereTwo) (v w : TangentSpace (𝓡 2) x),
        (F.S.family.metric t).inner (e x)
            (mfderiv (𝓡 2) I e x v) (mfderiv (𝓡 2) I e x w) =
          (2 * (T - t)) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
            x v w := by
  let _ : CompactSpace F.M := ancientKappaSurface_compact F hF hdim
  let _ : SimplyConnectedSpace F.M := hsimply
  obtain ⟨hT, pi, hlocal, hcover, _, hmetric, _, _⟩ :=
    ancientKappaSurface_fixed_round_cover F hF hdim
  have hbijective : Function.Bijective pi := hcover.bijective_of_simplyConnected
  let e : SphereTwo ≃ₘ⟮𝓡 2, I⟯ F.M := hlocal.diffeomorphOfBijective hbijective
  refine ⟨hT, e, ?_⟩
  intro t ht x v w
  exact hmetric t ht x v w

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
