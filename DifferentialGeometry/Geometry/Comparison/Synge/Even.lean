import DifferentialGeometry.Geometry.Comparison.Synge.Weinstein
import DifferentialGeometry.Geometry.Metric.UniversalCoverCompact
import DifferentialGeometry.Geometry.Curvature.UniversalCover
import DifferentialGeometry.Topology.Manifold.UniversalCoverOrientation
import DifferentialGeometry.Topology.Covering.UniversalDeckGroup
import DifferentialGeometry.Topology.Covering.TrivialFundamentalGroup

noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Covering

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

theorem synge_simplyConnected_of_even_dim {n : ℕ} (hdim : Module.finrank ℝ E = n)
    (hn : 2 ≤ n) (heven : Even n) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hsec : HasPositiveSectionalCurvature g)
    (horient : ∃ o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n),
      DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace 𝓘(ℝ, E)) o) :
    SimplyConnectedSpace M := by
  let : Inhabited M := ⟨Classical.choice inferInstance⟩
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  let : SemilocallySimplyConnectedSpace M :=
    DifferentialGeometry.Geometry.Riemannian.Topology.manifold_semilocallySimplyConnectedSpace
      (I := 𝓘(ℝ, E))
  let : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let : CompactSpace (UniversalCover M) :=
    Riemannian.universalCover_compactSpace_of_positiveSectional g hsec (hdim ▸ hn)
  let h := UniversalCover.liftedMetric (I := 𝓘(ℝ, E)) g
  obtain ⟨o, ho⟩ := horient
  let o' := universalCoverOrientation o
  have ho' := universalCoverOrientation_compatible hdim o ho
  have hcurv : HasPositiveSectionalCurvature h := hsec.universalCoverMetric
  have htrivial (a : FundamentalGroup M (default : M)) : a = 1 := by
    obtain ⟨x, hx⟩ := synge_weinstein_fixed_point hdim hn h hcurv o' ho'
      (UniversalCover.deckDiffeo (I := 𝓘(ℝ, E)) a)
      (UniversalCover.deck_inner g a)
      (Or.inl ⟨heven, universalCoverDeck_preserves_orientation o a⟩)
    have hdeck : fundamentalGroupToDeck a = 1 :=
      deckGroup_eq_one_of_fixed_point UniversalCover.proj_isCoveringMap
        (fundamentalGroupToDeck a) x hx
    apply fundamentalGroupToDeck_injective
    simpa only [map_one] using hdeck
  let : Subsingleton (FundamentalGroup M (default : M)) :=
    ⟨fun a b => (htrivial a).trans (htrivial b).symm⟩
  exact DifferentialGeometry.Topology.simplyConnectedSpace_of_subsingleton_fundamentalGroup (default : M)

end DifferentialGeometry.Geometry
