import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplitting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Contractible

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientSplittingFactorTopology : TopologicalSpace F.M := F.topology
local instance ancientSplittingFactorCharted : ChartedSpace H F.M := F.charted
local instance ancientSplittingFactorSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientSplittingFactorC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance ancientSplittingFactorT2 : T2Space F.M := F.t2
local instance ancientSplittingFactorSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance ancientSplittingFactorInhabited : Inhabited F.M := ⟨F.basepoint⟩

local instance ancientSplittingFactorLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

local instance ancientSplittingFactorSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

private theorem simplyConnectedSpace_of_simplyConnectedSpace_prod_real {X : Type*}
    [TopologicalSpace X] [SimplyConnectedSpace (X × ℝ)] : SimplyConnectedSpace X := by
  let eR : ContinuousMap.HomotopyEquiv ℝ Unit :=
    Classical.choice (ContractibleSpace.hequiv ℝ Unit)
  let e : ContinuousMap.HomotopyEquiv (X × ℝ) X :=
    ((ContinuousMap.HomotopyEquiv.refl X).prodCongr eR).trans
      (Homeomorph.prodUnique X Unit).toHomotopyEquiv
  exact e.simplyConnectedSpace_iff.mp ‹SimplyConnectedSpace (X × ℝ)›

theorem connectedSpace_and_simplyConnectedSpace_of_universalCover_product
    (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)
    (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
    (hconnected : ConnectedSpace F.M) :
    ConnectedSpace G.M ∧ SimplyConnectedSpace G.M := by
  let _ : TopologicalSpace G.M := G.topology
  let _ : ConnectedSpace F.M := hconnected
  have hsc : SimplyConnectedSpace (G.M × ℝ) :=
    Phi.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance
  let _ : SimplyConnectedSpace (G.M × ℝ) := hsc
  have hscG : SimplyConnectedSpace G.M := simplyConnectedSpace_of_simplyConnectedSpace_prod_real
  let _ : SimplyConnectedSpace G.M := hscG
  exact ⟨inferInstance, hscG⟩

theorem metricComplete_of_universalCover_product
    (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)
    (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
    (hconnected : ConnectedSpace F.M) (t : ℝ)
    (hprod : ∀ (y : G.M) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (w, c)) =
        (G.S.family.metric t).inner y v w + a * c)
    (hcomplete : MetricComplete (I := I) (F.atTime t)) :
    MetricComplete (I := 𝓡 2) (G.atTime t) := by
  let _ : TopologicalSpace G.M := G.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
  let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
  let _ : IsManifold (𝓡 2) 1 G.M :=
    IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
  let _ : T2Space G.M := G.t2
  let _ : SigmaCompactSpace G.M := G.sigmaCompact
  let _ : T2Space (TangentBundle (𝓡 2) G.M) := G.t2TangentBundle
  let _ : ConnectedSpace F.M := hconnected
  let _ : SigmaCompactSpace (UniversalCover F.M) :=
    Phi.toHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  have hliftBase : RiemannianMetricComplete (I := I) (F.S.family.metric t) := ⟨hcomplete⟩
  have hlift : RiemannianMetricComplete (I := I)
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) :=
    UniversalCover.liftedMetric_complete (I := I) (F.S.family.metric t) hliftBase
  have heq : Diffeomorph.pullbackMetricCross
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Phi =
      (G.S.family.metric t).prod (euclideanMetric (E := ℝ)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z u v
    obtain ⟨y, s⟩ := z
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.prod_inner]
    change (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) u)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) v) =
      (G.S.family.metric t).inner y u.1 v.1 + inner ℝ (u.2 : ℝ) (v.2 : ℝ)
    rw [RCLike.inner_apply, conj_trivial, mul_comm]
    exact hprod y s u.1 v.1 (u.2 : ℝ) (v.2 : ℝ)
  have hc : RiemannianMetricComplete
      ((G.S.family.metric t).prod (euclideanMetric (E := ℝ))) := by
    rw [← heq]
    exact DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_pullbackMetricCross
      (J := I) hlift Phi
  have hfac : RiemannianMetricComplete (I := 𝓡 2) (G.S.family.metric t) :=
    (RiemannianMetricComplete.prod_iff.mp hc).1
  dsimp only [MetricComplete, PointedFlowData.atTime]
  exact hfac.complete

theorem ancient_fixed_universal_cover_product_of_negative_time_metric_product
    (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)
    (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
    (hconnected : ConnectedSpace F.M)
    (hcompleteF : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hscalarG : ∀ t : ℝ, t < 0 → ∀ y : G.M, 0 < G.S.scalar t y)
    (hscalar0 : ∀ y : G.M, 0 < G.S.scalar 0 y)
    (hprod : ∀ t : ℝ, t < 0 → ∀ (y : G.M) (s : ℝ)
      (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (w, c)) =
        (G.S.family.metric t).inner y v w + a * c) :
    let _ : ConnectedSpace F.M := hconnected
    ∃ G' : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval,
      let _ : TopologicalSpace G'.M := G'.topology
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G'.M := G'.charted
      let _ : IsManifold (𝓡 2) ∞ G'.M := G'.smooth
      let _ : IsManifold (𝓡 2) 1 G'.M :=
        IsManifold.of_le (I := 𝓡 2) (M := G'.M) (n := ∞) (by decide)
      let _ : T2Space G'.M := G'.t2
      let _ : SigmaCompactSpace G'.M := G'.sigmaCompact
      ConnectedSpace G'.M ∧ SimplyConnectedSpace G'.M ∧
        (∀ t : ℝ, t ≤ 0 → MetricComplete (I := 𝓡 2) (G'.atTime t)) ∧
        (∀ t : ℝ, t ≤ 0 → ∀ y : G'.M, 0 < G'.S.scalar t y) ∧
        ∃ Phi' : (G'.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
          ∀ (t : ℝ), t ≤ 0 → ∀ (y : G'.M) (s : ℝ)
            (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
            (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi' (y, s))
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi' (y, s) (v, a))
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi' (y, s) (w, c)) =
              (G'.S.family.metric t).inner y v w + a * c := by
  have hpack :=
    connectedSpace_and_simplyConnectedSpace_of_universalCover_product F G Phi hconnected
  have hcompleteG : ∀ t : ℝ, t < 0 → MetricComplete (I := 𝓡 2) (G.atTime t) :=
    fun t ht => metricComplete_of_universalCover_product F G Phi hconnected t (hprod t ht)
      (hcompleteF t ht.le)
  exact ancient_fixed_universal_cover_product_of_negative_splitting
    F G Phi hconnected hcompleteF hpack.1 hpack.2 hcompleteG hscalarG hprod hscalar0

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
