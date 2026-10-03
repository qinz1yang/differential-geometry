import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteRetainedInterior
import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev OldE3 := EuclideanSpace ℝ (Fin 3)
private abbrev OldIC := (𝓡 2).prod 𝓘(ℝ)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph OldIC I ∞ (f i))
local notation "OldQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteOldMetric (U : Opens M) (g : SmoothRiemannianMetric I U)
    (R : Set (ConnectedComponents (cutCore f)))
    (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace OldE3 OldQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ OldQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    SmoothRiemannianMetric (𝓡 3) (finiteRetainedInteriorOpens hL hδ f hf hdisj R) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace OldE3 OldQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ OldQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let : T2Space OldQ := finiteCapQuotient_t2Space hL hδ f hf hdisj
  exact pullbackMetricOfInjectiveLocalDiffeomorph g
    (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet)
    (isLocalDiffeomorph_finiteRetainedInteriorOriginalMap hL hδ f hf hdisj I hdim hs U R hRet)
    (injective_finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet)

theorem finiteOldMetric_inner (U : Opens M) (g : SmoothRiemannianMetric I U)
    (R : Set (ConnectedComponents (cutCore f)))
    (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace OldE3 OldQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ OldQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    ∀ (q : finiteRetainedInteriorOpens hL hδ f hf hdisj R) (v w : TangentSpace (𝓡 3) q),
      (finiteOldMetric I hdim hL hδ f hf hdisj hs U g R hRet).inner q v w =
        g.inner (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet q)
          (mfderiv (𝓡 3) I (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet) q v)
          (mfderiv (𝓡 3) I (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet) q w) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace OldE3 OldQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ OldQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let : T2Space OldQ := finiteCapQuotient_t2Space hL hδ f hf hdisj
  dsimp only
  intro q v w
  exact pullbackMetricOfInjectiveLocalDiffeomorph_inner g
    (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet)
    (isLocalDiffeomorph_finiteRetainedInteriorOriginalMap hL hδ f hf hdisj I hdim hs U R hRet)
    (injective_finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet) q v w

theorem finiteOldMetric_original_inner (U : Opens M) (g : SmoothRiemannianMetric I U)
    (R : Set (ConnectedComponents (cutCore f)))
    (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
    (p : coreInteriorDomain f)
    (hp : (⟨p.val, interior_subset p.property⟩ : cutCore f) ∈ retainedCore f R)
    (v w : TangentSpace I p) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace OldE3 OldQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ OldQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    (finiteOldMetric I hdim hL hδ f hf hdisj hs U g R hRet).inner
      (finiteRetainedInteriorImage hL hδ f hf hdisj R p hp)
      (mfderiv I (𝓡 3) (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj) p v)
      (mfderiv I (𝓡 3) (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj) p w) =
        g.inner ⟨p.val, hRet hp⟩ v w := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace OldE3 OldQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ OldQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  have hd := finiteRetainedInteriorOriginalMap_mfderiv_image_comp hL hδ f hf hdisj I hdim hs U R hRet p hp
  have hv := congrArg (fun A : TangentSpace I p →L[ℝ] TangentSpace I p => A v) hd
  have hw := congrArg (fun A : TangentSpace I p →L[ℝ] TangentSpace I p => A w) hd
  dsimp only
  have ht := finiteOldMetric_inner I hdim hL hδ f hf hdisj hs U g R hRet
    (finiteRetainedInteriorImage hL hδ f hf hdisj R p hp)
    (mfderiv I (𝓡 3) (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj) p v)
    (mfderiv I (𝓡 3) (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj) p w)
  refine ht.trans ?_
  dsimp only [TangentSpace] at hv hw ⊢
  rw [finiteRetainedInteriorOriginalMap_image]
  erw [hv, hw]
  rfl
end DifferentialGeometry.PDE.RicciFlow.StandardCap
