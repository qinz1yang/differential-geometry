import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreInteriorChart
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
variable {ι M : Type*} [TopologicalSpace M]
variable {precision : ι → ℝ}

def coreInteriorInclusion (f : ∀ i : ι, bufferedCylinder (precision i) → M) :
    coreInteriorDomain f → cutCore f := fun p => ⟨p.val, interior_subset p.property⟩

theorem isOpenEmbedding_coreInteriorInclusion
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) :
    _root_.Topology.IsOpenEmbedding (coreInteriorInclusion f) := by
  have hi : _root_.Topology.IsEmbedding (coreInteriorInclusion f) :=
    _root_.Topology.IsEmbedding.subtypeVal.codRestrict (cutCore f) (fun p => interior_subset p.property)
  refine ⟨hi, ?_⟩
  have hr : range (coreInteriorInclusion f) = (Subtype.val : cutCore f → M) ⁻¹' interior (cutCore f) := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact q.property
    · intro hp
      exact ⟨⟨p.val, hp⟩, Subtype.ext rfl⟩
  rw [hr]
  exact isOpen_interior.preimage continuous_subtype_val

variable [Finite ι] [T2Space M]

theorem cutCore_locallyPathConnectedSpace [LocallyPathConnectedSpace M]
    (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    LocallyPathConnectedSpace (cutCore f) := by
  let : LocallyPathConnectedSpace S2 := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) S2
  let : LocallyPathConnectedSpace (coreInteriorDomain f) := (coreInteriorDomain f).isOpen.locallyPathConnectedSpace
  let C (b : ι × Bool) := S2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))
  let (b : ι × Bool) : LocallyPathConnectedSpace (Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    (convex_Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))).locallyPathConnectedSpace
  let ψ : (Σ b : ι × Bool, C b) → cutCore f := fun q => cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj q.1 q.2
  have hψ : Continuous ψ := continuous_sigma (fun b => (isOpenEmbedding_cuttingCollarMap hδ f hf hdisj b).continuous)
  have hψo : IsOpenMap ψ := isOpenMap_sigma.mpr (fun b => (isOpenEmbedding_cuttingCollarMap hδ f hf hdisj b).isOpenMap)
  let F := Sum.elim (coreInteriorInclusion f) ψ
  have hF : Continuous F := (isOpenEmbedding_coreInteriorInclusion f).continuous.sumElim hψ
  have hFo : IsOpenMap F := (isOpenEmbedding_coreInteriorInclusion f).isOpenMap.sumElim hψo
  have hFs : Surjective F := by
    intro p
    by_cases hp : p.val ∈ interior (cutCore f)
    · exact ⟨Sum.inl ⟨p.val, hp⟩, Subtype.ext rfl⟩
    · have hfront : p ∈ range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
        rw [range_cuttingSphereAttachment hδ f hf hdisj]
        exact ⟨subset_closure p.property, hp⟩
      obtain ⟨⟨b, y⟩, he⟩ := hfront
      refine ⟨Sum.inr ⟨b, (y, ⟨0, ⟨le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩⟩)⟩, ?_⟩
      exact (cuttingCollarMap_zero hδ f (fun i => (hf i).injective) hdisj b y).trans he
  exact (hFo.isQuotientMap hF hFs).locallyPathConnectedSpace

theorem cutCore_finite_connectedComponents [CompactSpace M] [LocallyPathConnectedSpace M]
    (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    Finite (ConnectedComponents (cutCore f)) := by
  let : LocallyPathConnectedSpace (cutCore f) := cutCore_locallyPathConnectedSpace hδ f hf hdisj
  let : CompactSpace (cutCore f) := isCompact_iff_compactSpace.mp (isCompact_cutCore f hf)
  infer_instance
end DifferentialGeometry.Topology.ThreeManifold.Surgery
