import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreComponents
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev SelectionE3 := EuclideanSpace ℝ (Fin 3)
private abbrev SelectionS2 := Metric.sphere (0 : SelectionE3) 1
variable {ι M : Type*} [TopologicalSpace M] {precision : ι → ℝ}

def retainedCore (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (R : Set (ConnectedComponents (cutCore f))) : Set (cutCore f) := ConnectedComponents.mk ⁻¹' R

def discardedCore (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (R : Set (ConnectedComponents (cutCore f))) : Set (cutCore f) := ConnectedComponents.mk ⁻¹' Rᶜ

theorem retained_discarded_partition (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (R : Set (ConnectedComponents (cutCore f))) :
    retainedCore f R ∪ discardedCore f R = univ ∧ Disjoint (retainedCore f R) (discardedCore f R) := by
  change retainedCore f R ∪ (retainedCore f R)ᶜ = univ ∧ Disjoint (retainedCore f R) (retainedCore f R)ᶜ
  exact ⟨union_compl_self _, disjoint_compl_right⟩

theorem retainedCore_same_component (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (R : Set (ConnectedComponents (cutCore f))) {p q : cutCore f}
    (h : ConnectedComponents.mk p = ConnectedComponents.mk q) :
    p ∈ retainedCore f R ↔ q ∈ retainedCore f R := by
  change ConnectedComponents.mk p ∈ R ↔ ConnectedComponents.mk q ∈ R
  rw [h]

variable [Finite ι] [T2Space M] [LocallyPathConnectedSpace M]
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))

include hδ hf hdisj in
theorem isClopen_retained_discardedCore (R : Set (ConnectedComponents (cutCore f))) :
    IsClopen (retainedCore f R) ∧ IsClopen (discardedCore f R) := by
  let : LocallyPathConnectedSpace (cutCore f) := cutCore_locallyPathConnectedSpace hδ f hf hdisj
  have h : IsClopen (retainedCore f R) :=
    ⟨(isClosed_discrete R).preimage ConnectedComponents.continuous_coe,
      (isOpen_discrete R).preimage ConnectedComponents.continuous_coe⟩
  exact ⟨h, h.compl⟩

include hδ hf hdisj in
theorem isCompact_retained_discardedCore [CompactSpace M] (R : Set (ConnectedComponents (cutCore f))) :
    IsCompact (retainedCore f R) ∧ IsCompact (discardedCore f R) := by
  let : CompactSpace (cutCore f) := isCompact_iff_compactSpace.mp (isCompact_cutCore f hf)
  have h := isClopen_retained_discardedCore hδ f hf hdisj R
  exact ⟨h.1.isClosed.isCompact, h.2.isClosed.isCompact⟩

omit [LocallyPathConnectedSpace M] in
def cuttingSphereComponent (b : ι × Bool) : ConnectedComponents (cutCore f) :=
  ConnectedComponents.mk (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, spherePoint⟩)

theorem cuttingSphere_component_eq (b : ι × Bool) (y : SelectionS2) :
    ConnectedComponents.mk (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩) =
      cuttingSphereComponent hδ f hf hdisj b := by
  let : LocallyPathConnectedSpace (cutCore f) := cutCore_locallyPathConnectedSpace hδ f hf hdisj
  let : ConnectedSpace SelectionS2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) (0 : SelectionE3) (by norm_num : (0 : ℝ) ≤ 1))
  have hc : Continuous (fun z : SelectionS2 =>
      ConnectedComponents.mk (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, z⟩)) :=
    ConnectedComponents.continuous_coe.comp
      ((isClosedEmbedding_cuttingSphereAttachment hδ f hf hdisj).continuous.comp continuous_sigmaMk)
  exact PreconnectedSpace.constant (inferInstance : PreconnectedSpace SelectionS2) hc (x := y) (y := spherePoint)

theorem cuttingSphere_mem_retainedCore_iff (R : Set (ConnectedComponents (cutCore f)))
    (b : ι × Bool) (y : SelectionS2) :
    cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩ ∈ retainedCore f R ↔
      cuttingSphereComponent hδ f hf hdisj b ∈ R := by
  change ConnectedComponents.mk _ ∈ R ↔ _
  rw [cuttingSphere_component_eq hδ f hf hdisj b y]

theorem cuttingSpheres_same_component_retention (R : Set (ConnectedComponents (cutCore f)))
    (b c : ι × Bool) (hbc : cuttingSphereComponent hδ f hf hdisj b = cuttingSphereComponent hδ f hf hdisj c)
    (y z : SelectionS2) :
    cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩ ∈ retainedCore f R ↔
      cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨c, z⟩ ∈ retainedCore f R := by
  rw [cuttingSphere_mem_retainedCore_iff hδ f hf hdisj R b y,
    cuttingSphere_mem_retainedCore_iff hδ f hf hdisj R c z, hbc]
end DifferentialGeometry.Topology.ThreeManifold.Surgery
