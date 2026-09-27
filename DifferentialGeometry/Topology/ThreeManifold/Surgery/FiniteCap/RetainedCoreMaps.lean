import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapPatchSelection

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CoreMapE3 := EuclideanSpace ℝ (Fin 3)
private abbrev CoreMapS2 := Metric.sphere (0 : CoreMapE3) 1
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
variable {precision : ι → ℝ} {L B : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (R : Set (ConnectedComponents (cutCore f)))

def finiteRetainedCoreInclusion : retainedCore f R → finiteCapRetained hL hδ f hf hdisj R :=
  fun p => ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p.val, p.property⟩

def retainedCoreDomainMap (U : Opens M)
    (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U) : retainedCore f R → U :=
  fun p => ⟨p.val.val, hRet p.property⟩

def finiteRetainedCollarCoreMap (b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R})
    (hfit : B ≤ cuttingCollarWidth (precision b.val.1)) :
    CoreMapS2 × Ico (0 : ℝ) B → retainedCore f R := fun q =>
  ⟨cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b.val
    (q.1, ⟨q.2.val, q.2.property.1, q.2.property.2.trans_le hfit⟩),
    (finiteCapRestrictedNeighborhood_subset_retained hL hδ f hf hdisj R b.val b.property B)
      ((finiteCapRestrictedNeighborhood_collar_iff hL hδ f hf hdisj b.val B _).mpr q.2.property.2)⟩

theorem finiteRetainedCollarCoreMap_zero
    (b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R})
    (hfit : B ≤ cuttingCollarWidth (precision b.val.1)) (hB : 0 < B) (y : CoreMapS2) :
    (finiteRetainedCollarCoreMap hL hδ f hf hdisj R b hfit (y, ⟨0, le_rfl, hB⟩)).val =
      cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b.val, y⟩ :=
  cuttingCollarMap_zero hδ f (fun i => (hf i).injective) hdisj b.val y
end DifferentialGeometry.Topology.ThreeManifold.Surgery
