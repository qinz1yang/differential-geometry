import DifferentialGeometry.Geometry.Neck.ScalarRetainedCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {ι : Type*} {δ : ι → ℝ} (f : ∀ i, bufferedCylinder (δ i) → M)
  {eps C1 C2 t B : ℝ} {x : cutCore f}

theorem CanonicalWitness.domain_subset_cutCore_component_of_scalar_gap
    (W : CanonicalWitness S eps C1 C2 x.val t)
    (hband : ∀ i, ∀ y ∈ closedSlab (f i), B ≤ S.scalar t y)
    (hgap : C2 * S.scalar t x.val < B) :
    W.domain.carrier ⊆ (Subtype.val : cutCore f → M) '' connectedComponent x := by
  have hdomain : W.domain.carrier ⊆ cutCore f := by
    intro y hy hremoved
    obtain ⟨i,q,hq,rfl⟩ := mem_iUnion.mp hremoved
    have hclosed : f i q ∈ closedSlab (f i) := ⟨q,⟨hq.1.le,hq.2.le⟩,rfl⟩
    exact (not_lt_of_ge (le_trans (hband i _ hclosed) (W.scalar_bounds _ hy).2)) hgap
  let A : Set (cutCore f) := Subtype.val ⁻¹' W.domain.carrier
  have hAimage : (Subtype.val : cutCore f → M) '' A = W.domain.carrier := by
    apply Subset.antisymm (image_preimage_subset _ _)
    intro y hy
    exact ⟨⟨y,hdomain hy⟩,hy,rfl⟩
  have hA : IsPreconnected A := _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    (hAimage.symm ▸ W.domain.connected.isPreconnected)
  have hx : x ∈ A := by
    change x.val ∈ W.domain.carrier
    exact interior_subset W.center_inside
  rw [← hAimage]
  exact image_mono (hA.subset_connectedComponent hx)

theorem CanonicalWitness.domain_subset_discarded_core_of_scalar_gap
    (R : Set (ConnectedComponents (cutCore f))) (hx : x ∈ discardedCore f R)
    (W : CanonicalWitness S eps C1 C2 x.val t)
    (hband : ∀ i, ∀ y ∈ closedSlab (f i), B ≤ S.scalar t y)
    (hgap : C2 * S.scalar t x.val < B) :
    W.domain.carrier ⊆ (Subtype.val : cutCore f → M) '' discardedCore f R := by
  apply (W.domain_subset_cutCore_component_of_scalar_gap f hband hgap).trans
  apply image_mono
  intro y hy
  change ConnectedComponents.mk y ∉ R
  have heq : ConnectedComponents.mk y = ConnectedComponents.mk x := ConnectedComponents.coe_eq_coe'.mpr hy
  rw [heq]
  exact hx

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
