import DifferentialGeometry.Geometry.Neck.CompactSide
import DifferentialGeometry.Geometry.Neck.SpatialRestriction
import DifferentialGeometry.Topology.Manifold.ConnectedComponent
import DifferentialGeometry.Topology.SphereSeparation.OpenEmbeddingSides

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.SphereSeparation

private theorem compactSide_cast
    {X : Type*} [TopologicalSpace X] {S T : Set X} (h : S = T) (d : SphereSides S) :
    (h ▸ d).compactSide = d.compactSide := by
  cases h
  rfl

theorem exists_spatial_neck_open_image_side_exclusion_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (X M : Type*) [TopologicalSpace X] [ConnectedSpace X]
          [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p : M) (nk : SpatialNeck g eps p)
          (f : X → M), _root_.Topology.IsOpenEmbedding f →
          (∀ x ∈ range f, Nonempty (SpatialNeck g eps x)) →
          ¬ IsCompact (connectedComponent p) →
          ∀ S : Set X, f '' S = range (fun q : Sphere 2 => nk.map (q, 0)) →
            ¬ Nonempty (SphereSides S) := by
  obtain ⟨eta,heta,hexclude⟩ := exists_spatial_neck_compact_side_exclusion_tolerance
  refine ⟨eta,heta,?_⟩
  intro eps heps X M _ _ _ _ _ _ g p nk f hf hall hnoncompact S hS ⟨d⟩
  let U := DifferentialGeometry.connectedComponentOpen (I := I3) p
  let : LocallyConnectedSpace U := ChartedSpace.locallyConnectedSpace ThreeSpace U
  let : ConnectedSpace U := DifferentialGeometry.connectedComponentOpen_connectedSpace p
  let : NoncompactSpace U := ⟨by
    intro hc
    have h := hc.image continuous_subtype_val
    rw [image_univ, Subtype.range_coe_subtype] at h
    exact hnoncompact h⟩
  have hpc : p ∈ range f := by
    have hpS : p ∈ f '' S := hS.symm ▸ ⟨nk.center,nk.center_eq⟩
    exact image_subset_range _ _ hpS
  have hfc : range f ⊆ U := (isConnected_range hf.continuous).isPreconnected.subset_connectedComponent hpc
  let F : X → U := fun x => ⟨f x,hfc ⟨x,rfl⟩⟩
  have hF : _root_.Topology.IsOpenEmbedding F :=
    _root_.Topology.IsOpenEmbedding.of_comp F U.isOpen.isOpenEmbedding_subtypeVal hf
  obtain ⟨hp,out,_,hmap,_,_,_⟩ := nk.exists_restrict_target U
    nk.controlled_range_subset_connectedComponent
  obtain ⟨e,he⟩ := d.exists_image_openEmbedding hF
  have hzero (q : Sphere 2) : (q, (0:ℝ)) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ :=
    ⟨mem_univ _,neg_lt_zero.mpr (inv_pos.mpr nk.eps_pos),inv_pos.mpr nk.eps_pos⟩
  have hs : F '' S = range (fun q : Sphere 2 => out.map (q, 0)) := by
    apply (image_injective.mpr Subtype.val_injective)
    rw [image_image]
    change f '' S = (Subtype.val : U → M) '' range (fun q : Sphere 2 => out.map (q,0))
    rw [← range_comp]
    rw [hS]
    congr 1
    funext q
    exact (hmap _ (hzero q)).symm
  let e' : SphereSides (range (fun q : Sphere 2 => out.map (q,0))) := hs ▸ e
  have he' : e'.compactSide = F '' d.compactSide := (compactSide_cast hs e).trans he
  apply hexclude eps heps U (g.restrictOpen U) ⟨p,hp⟩ out e'
  intro x hx
  obtain ⟨y,_,hy⟩ := he' ▸ hx
  have hxrange : (x : M) ∈ range f := ⟨y, congrArg Subtype.val hy⟩
  obtain ⟨nx⟩ := hall x hxrange
  have hcapture : nx.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ U := by
    rw [show (U : Set M) = connectedComponent (x : M) from connectedComponent_eq x.property]
    exact nx.controlled_range_subset_connectedComponent
  obtain ⟨hxU,nxU,_⟩ := nx.exists_restrict_target U hcapture
  exact ⟨nxU⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
