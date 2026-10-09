import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSeparation
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapComponentLabel

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.Manifold.Attachment
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem radialCapBoundary_covers_sphere {L : ℝ} (hL : 0 < L)
    (x : {x : E3 // ‖x‖ ≤ L}) (hx : ‖x.val‖ = L) :
    x ∈ range (radialCapBoundary hL) := by
  let y : Metric.sphere (0 : E3) 1 := ⟨L⁻¹ • x.val, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hL), hx, inv_mul_cancel₀ hL.ne']⟩
  refine ⟨y, Subtype.ext ?_⟩
  change L • (L⁻¹ • x.val) = x.val
  rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]

variable {ι M : Type*} {precision : ι → ℝ} {L : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, Injective (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))


def finiteCapOpenInteriors : Set (FiniteCapQuotient hL hδ f hf hdisj) :=
  finiteCapInclusion hL hδ f hf hdisj '' {x : IndexedCaps ι L | ‖x.2.val‖ < L}



theorem finiteCoreInclusion_range_eq_compl_openCaps :
    range (finiteCoreInclusion hL hδ f hf hdisj) =
      (finiteCapOpenInteriors hL hδ f hf hdisj)ᶜ := by
  ext q
  constructor
  · intro hq
    rintro ⟨⟨b, x⟩, hx, he⟩
    exact finiteCapInclusion_not_mem_core_of_norm_lt hL hδ f hf hdisj b x hx
      (he.symm ▸ hq)
  · intro hq
    have hcover := eq_univ_iff_forall.mp (finiteCapQuotient_cover hL hδ f hf hdisj) q
    rcases hcover with ⟨⟨b, x⟩, rfl⟩ | hcore
    · have hnot : ¬ ‖x.val‖ < L := fun hx => hq ⟨⟨b, x⟩, hx, rfl⟩
      have hx : ‖x.val‖ = L := le_antisymm x.property (le_of_not_gt hnot)
      obtain ⟨y, rfl⟩ := radialCapBoundary_covers_sphere hL x hx
      exact ⟨cuttingSphereAttachment hδ f hf hdisj ⟨b, y⟩,
        (finiteCapQuotient_coherence hL hδ f hf hdisj ⟨b, y⟩).symm⟩
    · exact hcore



def finiteCoreHomeomorphCapComplement [Finite ι] [TopologicalSpace M] [T2Space M]
    (ho : ∀ i, _root_.Topology.IsOpenEmbedding (f i)) :
    cutCore f ≃ₜ ↥((finiteCapOpenInteriors hL hδ f (fun i => (ho i).injective) hdisj)ᶜ) := by
  let j := finiteCoreInclusion hL hδ f (fun i => (ho i).injective) hdisj
  let U := (finiteCapOpenInteriors hL hδ f (fun i => (ho i).injective) hdisj)ᶜ
  have hr : range j = U := finiteCoreInclusion_range_eq_compl_openCaps hL hδ f
    (fun i => (ho i).injective) hdisj
  have hm (p : cutCore f) : j p ∈ U := hr ▸ mem_range_self p
  let F : cutCore f → U := fun p => ⟨j p, hm p⟩
  have he : _root_.Topology.IsEmbedding F :=
    (isClosedEmbedding_finiteCoreInclusion hL hδ f ho hdisj).isEmbedding.codRestrict U hm
  have hs : Surjective F := by
    intro q
    have hq : q.val ∈ range j := by
      rw [hr]
      exact q.property
    obtain ⟨p, hp⟩ := hq
    exact ⟨p, Subtype.ext hp⟩
  exact (Equiv.ofBijective F ⟨he.injective, hs⟩).toHomeomorphOfIsInducing he.isInducing

theorem finiteCoreHomeomorphCapComplement_apply [Finite ι] [TopologicalSpace M] [T2Space M]
    (ho : ∀ i, _root_.Topology.IsOpenEmbedding (f i)) (p : cutCore f) :
    (finiteCoreHomeomorphCapComplement hL hδ f hdisj ho p).val =
      finiteCoreInclusion hL hδ f (fun i => (ho i).injective) hdisj p := rfl


def finiteCoreComponentHomeomorphCapComplement [Finite ι] [TopologicalSpace M] [T2Space M]
    [LocallyPathConnectedSpace M]
    (ho : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (c : ConnectedComponents (cutCore f)) :
    retainedCore f {c} ≃ₜ
      {q : ↥((finiteCapOpenInteriors hL hδ f (fun i => (ho i).injective) hdisj)ᶜ) //
        finiteCapComponentLabel hL hδ f ho hdisj q.val = c} :=
  (finiteCoreHomeomorphCapComplement hL hδ f hdisj ho).subtype (fun _ => Iff.rfl)

theorem finiteCoreComponentHomeomorphCapComplement_apply
    [Finite ι] [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
    (ho : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (c : ConnectedComponents (cutCore f)) (p : retainedCore f {c}) :
    (finiteCoreComponentHomeomorphCapComplement hL hδ f hdisj ho c p).val.val =
      finiteCoreInclusion hL hδ f (fun i => (ho i).injective) hdisj p.val := rfl

include hδ hdisj in
theorem retainedCore_singleton_pathConnectedSpace
    [Finite ι] [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
    (ho : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (c : ConnectedComponents (cutCore f)) : PathConnectedSpace (retainedCore f {c}) := by
  let : LocallyPathConnectedSpace (cutCore f) :=
    cutCore_locallyPathConnectedSpace hδ f ho hdisj
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  apply isPathConnected_iff_pathConnectedSpace.mp
  have he : retainedCore f {ConnectedComponents.mk p} = connectedComponent p := by
    ext x
    exact ConnectedComponents.coe_eq_coe'
  rw [he, ← pathComponent_eq_connectedComponent]
  exact isPathConnected_pathComponent

end DifferentialGeometry.Topology.ThreeManifold.Surgery
