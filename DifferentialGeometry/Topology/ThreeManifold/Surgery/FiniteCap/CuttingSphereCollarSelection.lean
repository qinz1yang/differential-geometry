import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingSphereTwoSidedCollar
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSelection

/-!
# CuttingSphereCollarSelection
-/

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open DifferentialGeometry.Geometry.Neck

namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
  [LocallyPathConnectedSpace M] {precision : ι → ℝ}

theorem cuttingSphereTwoSidedCollar_component_eq (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    (b : ι × Bool) (y : S2) (t : ℝ) (ht : t ≤ 0) :
    ConnectedComponents.mk (⟨(cuttingSphereTwoSidedCollar hδ f hf b).toFun (y, t),
      (cuttingSphereTwoSidedCollar_mem_cutCore_iff hδ f hf hdisj b y t).mpr ht⟩ : cutCore f) =
      cuttingSphereComponent hδ f hf hdisj b := by
  let : LocallyPathConnectedSpace (cutCore f) :=
    cutCore_locallyPathConnectedSpace hδ f hf hdisj
  let : ConnectedSpace (Iic (0 : ℝ)) := isConnected_iff_connectedSpace.mp isConnected_Iic
  let c := cuttingSphereTwoSidedCollar hδ f hf b
  let g : Iic (0 : ℝ) → cutCore f := fun u =>
    ⟨c.toFun (y, u.val),
      (cuttingSphereTwoSidedCollar_mem_cutCore_iff hδ f hf hdisj b y u.val).mpr u.property⟩
  have hg : Continuous g :=
    (c.isOpenEmbedding_toFun.continuous.comp
      (continuous_const.prodMk continuous_subtype_val)).subtype_mk _
  have he : ConnectedComponents.mk (g ⟨t, ht⟩) =
      ConnectedComponents.mk (g ⟨0, (le_rfl : (0 : ℝ) ≤ 0)⟩) :=
    PreconnectedSpace.constant (inferInstance : PreconnectedSpace (Iic (0 : ℝ)))
      (ConnectedComponents.continuous_coe.comp hg)
  have hz : g ⟨0, (le_rfl : (0 : ℝ) ≤ 0)⟩ =
      cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩ :=
    Subtype.ext (c.zero_eq y)
  exact he.trans ((congrArg ConnectedComponents.mk hz).trans
    (cuttingSphere_component_eq hδ f hf hdisj b y))

theorem cuttingSphereTwoSidedCollar_mem_selected_iff (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    (R : Set (ConnectedComponents (cutCore f))) (b : ι × Bool) (y : S2) (t : ℝ) :
    (cuttingSphereTwoSidedCollar hδ f hf b).toFun (y, t) ∈
      (Subtype.val : cutCore f → M) '' retainedCore f R ↔
        t ≤ 0 ∧ cuttingSphereComponent hδ f hf hdisj b ∈ R := by
  constructor
  · rintro ⟨p, hp, he⟩
    have ht : t ≤ 0 :=
      (cuttingSphereTwoSidedCollar_mem_cutCore_iff hδ f hf hdisj b y t).mp (he ▸ p.property)
    refine ⟨ht, ?_⟩
    have hlabel := cuttingSphereTwoSidedCollar_component_eq hδ f hf hdisj b y t ht
    have hpoint : p = ⟨(cuttingSphereTwoSidedCollar hδ f hf b).toFun (y, t),
        (cuttingSphereTwoSidedCollar_mem_cutCore_iff hδ f hf hdisj b y t).mpr ht⟩ :=
      Subtype.ext he
    change ConnectedComponents.mk p ∈ R at hp
    rwa [hpoint, hlabel] at hp
  · rintro ⟨ht, hb⟩
    refine ⟨⟨_, (cuttingSphereTwoSidedCollar_mem_cutCore_iff hδ f hf hdisj b y t).mpr ht⟩,
      ?_, rfl⟩
    change ConnectedComponents.mk _ ∈ R
    rwa [cuttingSphereTwoSidedCollar_component_eq hδ f hf hdisj b y t ht]

end DifferentialGeometry.Topology.ThreeManifold.Surgery
