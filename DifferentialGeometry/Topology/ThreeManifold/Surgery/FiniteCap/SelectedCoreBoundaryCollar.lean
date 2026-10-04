import DifferentialGeometry.Topology.ClopenSubtypeFrontier
import DifferentialGeometry.Topology.VanKampen.SigmaBoundaryCollars
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingSphereCollarSelection

/-!
# SelectedCoreBoundaryCollar
-/

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open DifferentialGeometry.Geometry.Neck

namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
  [LocallyPathConnectedSpace M] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))

abbrev SelectedCuttingSpheres (R : Set (ConnectedComponents (cutCore f))) :=
  Σ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (b, S2).2

def selectedCuttingSphereMap (R : Set (ConnectedComponents (cutCore f))) :
    SelectedCuttingSpheres hδ f hf hdisj R → M :=
  fun p => cuttingSphereMap hδ f ⟨p.1.val, p.2⟩

include hδ hf hdisj in
theorem isClosed_selectedCore_ambient (R : Set (ConnectedComponents (cutCore f))) :
    IsClosed ((Subtype.val : cutCore f → M) '' retainedCore f R) :=
  (isClosed_cutCore f hf).isClosedMap_subtype_val _
    (isClopen_retained_discardedCore hδ f hf hdisj R).1.isClosed

theorem frontier_selectedCore_subset_sphere_range
    (R : Set (ConnectedComponents (cutCore f))) :
    frontier ((Subtype.val : cutCore f → M) '' retainedCore f R) ⊆
      range (selectedCuttingSphereMap hδ f hf hdisj R) := by
  intro x hx
  have h := DifferentialGeometry.Topology.frontier_subtype_image_subset_of_isClopen
    (isClosed_cutCore f hf) (isClopen_retained_discardedCore hδ f hf hdisj R).1 hx
  have hfront : x ∈ range (cuttingSphereMap hδ f) := by
    rw [range_cuttingSphereMap, ← frontier_cutCore hδ f hf hdisj]
    exact h.1
  obtain ⟨⟨b, y⟩, he⟩ := hfront
  obtain ⟨p, hp, hpv⟩ := h.2
  have hp' : p = cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩ :=
    Subtype.ext (hpv.trans he.symm)
  have hb : cuttingSphereComponent hδ f hf hdisj b ∈ R :=
    (cuttingSphere_mem_retainedCore_iff hδ f hf hdisj R b y).mp (hp' ▸ hp)
  exact ⟨⟨⟨b, hb⟩, y⟩, he⟩

def selectedCoreBoundaryCollar (R : Set (ConnectedComponents (cutCore f))) :
    TwoSidedCollar (selectedCuttingSphereMap hδ f hf hdisj R) :=
  TwoSidedCollar.sigma
    (fun b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} =>
      cuttingSphereTwoSidedCollar hδ f hf b.val)
    (fun b c h => by
      have hbc : b.val ≠ c.val := fun he => h (Subtype.ext he)
      exact pairwise_disjoint_cuttingSphereTwoSidedCollars hδ f hf hdisj hbc)

omit [Finite ι] [T2Space M] [LocallyPathConnectedSpace M] in
theorem selectedCoreBoundaryCollar_apply (R : Set (ConnectedComponents (cutCore f)))
    (b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R})
    (y : S2) (t : ℝ) :
    (selectedCoreBoundaryCollar hδ f hf hdisj R).toFun (⟨b, y⟩, t) =
      (cuttingSphereTwoSidedCollar hδ f hf b.val).toFun (y, t) := rfl

theorem selectedCoreBoundaryCollar_mem_iff (R : Set (ConnectedComponents (cutCore f)))
    (p : SelectedCuttingSpheres hδ f hf hdisj R × ℝ) :
    (selectedCoreBoundaryCollar hδ f hf hdisj R).toFun p ∈
      (Subtype.val : cutCore f → M) '' retainedCore f R ↔ p.2 ≤ 0 := by
  rcases p with ⟨⟨b, y⟩, t⟩
  rw [selectedCoreBoundaryCollar_apply hδ f hf hdisj R b y t,
    cuttingSphereTwoSidedCollar_mem_selected_iff hδ f hf hdisj R b.val y t]
  exact and_iff_left b.property

end DifferentialGeometry.Topology.ThreeManifold.Surgery
