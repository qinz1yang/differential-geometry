import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapComponentLabel
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Cap (L : ℝ) := {x : E3 // ‖x‖ ≤ L}

private theorem isConnected_union_iUnion_attached {X J : Type*} [TopologicalSpace X]
    (B : Set X) (C : J → Set X) (hB : IsConnected B) (hC : ∀ j, IsConnected (C j))
    (hBC : ∀ j, (B ∩ C j).Nonempty) : IsConnected (B ∪ ⋃ j, C j) := by
  let T : Option J → Set X := fun i => i.elim B (fun j => B ∪ C j)
  obtain ⟨x, hx⟩ := hB.nonempty
  have hT : ∀ i, IsPreconnected (T i) := by
    intro i
    cases i with
    | none => exact hB.isPreconnected
    | some j => exact (IsConnected.union (hBC j) hB (hC j)).isPreconnected
  have hTx : ∀ i, x ∈ T i := by
    intro i
    cases i with
    | none => exact hx
    | some j => exact Or.inl hx
  have he : (⋃ i, T i) = B ∪ ⋃ j, C j := by
    ext z
    constructor
    · rintro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      cases i with
      | none => exact Or.inl hi
      | some j => exact hi.elim Or.inl (fun hz => Or.inr (mem_iUnion.mpr ⟨j, hz⟩))
    · rintro (hz | hz)
      · exact mem_iUnion.mpr ⟨none, hz⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
        exact mem_iUnion.mpr ⟨some j, Or.inr hj⟩
  rw [← he]
  exact ⟨⟨x, mem_iUnion.mpr ⟨none, hx⟩⟩, isPreconnected_iUnion ⟨x, mem_iInter.mpr hTx⟩ hT⟩

variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "FiberQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

theorem isConnected_finiteCapComponentLabel_fiber (c : ConnectedComponents (cutCore f)) :
    IsConnected (finiteCapComponentLabel hL hδ f hf hdisj ⁻¹' {c}) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  let core := finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
  let cap := finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj
  let B : Set FiberQ := core '' connectedComponent p
  let J := {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b = ConnectedComponents.mk p}
  let C : J → Set FiberQ := fun b => range (fun x : Cap L => cap ⟨b.val, x⟩)
  have hB : IsConnected B := isConnected_connectedComponent.image core (continuous_adjunctionLower _ _).continuousOn
  have hcapSet : IsConnected {x : E3 | ‖x‖ ≤ L} := by
    simpa only [Metric.closedBall, dist_zero_right] using (Metric.isConnected_closedBall (x := (0 : E3)) hL.le)
  let : ConnectedSpace (Cap L) := isConnected_iff_connectedSpace.mp hcapSet
  have hC : ∀ j, IsConnected (C j) := by
    intro j
    exact isConnected_range ((continuous_adjunctionCell _ _).comp continuous_sigmaMk)
  have hBC : ∀ j, (B ∩ C j).Nonempty := by
    intro j
    let a := cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨j.val, spherePoint⟩
    refine ⟨core a, ?_, ?_⟩
    · exact ⟨a, ConnectedComponents.coe_eq_coe'.mp j.property, rfl⟩
    · exact ⟨radialCapBoundary hL spherePoint,
        finiteCapQuotient_coherence hL hδ f (fun i => (hf i).injective) hdisj ⟨j.val, spherePoint⟩⟩
  have he : finiteCapComponentLabel hL hδ f hf hdisj ⁻¹' {ConnectedComponents.mk p} = B ∪ ⋃ j, C j := by
    ext q
    constructor
    · intro hq
      have hcover := eq_univ_iff_forall.mp (finiteCapQuotient_cover hL hδ f (fun i => (hf i).injective) hdisj) q
      rcases hcover with ⟨⟨b, x⟩, rfl⟩ | ⟨x, rfl⟩
      · change cuttingSphereComponent hδ f hf hdisj b = ConnectedComponents.mk p at hq
        exact Or.inr (mem_iUnion.mpr ⟨⟨b, hq⟩, x, rfl⟩)
      · change ConnectedComponents.mk x = ConnectedComponents.mk p at hq
        exact Or.inl ⟨x, ConnectedComponents.coe_eq_coe'.mp hq, rfl⟩
    · rintro (hq | hq)
      · obtain ⟨x, hx, rfl⟩ := hq
        exact ConnectedComponents.coe_eq_coe'.mpr hx
      · obtain ⟨j, x, rfl⟩ := mem_iUnion.mp hq
        exact j.property
  rw [he]
  exact isConnected_union_iUnion_attached B C hB hC hBC

theorem connectedComponent_eq_finiteCapComponentLabel_fiber (q : FiberQ) :
    connectedComponent q = finiteCapComponentLabel hL hδ f hf hdisj ⁻¹'
      {finiteCapComponentLabel hL hδ f hf hdisj q} := by
  let : LocallyPathConnectedSpace (cutCore f) := cutCore_locallyPathConnectedSpace hδ f hf hdisj
  have hc : IsClopen (finiteCapComponentLabel hL hδ f hf hdisj ⁻¹' {finiteCapComponentLabel hL hδ f hf hdisj q}) :=
    ⟨(isClosed_discrete _).preimage (continuous_finiteCapComponentLabel hL hδ f hf hdisj),
      (isOpen_discrete _).preimage (continuous_finiteCapComponentLabel hL hδ f hf hdisj)⟩
  exact Subset.antisymm (hc.connectedComponent_subset rfl)
    ((isConnected_finiteCapComponentLabel_fiber hL hδ f hf hdisj _).subset_connectedComponent rfl)
end DifferentialGeometry.Topology.ThreeManifold.Surgery
