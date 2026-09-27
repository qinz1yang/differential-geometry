import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapComponentLabel

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "SelectedQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCapRetained (R : Set (ConnectedComponents (cutCore f))) : Opens SelectedQ :=
  ⟨finiteCapComponentLabel hL hδ f hf hdisj ⁻¹' R, by
    let : LocallyPathConnectedSpace (cutCore f) := cutCore_locallyPathConnectedSpace hδ f hf hdisj
    exact (isOpen_discrete R).preimage (continuous_finiteCapComponentLabel hL hδ f hf hdisj)⟩

def finiteCapDiscarded (R : Set (ConnectedComponents (cutCore f))) : Opens SelectedQ :=
  finiteCapRetained hL hδ f hf hdisj Rᶜ

theorem finiteCapRetained_discarded_partition (R : Set (ConnectedComponents (cutCore f))) :
    ((finiteCapRetained hL hδ f hf hdisj R : Set SelectedQ) ∪ finiteCapDiscarded hL hδ f hf hdisj R) = univ ∧
      Disjoint (finiteCapRetained hL hδ f hf hdisj R : Set SelectedQ) (finiteCapDiscarded hL hδ f hf hdisj R) := by
  change (finiteCapRetained hL hδ f hf hdisj R : Set SelectedQ) ∪
    (finiteCapRetained hL hδ f hf hdisj R : Set SelectedQ)ᶜ = univ ∧
    Disjoint (finiteCapRetained hL hδ f hf hdisj R : Set SelectedQ) (finiteCapRetained hL hδ f hf hdisj R : Set SelectedQ)ᶜ
  exact ⟨union_compl_self _, disjoint_compl_right⟩

theorem isClopen_finiteCapRetained_discarded (R : Set (ConnectedComponents (cutCore f))) :
    IsClopen (finiteCapRetained hL hδ f hf hdisj R : Set SelectedQ) ∧
      IsClopen (finiteCapDiscarded hL hδ f hf hdisj R : Set SelectedQ) := by
  let : LocallyPathConnectedSpace (cutCore f) := cutCore_locallyPathConnectedSpace hδ f hf hdisj
  have h : IsClopen (finiteCapRetained hL hδ f hf hdisj R : Set SelectedQ) :=
    ⟨(isClosed_discrete R).preimage (continuous_finiteCapComponentLabel hL hδ f hf hdisj),
      (finiteCapRetained hL hδ f hf hdisj R).isOpen⟩
  exact ⟨h, h.compl⟩

theorem finiteCapRetained_discarded_core_preimage (R : Set (ConnectedComponents (cutCore f))) :
    (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj ⁻¹'
      (finiteCapRetained hL hδ f hf hdisj R : Set SelectedQ)) = retainedCore f R ∧
    (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj ⁻¹'
      (finiteCapDiscarded hL hδ f hf hdisj R : Set SelectedQ)) = discardedCore f R := ⟨rfl, rfl⟩

theorem finiteCapRetained_cap_preimage (R : Set (ConnectedComponents (cutCore f))) :
    finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⁻¹'
      (finiteCapRetained hL hδ f hf hdisj R : Set SelectedQ) =
        {p : IndexedCaps ι L | cuttingSphereComponent hδ f hf hdisj p.1 ∈ R} := rfl

theorem finiteCapRetained_discarded_compactSpace [CompactSpace M]
    (R : Set (ConnectedComponents (cutCore f))) :
    CompactSpace (finiteCapRetained hL hδ f hf hdisj R) ∧
      CompactSpace (finiteCapDiscarded hL hδ f hf hdisj R) := by
  let : CompactSpace SelectedQ := finiteCapQuotient_compactSpace hL hδ f hf hdisj
  have h := isClopen_finiteCapRetained_discarded hL hδ f hf hdisj R
  exact ⟨isCompact_iff_compactSpace.mp h.1.isClosed.isCompact,
    isCompact_iff_compactSpace.mp h.2.isClosed.isCompact⟩

theorem finiteCapRetained_original_component_witness (R : Set (ConnectedComponents (cutCore f)))
    (c : ConnectedComponents (cutCore f)) (hc : c ∈ R) :
    ∃ p : cutCore f, ConnectedComponents.mk p = c ∧
      finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p ∈
        (finiteCapRetained hL hδ f hf hdisj R : Set SelectedQ) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  exact ⟨p, rfl, hc⟩

theorem finiteCapRetained_empty_discarded_univ :
    (finiteCapRetained hL hδ f hf hdisj ∅ : Set SelectedQ) = ∅ ∧
      (finiteCapDiscarded hL hδ f hf hdisj ∅ : Set SelectedQ) = univ := by
  simp [finiteCapRetained, finiteCapDiscarded]
end DifferentialGeometry.Topology.ThreeManifold.Surgery
